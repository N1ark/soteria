(* The host primitives of the rules ([rules/*.kn]) that the value languages of
   the C tool and of soteria-rust share: the constants and folds on literals,
   the floating point primitives, and the SMT operators and sorts of the view
   functions. They are ported from the [Prims] and the [Enc] module of the first
   generation of the value language.

   [Make (V)] gives them over the types that Kanon generates for a language, of
   which it needs only a few sorts and nodes ({!module-type-Lang}). The language
   includes the result as the module of its primitives ([Bv_prims] for C,
   [Rust_prims] for Rust): the generated rules call all primitives there, and
   check them against their declarations, at their types: the integers of Kanon
   are [Z.t], and a bit-vector literal is a [Z.t] in [0, 2^n) of the width [n]
   of its sort, which the folds take as arguments, after the sorts of their
   operands. *)

(** What the primitives need of a language: its terms, a few of its sorts and
    nodes, and the traversal of the free variables of a term, which has to match
    every node of the language. *)
module type Lang = sig
  include Value_lang.Term

  val t_bool : ty
  val t_bv : int -> ty
  val t_ptr : int -> ty
  val k_bool : bool -> kind
  val k_bitvec : Z.t -> kind
  val k_ptr : t -> t -> kind
  val k_seq : t list -> kind

  (** The width of a bit-vector, location or pointer sort; fails on the others.
  *)
  val size_of : ty -> int

  (** The precision of a float sort; fails on the others. *)
  val fp_of_ty : ty -> Bv_base.FloatPrecision.t

  (** [iter_vars t f] calls [f] on the variables of [t] that are not bound in
      it, left to right. *)
  val used_binders_iter_vars : t -> (Symex.Var.t * ty -> unit) -> unit
end

module Make (V : Lang) = struct
  module L = Logs.Import.L
  module Var = Symex.Var
  module F = Floatml.AnyFloat
  module FloatPrecision = Bv_base.FloatPrecision
  module FloatClass = Bv_base.FloatClass
  module RoundingMode = Bv_base.RoundingMode

  type t = V.t
  type ty = V.ty
  type smt_op = (t, ty) View_host.smt_op
  type smt_sort_op = ty View_host.smt_sort_op

  let sort_by_tag (l : t list) =
    List.sort (fun l r -> Int.compare l.V.tag r.V.tag) l

  (* {1 Constants}

     The order of their creation is the order of their tags, which decides the
     order of the operands of commutative operators: it is that of the first
     generation of the value language, which the pp output of the tools depends
     on: [v_true], [v_false], the zero literals of 1 to 256 bits, then the one
     literals of 1 to 256 bits. *)

  let v_true = V.node (V.k_bool true) V.t_bool
  let v_false = V.node (V.k_bool false) V.t_bool

  let mk_bv_int n bv =
    assert (n > 0);
    assert (Z.(zero <= bv && bv < one lsl n));
    V.node (V.k_bitvec bv) (V.t_bv n)

  (* Bitwidth -> [(1 lsl n) - 1] mask. Memoized to avoid re-allocating the mask
     bignum on each [mk_masked] call (expensive in pathological cases). *)
  let mask_cache : Z.t Array.t = Array.init 256 (fun n -> Z.(pred (one lsl n)))
  let mask_of_bits n = if n <= 255 then mask_cache.(n) else Z.(pred (one lsl n))

  let mk_masked_int n bv =
    let mask = mask_of_bits n in
    V.node (V.k_bitvec (Z.logand bv mask)) (V.t_bv n)

  (* Index [n-1] holds the cached value for bitwidth [n]; we skip [n=0] because
     [mk_bv] asserts [n > 0]. *)
  let zero_cache : t Array.t =
    Array.init 256 (fun n -> mk_bv_int (n + 1) Z.zero)

  let[@inline] bv_zero_int n =
    if n <= 256 then zero_cache.(n - 1) else mk_bv_int n Z.zero

  let one_cache : t Array.t = Array.init 256 (fun n -> mk_bv_int (n + 1) Z.one)

  let[@inline] bv_one_int n =
    if n <= 256 then one_cache.(n - 1) else mk_bv_int n Z.one

  (* {1 Primitives of the rules} *)

  let used_binders_iter_vars = V.used_binders_iter_vars

  let used_binders binders body =
    let body_vars =
      Var.Hashset.of_iter (used_binders_iter_vars body |> Iter.map fst)
    in
    List.filter (fun (v, _) -> Var.Hashset.mem body_vars v) binders

  let[@inline] size_of ty = V.size_of ty
  let[@inline] size_of_ty ty = Z.of_int (size_of ty)
  let mk_bv n z = mk_bv_int (Z.to_int n) z
  let mk_masked n z = mk_masked_int (Z.to_int n) z
  let bv_zero n = bv_zero_int (Z.to_int n)
  let bv_one n = bv_one_int (Z.to_int n)
  let fp_of_ty = V.fp_of_ty

  (* {2 Folds on literals}

     The old folds took values with their width ([{ w; z }]); these take the
     sorts of their operands and the integers. *)

  let[@inline] masked w z = Z.extract z 0 w

  (* [z] read as a signed integer of [w] bits *)
  let[@inline] signed w z = Z.signed_extract z 0 w
  let lit_add s1 _ a b = masked (size_of s1) (Z.add a b)
  let lit_sub s1 _ a b = masked (size_of s1) (Z.sub a b)
  let lit_mul s1 _ a b = masked (size_of s1) (Z.mul a b)
  let lit_neg s1 a = masked (size_of s1) (Z.neg a)
  let lit_and s1 _ a b = masked (size_of s1) (Z.logand a b)
  let lit_or s1 _ a b = masked (size_of s1) (Z.logor a b)
  let lit_xor s1 _ a b = masked (size_of s1) (Z.logxor a b)
  let lit_not s1 a = masked (size_of s1) (Z.lognot a)

  (* the shift amount, if it is less than the width *)
  let shift_amount w b =
    let s = Z.extract b 0 w in
    if Z.lt s (Z.of_int w) then Some (Z.to_int s) else None

  let lit_shl s1 _ a b =
    let w = size_of s1 in
    match shift_amount w b with
    | Some s -> masked w (Z.shift_left a s)
    | None -> masked w Z.zero

  let lit_lshr s1 _ a b =
    let w = size_of s1 in
    match shift_amount w b with
    | Some s -> masked w (Z.shift_right a s)
    | None -> masked w Z.zero

  let lit_ashr s1 _ a b =
    let w = size_of s1 in
    let n = signed w a in
    match shift_amount w b with
    | Some s -> masked w (Z.shift_right n s)
    | None -> masked w (if Z.lt n Z.zero then Z.minus_one else Z.zero)

  let lit_smod s1 _ a b =
    let w = size_of s1 in
    let n = signed w a and d = signed w b in
    if Z.equal d Z.zero then a
    else
      let r = Z.rem n d in
      if Z.equal r Z.zero || Z.sign r = Z.sign d then masked w r
      else masked w (Z.add r d)

  let lit_extract from_ to_ _ a =
    let from_ = Z.to_int from_ in
    masked (Z.to_int to_ - from_ + 1) (Z.shift_right a from_)

  let lit_concat _ s2 a b = Z.logor (Z.shift_left a (size_of s2)) b

  let lit_udiv s1 _ a b =
    let w = size_of s1 in
    let d = Z.extract b 0 w in
    if Z.equal d Z.zero then masked w Z.minus_one else masked w (Z.div a d)

  let lit_sdiv s1 _ a b =
    let w = size_of s1 in
    let n = signed w a and d = signed w b in
    if Z.equal d Z.zero then
      masked w (if Z.lt n Z.zero then Z.one else Z.minus_one)
    else masked w (Z.div n d)

  let lit_urem s1 _ a b =
    let w = size_of s1 in
    let d = Z.extract b 0 w in
    if Z.equal d Z.zero then a else masked w (Z.rem a d)

  let lit_srem s1 _ a b =
    let w = size_of s1 in
    let n = signed w a and d = signed w b in
    if Z.equal d Z.zero then a else masked w (Z.rem n d)

  let lit_zext _ _ a = a
  let lit_sext k s1 a = masked (size_of s1 + Z.to_int k) (signed (size_of s1) a)
  let signed_extract z o l = Z.signed_extract z (Z.to_int o) (Z.to_int l)
  let popcount z = Z.of_int (Z.popcount z)
  let log2 z = Z.of_int (Z.log2 z)
  let tdiv = Z.div
  let trem = Z.rem
  let divisible = Z.divisible
  let z_land = Z.logand
  let z_lsl a b = Z.shift_left a (Z.to_int b)

  (* {2 Floats} *)

  let fp_size fp = Z.of_int (FloatPrecision.size fp)
  let fp_of_size n = FloatPrecision.of_size (Z.to_int n)
  let f_prec = F.precision
  let f_equal = F.equal
  let f_bits_equal = F.bits_equal
  let f_to_bits = F.to_z
  let f_of_bits = F.of_bits_z
  let f_nan = F.nan
  let f_is_class fc f = FloatClass.as_fpclass fc = F.fpclass f
  let f_is_nan = F.is_nan
  let f_is_zero = F.is_zero
  let f_is_negative = F.is_negative
  let f_is_positive = F.is_positive
  let f_eq = F.eq
  let f_lt = F.lt
  let f_le = F.le
  let f_add = F.add
  let f_sub = F.sub
  let f_mul = F.mul
  let f_div = F.div
  let f_rem = F.rem
  let f_fmod = F.fmod
  let f_min = F.min
  let f_max = F.max
  let f_fma = F.fma
  let f_abs = F.abs
  let f_neg = F.neg
  let f_sqrt = F.sqrt
  let f_round = F.round
  let f_convert = F.convert

  let f_to_int rounding signed size f =
    match Bv_base.int_size_of_size (Z.to_int size) with
    | Some int_size -> F.float2int f int_size rounding ~signed
    | None -> None

  let f_of_int rounding signed fp size z =
    match Bv_base.int_size_of_size (Z.to_int size) with
    | Some int_size -> Some (F.int2float z int_size fp rounding ~signed)
    | None -> None

  (* {1 Terms that Kanon does not build} *)

  (* No simplification, and the sizes of the operands must be equal *)
  let mk_ptr (l : t) (o : t) : t =
    let n = size_of o.V.ty in
    assert (size_of l.V.ty = n);
    V.node (V.k_ptr l o) (V.t_ptr n)

  let mk_seq (s : ty) (l : t list) : t = V.node (V.k_seq l) s
  let bad_operands (_ : t) : t = L.failwith "rebuild: wrong number of operands"

  (* {1 SMT encoding}

     The operators apply to the operands of the term. The order of the calls to
     [encode_child] is that of the old [encode_node]: it is the order in which
     the declarations are emitted. *)

  let rm_to_smt : RoundingMode.t -> Smt.RoundingMode.t = function
    | RoundingMode.NearestTiesToEven -> Smt.RoundingMode.NearestTiesToEven
    | NearestTiesToAway -> Smt.RoundingMode.NearestTiesToAway
    | Ceil -> Smt.RoundingMode.Ceil
    | Floor -> Smt.RoundingMode.Floor
    | Truncate -> Smt.RoundingMode.Truncate

  let wrong () = L.failwith "encode_head: wrong number of operands"

  (* one operand *)
  let un (f : Smt.sexp -> Smt.sexp) : smt_op =
   fun ~sort_of_ty:_ ~encode_child -> function
    | [ a ] -> f (encode_child a)
    | _ -> wrong ()

  (* two operands, left to right *)
  let bin (f : Smt.sexp -> Smt.sexp -> Smt.sexp) : smt_op =
   fun ~sort_of_ty:_ ~encode_child -> function
    | [ a; b ] ->
        let e1 = encode_child a in
        let e2 = encode_child b in
        f e1 e2
    | _ -> wrong ()

  (* three operands, right to left: the old code passed the encodings as
     arguments *)
  let tri (f : Smt.sexp -> Smt.sexp -> Smt.sexp -> Smt.sexp) : smt_op =
   fun ~sort_of_ty:_ ~encode_child -> function
    | [ a; b; c ] ->
        let e3 = encode_child c in
        let e2 = encode_child b in
        let e1 = encode_child a in
        f e1 e2 e3
    | _ -> wrong ()

  let encode_var v = Smt.atom (Var.to_string v)
  let h_var x : smt_op = fun ~sort_of_ty:_ ~encode_child:_ _ -> encode_var x

  let h_float ty f : smt_op =
   fun ~sort_of_ty:_ ~encode_child:_ _ ->
    let size = FloatPrecision.size (V.fp_of_ty ty) in
    Smt.float_of_bv size (Smt.bv_k size (F.to_z f))

  let h_bool b : smt_op = fun ~sort_of_ty:_ ~encode_child:_ _ -> Smt.bool_k b

  let h_bits ty z : smt_op =
   fun ~sort_of_ty:_ ~encode_child:_ _ -> Smt.bv_k (size_of ty) z

  (* the offset is encoded before the location *)
  let h_ptr ty : smt_op =
   fun ~sort_of_ty:_ ~encode_child -> function
    | [ l; o ] ->
        let eo = encode_child o in
        let el = encode_child l in
        Ptr_sort.mk_ptr (size_of ty) el eo
    | _ -> wrong ()

  let h_seq : smt_op =
   fun ~sort_of_ty:_ ~encode_child vs ->
    match vs with
    | [] -> L.failwith "need type to encode empty lists"
    | _ :: _ ->
        List.map (fun v -> Smt.seq_singl (encode_child v)) vs |> Smt.seq_concat

  (* the body is encoded before the sorts of the binders *)
  let h_exists vs : smt_op =
   fun ~sort_of_ty ~encode_child -> function
    | [ body ] ->
        let encode_binder (v, ty) = Smt.list [ encode_var v; sort_of_ty ty ] in
        let body = encode_child body in
        Smt.exists (List.map encode_binder vs) body
    | _ -> wrong ()

  let h_distinct : smt_op =
   fun ~sort_of_ty:_ ~encode_child vs -> Smt.distinct (List.map encode_child vs)

  let h_not = un Smt.bool_not
  let h_fabs = un Smt.fp_abs
  let h_fneg = un Smt.fp_neg
  let h_fsqrt = un Smt.fp_sqrt

  let h_ptr_loc : smt_op =
   fun ~sort_of_ty:_ ~encode_child -> function
    | [ a ] ->
        let e1 = encode_child a in
        Ptr_sort.get_loc (size_of a.V.ty) e1
    | _ -> wrong ()

  let h_ptr_ofs : smt_op =
   fun ~sort_of_ty:_ ~encode_child -> function
    | [ a ] ->
        let e1 = encode_child a in
        Ptr_sort.get_ofs (size_of a.V.ty) e1
    | _ -> wrong ()

  let h_bv_of_bool n =
    let n = Z.to_int n in
    un (fun b -> Smt.ite b (Smt.bv_k n Z.one) (Smt.bv_k n Z.zero))

  let h_bv_of_float rm signed n =
    let n = Z.to_int n in
    un
      (if signed then Smt.sbv_of_float (rm_to_smt rm) n
       else Smt.ubv_of_float (rm_to_smt rm) n)

  let h_float_of_bv rm signed fp =
    let size = FloatPrecision.size fp in
    un
      (if signed then Smt.float_of_sbv (rm_to_smt rm) size
       else Smt.float_of_ubv (rm_to_smt rm) size)

  let h_float_of_bv_raw fp = un (Smt.float_of_bv (FloatPrecision.size fp))

  let h_float_of_float rm fp =
    un (Smt.float_of_float (rm_to_smt rm) (FloatPrecision.size fp))

  let h_bv_extract from_ to_ =
    un (Smt.bv_extract (Z.to_int to_) (Z.to_int from_))

  let h_bv_extend signed by =
    let by = Z.to_int by in
    un (if signed then Smt.bv_sign_extend by else Smt.bv_zero_extend by)

  let h_bv_not = un Smt.bv_not
  let h_neg = un Smt.bv_neg
  let h_fis fc = un (Smt.fp_is (FloatClass.as_fpclass fc))
  let h_fisneg = un Smt.fp_is_negative
  let h_fispos = un Smt.fp_is_positive
  let h_fround rm = un (Smt.fp_round (rm_to_smt rm))
  let h_and = bin Smt.bool_and
  let h_or = bin Smt.bool_or
  let h_eq = bin Smt.eq
  let h_feq = bin Smt.fp_eq
  let h_fleq = bin Smt.fp_leq
  let h_flt = bin Smt.fp_lt
  let h_fadd = bin Smt.fp_add
  let h_fsub = bin Smt.fp_sub
  let h_fmul = bin Smt.fp_mul
  let h_fdiv = bin Smt.fp_div
  let h_frem = bin Smt.fp_rem
  let h_fmin = bin Smt.fp_min
  let h_fmax = bin Smt.fp_max
  let h_add = bin Smt.bv_add
  let h_sub = bin Smt.bv_sub
  let h_mul = bin Smt.bv_mul
  let h_div signed = bin (if signed then Smt.bv_sdiv else Smt.bv_udiv)
  let h_rem signed = bin (if signed then Smt.bv_srem else Smt.bv_urem)
  let h_mod = bin Smt.bv_smod
  let h_add_ovf signed = bin (if signed then Smt.bv_saddo else Smt.bv_uaddo)
  let h_sub_ovf signed = bin (if signed then Smt.bv_ssubo else Smt.bv_usubo)
  let h_mul_ovf signed = bin (if signed then Smt.bv_smulo else Smt.bv_umulo)
  let h_lt signed = bin (if signed then Smt.bv_slt else Smt.bv_ult)
  let h_leq signed = bin (if signed then Smt.bv_sleq else Smt.bv_uleq)
  let h_concat = bin Smt.bv_concat
  let h_bit_and = bin Smt.bv_and
  let h_bit_or = bin Smt.bv_or
  let h_bit_xor = bin Smt.bv_xor
  let h_shl = bin Smt.bv_shl
  let h_lshr = bin Smt.bv_lshr
  let h_ashr = bin Smt.bv_ashr
  let h_fma = tri Smt.fp_fma
  let h_ite = tri Smt.ite

  (* {2 Sorts} *)

  let so_bool : smt_sort_op = fun ~sort_of_ty:_ _ -> Smt.t_bool
  let so_bits n : smt_sort_op = fun ~sort_of_ty:_ _ -> Smt.t_bits (Z.to_int n)
  let so_ptr n : smt_sort_op = fun ~sort_of_ty:_ _ -> Ptr_sort.sort (Z.to_int n)

  let so_float p : smt_sort_op =
   fun ~sort_of_ty:_ _ ->
    match p with
    | FloatPrecision.F16 -> Smt.t_f16
    | F32 -> Smt.t_f32
    | F64 -> Smt.t_f64
    | F128 -> Smt.t_f128

  let so_seq : smt_sort_op =
   fun ~sort_of_ty -> function
    | [ c ] -> Smt.t_seq (sort_of_ty c)
    | _ -> L.failwith "encode_sort: a sequence has one component"
end
