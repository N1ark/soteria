open Logs.Import
open Hc
open Soteria_std
include Svalue_ast

(** Builds the untyped svalue layer for extension [V]: the value/type
    definitions specialised to [V], the hash-cons table, and the simplifying
    smart constructors ({{!Make.module-type-Bool}[Bool]},
    {{!Make.module-type-BitVec}[BitVec]}, {{!Make.module-type-Float}[Float]},
    {{!Make.Ptr}[Ptr]}, {{!Make.SSeq}[SSeq]}, ...). This is the foundation the
    rest of [Bv_values] is built on; most callers reach it as [Typed.Svalue]
    rather than applying it directly (see {!Typed.Make}).

    [Make] is {b generative} (note the final [()]): each application mints a
    fresh, abstract [ghost] tagging every value it hash-conses, and owns its own
    table. Two applications — even to the same [V] — therefore produce mutually
    incompatible [t]s, so values from one can never be mixed with another's.
    Apply it once and share the resulting module. *)
module Make (V : Value_ext) () = struct
  module Ext = V
  module Unop = Unop
  module Binop = Binop
  module Nop = Nop
  module Triop = Triop
  module RoundingMode = RoundingMode
  module FloatClass = FloatClass
  module FloatPrecision = FloatPrecision
  module Var = Var

  (** The fresh, abstract ghost identifying this application of {!Make}. *)
  type ghost

  let equal_ghost _ _ = true

  (* lift everything *)
  type nonrec ty = ghost V.ty ty
  type nonrec t = (ghost, ghost V.t, ghost V.ty) t
  type nonrec t_kind = (ghost, ghost V.t, ghost V.ty) t_kind
  type nonrec t_node = (ghost, ghost V.t, ghost V.ty) t_node

  let pp_ty = pp_ty V.pp_ty
  let equal_ty = equal_ty (V.equal_ty equal_ghost)

  let equal_t_node =
    equal_t_node equal_ghost (V.equal equal_ghost) (V.equal_ty equal_ghost)

  (* actual decls *)

  let t_bool = TBool
  let t_float fp = TFloat fp
  let t_f16 = t_float F16
  let t_f32 = t_float F32
  let t_f64 = t_float F64
  let t_f128 = t_float F128
  let t_loc n = TLoc n
  let t_ptr n = TPointer n
  let t_seq ty = TSeq ty
  let t_bv n = TBitVector n
  let is_float = [%matches? TFloat _]
  let is_bv = [%matches? TBitVector _]

  let precision_of_f = function
    | TFloat p -> p
    | ty -> L.failwith "Not a float: %a" pp_ty ty

  let hash t = t.tag
  let kind t = t.node.kind
  let unique_tag t = t.tag
  let is_bool_ty = [%matches? TBool]

  let[@inline] iter_vars (sv : t) (f : Var.t * ty -> unit) : unit =
    let rec aux ~ignore (sv : t) : unit =
      let aux' = aux ~ignore in
      match sv.node.kind with
      | Var v -> if Var.Set.mem v ignore then () else f (v, sv.node.ty)
      | Bool _ | Float _ | BitVec _ -> ()
      | Ptr (l, r) | Binop (_, l, r) ->
          aux' l;
          aux' r
      | Unop (_, sv) -> aux' sv
      | Triop (_, a, b, c) ->
          aux' a;
          aux' b;
          aux' c
      | Nop (_, l) | Seq l -> List.iter aux' l
      | Exists (vs, sv) ->
          let ignore =
            List.fold_left (fun ignore (v, _) -> Var.Set.add v ignore) ignore vs
          in
          aux ~ignore sv
      | Extension x -> V.iter_vars aux' x
    in
    aux ~ignore:Var.Set.empty sv

  let size_of = function
    | TBitVector n -> n
    | TPointer n -> n
    | TLoc n -> n
    | _ -> L.failwith "Not a bit value"

  let rec pp ft (t : t) =
    let open Fmt in
    match t.node.kind with
    | Var v -> pf ft "V%a" Var.pp v
    | Bool b -> pf ft "%b" b
    | Float f -> pf ft "%sf" (F.to_string f)
    | BitVec bv ->
        let size = size_of t.node.ty in
        if size mod 4 <> 0 then
          pf ft "0b%s" (Z.format ("0" ^ string_of_int size ^ "b") bv)
        else pf ft "0x%s" (Z.format ("0" ^ string_of_int (size / 4) ^ "x") bv)
    | Ptr (l, o) -> pf ft "&(%a, %a)" pp l pp o
    | Seq l -> pf ft "%a" (brackets (list ~sep:comma pp)) l
    | Exists (vs, v) ->
        let var_pp ft (v, ty) = pf ft "V%a:%a" Var.pp v pp_ty ty in
        pf ft "∃ %a. %a" (list ~sep:comma var_pp) vs pp v
    | Unop (Not, { node = { kind = Binop (Eq, v1, v2); _ }; _ }) ->
        pf ft "(%a != %a)" pp v1 pp v2
    | Unop (op, v) -> pf ft "%a(%a)" Unop.pp op pp v
    | Binop (op, v1, v2) -> pf ft "(%a %a %a)" pp v1 Binop.pp op pp v2
    | Triop (Ite, c, t, e) -> pf ft "(%a ? %a : %a)" pp c pp t pp e
    | Triop (op, a, b, c) -> pf ft "%a(%a, %a, %a)" Triop.pp op pp a pp b pp c
    | Nop (op, l) -> (
        let rec aux = function
          | acc, [] -> acc
          | Some l, { node = { kind = Var v; _ }; _ } :: rest ->
              aux (Some (Var.to_int v :: l), rest)
          | _, _ -> None
        in
        let range =
          aux (Some [], l)
          |> Option.bind (fun l ->
              let l = List.sort Int.compare l in
              let min = List.hd l in
              let max = List.hd @@ List.rev l in
              if max - min + 1 = List.length l then Some (min, max) else None)
        in
        match range with
        | Some (min, max) -> pf ft "%a(V|%d-%d|)" Nop.pp op min max
        | None -> pf ft "%a(%a)" Nop.pp op (list ~sep:comma pp) l)
    | Extension x -> V.pp pp ft x

  let[@inline] equal (a : t) (b : t) = Int.equal a.tag b.tag
  let[@inline] compare (a : t) (b : t) = Int.compare a.tag b.tag
  let pp_full ft t = pp_t_node Fmt.nop (Ext.pp pp) Ext.pp_ty ft t.node

  module Hcons = Hc.Make (struct
    type t = t_node

    let equal = equal_t_node
    let combine = hash_combine
    let hash_ty ty = hash_ty V.hash_ty ty

    let hash { kind; ty } =
      let h = hash_ty ty in
      match kind with
      | Bool b -> combine (combine h 1) (if b then 1 else 2)
      | Var v -> combine (combine h 2) (Var.to_int v)
      | Float f -> combine (combine h 3) (F.hash f)
      | BitVec z -> combine (combine h 4) (Z.hash z)
      | Ptr (l, r) -> combine (combine (combine h 5) l.tag) r.tag
      | Seq l ->
          List.fold_left (fun acc sv -> combine acc sv.tag) (combine h 6) l
      | Unop (op, v) -> combine (combine (combine h 7) (Unop.hash op)) v.tag
      | Binop (op, l, r) ->
          combine (combine (combine (combine h 8) (Binop.hash op)) l.tag) r.tag
      | Triop (op, a, b, c) ->
          combine
            (combine
               (combine (combine (combine h 13) (Triop.hash op)) a.tag)
               b.tag)
            c.tag
      | Nop (op, l) ->
          List.fold_left
            (fun acc sv -> combine acc sv.tag)
            (combine (combine h 9) (Nop.hash op))
            l
      | Exists (vs, sv) ->
          List.fold_left
            (fun acc (v, ty) ->
              combine (combine acc (Var.to_int v)) (hash_ty ty))
            (combine (combine h 11) sv.tag)
            vs
      | Extension e -> combine (combine h 12) (V.hash e)
  end)

  module Hashtbl = Hashtbl.Make (struct
    type nonrec t = t

    let equal = equal
    let hash = hash
  end)

  let ( <| ) kind ty : t = Hcons.hashcons { kind; ty }
  let mk_var v ty = Var v <| ty

  (** We put commutative binary operators in some sort of normal form where
      element with the smallest id is on the LHS, to increase cache hits. *)
  let mk_commut_binop op l r =
    if l.tag <= r.tag then Binop (op, l, r) else Binop (op, r, l)

  (** We put commutative n-ary operators in some sort of normal form where
      elements are sorted by ud, to increase cache hits. If [idem] is true, will
      also remove duplicates. *)
  let mk_commut_nop ~idem op vs =
    let sort = if idem then List.sort_uniq else List.sort in
    let vs = sort (fun l r -> Int.compare l.tag r.tag) vs in
    Nop (op, vs)

  type nonrec checked = checked = { signed : bool; unsigned : bool }

  let unchecked = unchecked
  let checked_both = checked_both
  let checked_of_signed = checked_of_signed

  (** {2 Operator declarations} *)

  module type Bool = sig
    val v_true : t
    val v_false : t
    val to_bool : t -> bool option
    val of_bool : bool -> t
    val and_ : t -> t -> t
    val and_lazy : t -> (unit -> t) -> t
    val or_ : t -> t -> t
    val or_lazy : t -> (unit -> t) -> t
    val conj : t list -> t
    val not : t -> t
    val split_ands : t -> t Iter.t
    val distinct : t list -> t
    val distinct_seq : t Seq.t -> t
    val ite : t -> t -> t -> t

    (** Do not use this directly when instantiating your own binders, use
        [exists_n] or its variants *)
    val mk_exists : (Var.t * ty) list -> t -> t

    val exists_n : not_in:t -> ty list -> (t list -> t) -> t
    val exists_1 : not_in:t -> ty -> (t -> t) -> t
    val exists_2 : not_in:t -> ty -> ty -> (t -> t -> t) -> t
    val exists_3 : not_in:t -> ty -> ty -> ty -> (t -> t -> t -> t) -> t
    val sem_eq : t -> t -> t
    val sem_eq_untyped : t -> t -> t
  end

  module type BitVec = sig
    (* constructor *)
    val mk : int -> Z.t -> t
    val mk_masked : int -> Z.t -> t
    val mki : int -> int -> t
    val zero : int -> t
    val one : int -> t
    val bv_to_z : bool -> int -> Z.t -> Z.t
    val to_z : t -> Z.t option
    val msb_of : t -> int

    (* arithmetic *)
    val add : ?checked:checked -> t -> t -> t
    val sub : ?checked:checked -> t -> t -> t
    val mul : ?checked:checked -> t -> t -> t
    val div : signed:bool -> t -> t -> t
    val rem : signed:bool -> t -> t -> t
    val mod_ : t -> t -> t
    val neg : ?checked:bool -> t -> t

    (* overflow checks *)
    val add_overflows : signed:bool -> t -> t -> t
    val sub_overflows : signed:bool -> t -> t -> t
    val mul_overflows : signed:bool -> t -> t -> t
    val neg_overflows : t -> t

    (* inequalities *)
    val lt : signed:bool -> t -> t -> t
    val leq : signed:bool -> t -> t -> t
    val gt : signed:bool -> t -> t -> t
    val geq : signed:bool -> t -> t -> t

    (* bitvec manipulation *)
    val concat : t -> t -> t
    val extend : signed:bool -> int -> t -> t
    val extract : int -> int -> t -> t

    (* bitwise operations *)
    val and_ : t -> t -> t
    val or_ : t -> t -> t
    val xor : t -> t -> t
    val shl : t -> t -> t
    val lshr : t -> t -> t
    val ashr : t -> t -> t
    val not : t -> t

    (* bool-bv conversions *)
    val of_bool : int -> t -> t
    val to_bool : t -> t
    val not_bool : t -> t

    (* float-bv conversions *)
    val of_float : rounding:RoundingMode.t -> signed:bool -> size:int -> t -> t

    val to_float :
      rounding:RoundingMode.t -> signed:bool -> fp:FloatPrecision.t -> t -> t

    val to_float_raw : t -> t
  end

  module type Float = sig
    (* constructors *)

    (** The raw node constructor; all others go through it. *)
    val mk_raw : FloatPrecision.t -> F.t -> t

    val mk : FloatPrecision.t -> string -> t
    val mk_bits : FloatPrecision.t -> Z.t -> t
    val of_z : FloatPrecision.t -> Z.t -> t
    val to_bits_opt : t -> t option
    val to_float_opt : t -> float option
    val sign_bit_opt : t -> bool option
    val approx : (float -> float) -> t -> t option
    val approx2 : (float -> float -> float) -> t -> t -> t option
    val zero : FloatPrecision.t -> t
    val neg_zero : FloatPrecision.t -> t
    val one : FloatPrecision.t -> t
    val nan : FloatPrecision.t -> t
    val infinity : FloatPrecision.t -> t
    val neg_infinity : FloatPrecision.t -> t
    val fp_of : t -> FloatPrecision.t

    (* conversion between precisions *)
    val cast : rounding:RoundingMode.t -> fp:FloatPrecision.t -> t -> t

    (* arithmetic *)
    val add : t -> t -> t
    val sub : t -> t -> t
    val mul : t -> t -> t
    val div : t -> t -> t
    val rem : t -> t -> t
    val fmod : t -> t -> t
    val fmod_of_rem : t -> t -> t -> t
    val fma : t -> t -> t -> t
    val min : t -> t -> t
    val max : t -> t -> t
    val minimum : t -> t -> t
    val maximum : t -> t -> t
    val abs : t -> t
    val neg : t -> t
    val sqrt : t -> t
    val round : RoundingMode.t -> t -> t

    (* comparisons *)
    val eq : t -> t -> t
    val lt : t -> t -> t
    val leq : t -> t -> t
    val gt : t -> t -> t
    val geq : t -> t -> t

    (* classification *)
    val is_floatclass : FloatClass.t -> t -> t
    val is_normal : t -> t
    val is_subnormal : t -> t
    val is_zero : t -> t
    val is_infinite : t -> t
    val is_nan : t -> t
    val is_negative : t -> t
    val is_positive : t -> t
  end

  (** {2 Constants} *)

  let v_true = Bool true <| TBool
  let v_false = Bool false <| TBool

  let mk_bv n bv =
    assert (n > 0);
    assert (Z.(zero <= bv && bv < one lsl n));
    BitVec bv <| t_bv n

  (* Bitwidth -> [(1 lsl n) - 1] mask. Memoized to avoid re-allocating the mask
     bignum on each [mk_masked] call (expensive in pathological cases). *)
  let mask_cache : Z.t Array.t = Array.init 256 (fun n -> Z.(pred (one lsl n)))
  let mask_of_bits n = if n <= 255 then mask_cache.(n) else Z.(pred (one lsl n))

  let mk_masked n bv =
    let mask = mask_of_bits n in
    BitVec (Z.logand bv mask) <| t_bv n

  (* Index [n-1] holds the cached value for bitwidth [n]; we skip [n=0] because
     [mk] asserts [n > 0]. *)
  let zero_cache : t Array.t = Array.init 256 (fun n -> mk_bv (n + 1) Z.zero)

  let[@inline] bv_zero n =
    if n <= 256 then zero_cache.(n - 1) else mk_bv n Z.zero

  let one_cache : t Array.t = Array.init 256 (fun n -> mk_bv (n + 1) Z.one)
  let[@inline] bv_one n = if n <= 256 then one_cache.(n - 1) else mk_bv n Z.one

  (** {2 Simplification rules}

      The simplifying smart constructors are generated from the rules in
      [rules/*.bvr]; see [soteria/bvr]. *)

  module Prims = struct
    type nonrec ghost = ghost
    type ext = ghost V.t
    type ext_ty = ghost V.ty
    type nonrec t = t

    let node = ( <| )
    let equal_ty = equal_ty
    let equal = equal
    let ty v = v.node.ty
    let kind v = v.node.kind
    let tag_le l r = l.tag <= r.tag
    let sort_by_tag l = List.sort (fun l r -> Int.compare l.tag r.tag) l

    let used_binders binders body =
      let body_vars = Var.Hashset.of_iter (iter_vars body |> Iter.map fst) in
      List.filter (fun (v, _) -> Var.Hashset.mem body_vars v) binders

    let size_of_ty ty = Z.of_int (size_of ty)

    let fp_of_ty = function
      | TFloat fp -> fp
      | _ -> L.failwith "Unsupported float type"

    let mk_bv n z = mk_bv (Z.to_int n) z
    let mk_masked n z = mk_masked (Z.to_int n) z
    let bv_zero n = bv_zero (Z.to_int n)
    let bv_one n = bv_one (Z.to_int n)
    let v_true = v_true
    let v_false = v_false

    type bv = { w : int; z : Z.t }

    let bv_of_lit v =
      match v.node.kind with
      | BitVec z -> { w = size_of v.node.ty; z }
      | _ -> L.failwith "bv_of_lit: not a literal"

    let lit l = mk_bv (Z.of_int l.w) l.z
    let width l = Z.of_int l.w
    let to_z signed l = if signed then Z.signed_extract l.z 0 l.w else l.z
    let masked w z = { w; z = Z.extract z 0 w }
    let of_z n z = masked (Z.to_int n) z
    let lit_add a b = masked a.w (Z.add a.z b.z)
    let lit_sub a b = masked a.w (Z.sub a.z b.z)
    let lit_mul a b = masked a.w (Z.mul a.z b.z)
    let lit_neg a = masked a.w (Z.neg a.z)

    let lit_udiv a b =
      let d = Z.extract b.z 0 a.w in
      if Z.equal d Z.zero then masked a.w Z.minus_one
      else masked a.w (Z.div a.z d)

    let lit_sdiv a b =
      let n = Z.signed_extract a.z 0 a.w and d = Z.signed_extract b.z 0 a.w in
      if Z.equal d Z.zero then
        masked a.w (if Z.lt n Z.zero then Z.one else Z.minus_one)
      else masked a.w (Z.div n d)

    let bv_equal a b = a.w = b.w && Z.equal a.z b.z
    let lit_and a b = masked a.w (Z.logand a.z b.z)
    let lit_or a b = masked a.w (Z.logor a.z b.z)
    let lit_xor a b = masked a.w (Z.logxor a.z b.z)
    let lit_not a = masked a.w (Z.lognot a.z)

    (* the shift amount, if it is less than the width *)
    let shift_amount a b =
      let s = Z.extract b.z 0 a.w in
      if Z.lt s (Z.of_int a.w) then Some (Z.to_int s) else None

    let lit_shl a b =
      match shift_amount a b with
      | Some s -> masked a.w (Z.shift_left a.z s)
      | None -> masked a.w Z.zero

    let lit_lshr a b =
      match shift_amount a b with
      | Some s -> masked a.w (Z.shift_right a.z s)
      | None -> masked a.w Z.zero

    let lit_ashr a b =
      let n = Z.signed_extract a.z 0 a.w in
      match shift_amount a b with
      | Some s -> masked a.w (Z.shift_right n s)
      | None -> masked a.w (if Z.lt n Z.zero then Z.minus_one else Z.zero)

    let lit_urem a b =
      let d = Z.extract b.z 0 a.w in
      if Z.equal d Z.zero then a else masked a.w (Z.rem a.z d)

    let lit_srem a b =
      let n = Z.signed_extract a.z 0 a.w and d = Z.signed_extract b.z 0 a.w in
      if Z.equal d Z.zero then a else masked a.w (Z.rem n d)

    let lit_smod a b =
      let n = Z.signed_extract a.z 0 a.w and d = Z.signed_extract b.z 0 a.w in
      if Z.equal d Z.zero then a
      else
        let r = Z.rem n d in
        if Z.equal r Z.zero || Z.sign r = Z.sign d then masked a.w r
        else masked a.w (Z.add r d)

    let lit_extract from_ to_ l =
      let from_ = Z.to_int from_ in
      masked (Z.to_int to_ - from_ + 1) (Z.shift_right l.z from_)

    let lit_zext k l = { w = l.w + Z.to_int k; z = l.z }
    let lit_sext k l = masked (l.w + Z.to_int k) (Z.signed_extract l.z 0 l.w)

    let lit_concat l r =
      { w = l.w + r.w; z = Z.logor (Z.shift_left l.z r.w) r.z }

    let signed_extract z o l = Z.signed_extract z (Z.to_int o) (Z.to_int l)
    let popcount z = Z.of_int (Z.popcount z)
    let log2 z = Z.of_int (Z.log2 z)
    let tdiv = Z.div
    let trem = Z.rem
    let divisible = Z.divisible
    let fp_size fp = Z.of_int (FloatPrecision.size fp)
    let fp_of_size n = FloatPrecision.of_size (Z.to_int n)
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
      match int_size_of_size (Z.to_int size) with
      | Some int_size -> F.float2int f int_size rounding ~signed
      | None -> None

    let f_of_int rounding signed fp size z =
      match int_size_of_size (Z.to_int size) with
      | Some int_size -> Some (F.int2float z int_size fp rounding ~signed)
      | None -> None
  end

  module R = Svalue_rules.Make (Prims)

  let sure_neq = R.sure_neq

  (** {2 Booleans} *)

  module Bool : Bool = struct
    let v_true = v_true
    let v_false = v_false

    let[@inline] to_bool t =
      if equal t v_true then Some true
      else if equal t v_false then Some false
      else None

    let of_bool b =
      (* avoid re-alloc and re-hashconsing *)
      if b then v_true else v_false

    let and_ = R.b_and
    let or_ = R.b_or
    let not = R.b_not
    let ite = R.b_ite
    let sem_eq = R.sem_eq
    let mk_exists = R.b_mk_exists

    (** * [exists_n ~not_in tys mk] creates an existential with [length tys]
        variables of types [tys], that are not in [not_in], and with body
        created by [mk : t list -> t] which takes the created variables as input
        in the same order as [tys]. *)
    let exists_n ~not_in tys mk =
      (* FIXME: Ideally, the not_in parameter would not be necessary. What we
         should be doing is creating variables with identifiers Int.max, Int.max
         - 1, etc., then create the value, and then substitute those variables
         with ones that are not in the rest of the value. Unfortunately, this
         requires calling `Eval.eval`, but that creates a cycle... *)
      let max = ref 0 in
      iter_vars not_in (fun (v, _) -> max := Int.max !max (Var.to_int v));
      (* We create something high to note those are actually existentials and
         reduce chances of conflict *)
      let base = !max + 10_000 in
      let binders = List.mapi (fun i ty -> (Var.of_int (base + i), ty)) tys in
      let binders_vs = List.map (fun (v, ty) -> mk_var v ty) binders in
      let body = mk binders_vs in
      mk_exists binders body

    let exists_1 ~not_in ty mk =
      exists_n ~not_in [ ty ] (function
        | [ v ] -> mk v
        | _ -> L.failwith "exists_1: unreachable")

    let exists_2 ~not_in ty1 ty2 mk =
      exists_n ~not_in [ ty1; ty2 ] (function
        | [ v1; v2 ] -> mk v1 v2
        | _ -> L.failwith "exists_2: unreachable")

    let exists_3 ~not_in ty1 ty2 ty3 mk =
      exists_n ~not_in [ ty1; ty2; ty3 ] (function
        | [ v1; v2; v3 ] -> mk v1 v2 v3
        | _ -> L.failwith "exists_3: unreachable")

    let sem_eq_untyped = R.sem_eq_untyped

    let and_lazy v1 v2 =
      match v1.node.kind with Bool false -> v_false | _ -> and_ v1 (v2 ())

    let or_lazy v1 v2 =
      match v1.node.kind with Bool true -> v_true | _ -> or_ v1 (v2 ())

    let conj l = List.fold_left and_ v_true l

    let rec split_ands (sv : t) (f : t -> unit) : unit =
      match sv.node.kind with
      | Binop (And, s1, s2) ->
          split_ands s1 f;
          split_ands s2 f
      | _ -> f sv

    let distinct_seq s = R.b_distinct (List.of_seq s)
    let distinct l = R.b_distinct l
  end

  (** {2 Bit vectors} *)
  module BitVec : BitVec = struct
    let mk = mk_bv
    let mk_masked = mk_masked
    let mki n i = mk n (Z.of_int i)
    let zero = bv_zero
    let one = bv_one

    (** [bv_to_z signed bits z] parses a BitVector [z], for a given bitwidth
        [bits], with [signed], into an integer. *)
    let bv_to_z signed bits z = if signed then Z.signed_extract z 0 bits else z

    let to_z v = match v.node.kind with BitVec z -> Some z | _ -> None
    let msb_of v = Z.to_int (R.msb_of v)
    let add ?(checked = unchecked) v1 v2 = R.bv_add checked v1 v2
    let sub ?(checked = unchecked) v1 v2 = R.bv_sub checked v1 v2
    let mul ?(checked = unchecked) v1 v2 = R.bv_mul checked v1 v2
    let div ~signed v1 v2 = R.bv_div signed v1 v2
    let rem ~signed v1 v2 = R.bv_rem signed v1 v2
    let mod_ = R.bv_mod
    let neg ?(checked = false) v = R.bv_neg checked v
    let add_overflows ~signed v1 v2 = R.bv_add_overflows signed v1 v2
    let sub_overflows ~signed v1 v2 = R.bv_sub_overflows signed v1 v2
    let mul_overflows ~signed v1 v2 = R.bv_mul_overflows signed v1 v2
    let neg_overflows = R.bv_neg_overflows
    let lt ~signed v1 v2 = R.bv_lt signed v1 v2
    let leq ~signed v1 v2 = R.bv_leq signed v1 v2
    let gt ~signed v1 v2 = lt ~signed v2 v1
    let geq ~signed v1 v2 = leq ~signed v2 v1
    let concat = R.bv_concat
    let extend ~signed extend_by v = R.bv_extend signed (Z.of_int extend_by) v
    let extract from_ to_ v = R.bv_extract (Z.of_int from_) (Z.of_int to_) v
    let and_ = R.bv_and
    let or_ = R.bv_or
    let xor = R.bv_xor
    let shl = R.bv_shl
    let lshr = R.bv_lshr
    let ashr = R.bv_ashr
    let not = R.bv_not
    let of_bool n b = R.bv_of_bool (Z.of_int n) b
    let to_bool = R.bv_to_bool
    let not_bool = R.bv_not_bool

    let of_float ~rounding ~signed ~size v =
      R.bv_of_float rounding signed (Z.of_int size) v

    let to_float ~rounding ~signed ~fp v = R.bv_to_float rounding signed fp v
    let to_float_raw = R.bv_to_float_raw
  end

  (** {2 Floating point} *)
  module Float : Float = struct
    let fp_of v =
      match v.node.ty with
      | TFloat fp -> fp
      | _ -> L.failwith "Unsupported float type"

    let mk_raw fp f = Float f <| t_float fp

    let mk fp s =
      match F.of_string_opt fp s with
      | Some f -> mk_raw fp f
      | None -> L.failwith "Invalid float literal: %S" s

    let mk_bits fp z = mk_raw fp (F.of_bits_z fp z)

    (* A mathematical integer, rounded to [fp]; a magnitude too large for the
       format gives an infinity. Unlike {!BitVec.to_float} the argument is not
       the contents of a bit-vector, so it is not reduced to any width. *)
    let of_z fp z = mk_raw fp (F.of_z fp z)

    let to_float_opt v =
      match v.node.kind with Float f -> Some (F.to_float f) | _ -> None

    let sign_bit_opt v =
      match v.node.kind with
      | Float f ->
          Some (Z.testbit (F.to_z f) (FloatPrecision.size (fp_of v) - 1))
      | _ -> None

    let approx f v =
      Option.map
        (fun x ->
          let fp = fp_of v in
          mk_raw fp (F.of_float fp (f x)))
        (to_float_opt v)

    let approx2 f v1 v2 =
      Option.map2
        (fun x1 x2 ->
          let fp = fp_of v1 in
          mk_raw fp (F.of_float fp (f x1 x2)))
        (to_float_opt v1) (to_float_opt v2)

    let zero fp = mk_raw fp (F.zero fp)
    let neg_zero fp = mk_raw fp (F.neg_zero fp)
    let one fp = mk_raw fp (F.one fp)
    let nan fp = mk_raw fp (F.nan fp)
    let infinity fp = mk_raw fp (F.infinity fp)
    let neg_infinity fp = mk_raw fp (F.neg_infinity fp)

    let to_bits_opt v =
      match v.node.kind with
      | Float f ->
          let size = FloatPrecision.size (fp_of v) in
          Some (BitVec.mk_masked size (F.to_z f))
      | _ -> None

    let is_floatclass fc sv = R.float_is_floatclass fc sv
    let is_normal = is_floatclass Normal
    let is_subnormal = is_floatclass Subnormal
    let is_infinite = is_floatclass Infinite
    let is_nan = is_floatclass NaN
    let is_zero = is_floatclass Zero
    let is_negative = R.float_is_negative
    let is_positive = R.float_is_positive
    let cast ~rounding ~fp v = R.float_cast rounding fp v
    let eq = R.float_eq
    let lt = R.float_lt
    let leq = R.float_leq
    let gt v1 v2 = lt v2 v1
    let geq v1 v2 = leq v2 v1
    let add = R.float_add
    let sub = R.float_sub
    let div = R.float_div
    let mul = R.float_mul
    let rem = R.float_rem
    let abs = R.float_abs
    let neg = R.float_neg
    let fma = R.float_fma
    let fmod_of_rem = R.float_fmod_of_rem
    let fmod = R.float_fmod
    let min = R.float_min
    let max = R.float_max

    (* The IEEE 754-2019 [minimum]/[maximum]: unlike {!min}/{!max} a NaN
       propagates, and [-0.0] is strictly below [+0.0]. SMT-Lib has neither, so
       they are built from comparisons. *)
    let minimum v1 v2 =
      Bool.ite (Bool.or_ (is_nan v1) (is_nan v2)) (nan (fp_of v1))
      @@ Bool.ite (lt v1 v2) v1
      @@ Bool.ite (lt v2 v1) v2
      @@ Bool.ite (is_negative v1) v1 v2

    let maximum v1 v2 =
      Bool.ite (Bool.or_ (is_nan v1) (is_nan v2)) (nan (fp_of v1))
      @@ Bool.ite (lt v1 v2) v2
      @@ Bool.ite (lt v2 v1) v1
      @@ Bool.ite (is_negative v1) v2 v1

    let sqrt = R.float_sqrt
    let round rm sv = R.float_round rm sv
  end

  (** {2 Pointers} *)

  module Ptr = struct
    let mk l o =
      assert (size_of l.node.ty = size_of o.node.ty);
      Ptr (l, o) <| TPointer (size_of o.node.ty)

    let loc = R.ptr_loc
    let null_loc n = BitVec Z.zero <| TLoc n
    let is_null_loc l = Bool.sem_eq l (null_loc (size_of l.node.ty))
    let loc_of_z n z = BitVec z <| TLoc n
    let loc_of_int n i = loc_of_z n (Z.of_int i)
    let ofs = R.ptr_ofs

    let decompose p =
      match p.node.kind with Ptr (l, o) -> (l, o) | _ -> (loc p, ofs p)

    let add_ofs p o =
      let loc, ofs = decompose p in
      mk loc (BitVec.add ofs o)

    let null n = mk (null_loc n) (BitVec.zero n)
    let is_null p = Bool.sem_eq p (null (size_of p.node.ty))
    let is_at_null_loc p = is_null_loc (loc p)
  end

  (** {2 Sequences} *)

  module SSeq = struct
    let mk ~seq_ty l = Seq l <| seq_ty

    let inner_ty ty =
      match ty with TSeq ty -> ty | _ -> L.failwith "Expected a sequence type"
  end

  (** {2 General constructors} *)

  (** {2 Infix operators} *)

  module Infix = struct
    let bv_z = BitVec.mk
    let ptr = Ptr.mk
    let seq = SSeq.mk
    let ( ==@ ) = Bool.sem_eq
    let ( ==?@ ) = Bool.sem_eq_untyped
    let ( &&@ ) = Bool.and_
    let ( ||@ ) = Bool.or_
    let ( >@ ) = BitVec.gt ~signed:false
    let ( >=@ ) = BitVec.geq ~signed:false
    let ( <@ ) = BitVec.lt ~signed:false
    let ( <=@ ) = BitVec.leq ~signed:false
    let ( >$@ ) = BitVec.gt ~signed:true
    let ( >=$@ ) = BitVec.geq ~signed:true
    let ( <$@ ) = BitVec.lt ~signed:true
    let ( <=$@ ) = BitVec.leq ~signed:true
    let ( +@ ) = BitVec.add ~checked:unchecked
    let ( -@ ) = BitVec.sub ~checked:unchecked
    let ( ~- ) v = BitVec.neg v
    let ( *@ ) = BitVec.mul ~checked:unchecked
    let ( /@ ) = BitVec.div ~signed:false
    let ( /$@ ) = BitVec.div ~signed:true
    let ( %@ ) = BitVec.rem ~signed:false
    let ( %$@ ) = BitVec.rem ~signed:true
    let ( <<@ ) = BitVec.shl
    let ( >>@ ) = BitVec.lshr
    let ( >>>@ ) = BitVec.ashr
    let ( ^@ ) = BitVec.xor
    let ( &@ ) = BitVec.and_
    let ( |@ ) = BitVec.or_
    let ( ==.@ ) = Float.eq
    let ( >.@ ) = Float.gt
    let ( >=.@ ) = Float.geq
    let ( <.@ ) = Float.lt
    let ( <=.@ ) = Float.leq
    let ( +.@ ) = Float.add
    let ( -.@ ) = Float.sub
    let ( *.@ ) = Float.mul
    let ( /.@ ) = Float.div
  end
end
