(* The host primitives of the view functions ([rules/view.kn]): the SMT
   operators and sorts, and the few functions that Kanon cannot express. They
   are ported from the [Enc] module of the SMT encoding of the first generation
   of the value language, over the types that Kanon generates.

   [Bv_prims] includes this module: the generated rules call all primitives
   there, and check them against their declarations. *)

open Bv_types

(* the aliases are private: [Bv_prims] has its own *)
open struct
  module L = Logs.Import.L
  module Var = Symex.Var
  module F = Floatml.AnyFloat
  module FloatPrecision = Bv_base.FloatPrecision
  module FloatClass = Bv_base.FloatClass
  module RoundingMode = Bv_base.RoundingMode
  module Ptr_sort = Ptr_sort
  module Smt = Smt
  module View_host = View_host
end

type smt_op = (t, ty) View_host.smt_op
type smt_sort_op = ty View_host.smt_sort_op

let vsize = function
  | TBitVector n | TPointer n | TLoc n -> n
  | _ -> L.failwith "Not a bit value"

(* {1 Terms that Kanon does not build} *)

(* No simplification, and the sizes of the operands must be equal *)
let mk_ptr (l : t) (o : t) : t =
  let n = vsize o.ty in
  assert (vsize l.ty = n);
  node (Op2 (Ptr, l, o)) (TPointer n)

let mk_seq (s : ty) (l : t list) : t = node (Seq l) s
let bad_operands (_ : t) : t = L.failwith "rebuild: wrong number of operands"

(* {1 Printing} *)

(* What [ppx_deriving show] generated for the sorts: [(TBitVector 32)] *)
let rec pp_ty ft = function
  | TBool -> Format.pp_print_string ft "TBool"
  | TFloat p -> Format.fprintf ft "(@[<2>TFloat@ %a@])" FloatPrecision.pp p
  | TLoc n -> Format.fprintf ft "(@[<2>TLoc@ %d@])" n
  | TPointer n -> Format.fprintf ft "(@[<2>TPointer@ %d@])" n
  | TSeq s -> Format.fprintf ft "(@[<2>TSeq@ %a@])" pp_ty s
  | TBitVector n -> Format.fprintf ft "(@[<2>TBitVector@ %d@])" n

(* {1 SMT encoding}

   The operators apply to the operands of the term. The order of the calls to
   [encode_child] is that of the old [encode_node]: it is the order in which the
   declarations are emitted. *)

let rm_to_smt : RoundingMode.t -> Smt.RoundingMode.t = function
  | NearestTiesToEven -> NearestTiesToEven
  | NearestTiesToAway -> NearestTiesToAway
  | Ceil -> Ceil
  | Floor -> Floor
  | Truncate -> Truncate

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
  let size =
    match ty with
    | TFloat p -> FloatPrecision.size p
    | _ -> L.failwith "Unsupported float type"
  in
  Smt.float_of_bv size (Smt.bv_k size (F.to_z f))

let h_bool b : smt_op = fun ~sort_of_ty:_ ~encode_child:_ _ -> Smt.bool_k b

let h_bits ty z : smt_op =
 fun ~sort_of_ty:_ ~encode_child:_ _ -> Smt.bv_k (vsize ty) z

(* the offset is encoded before the location *)
let h_ptr ty : smt_op =
 fun ~sort_of_ty:_ ~encode_child -> function
  | [ l; o ] ->
      let eo = encode_child o in
      let el = encode_child l in
      Ptr_sort.mk_ptr (vsize ty) el eo
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
      Ptr_sort.get_loc (vsize a.ty) e1
  | _ -> wrong ()

let h_ptr_ofs : smt_op =
 fun ~sort_of_ty:_ ~encode_child -> function
  | [ a ] ->
      let e1 = encode_child a in
      Ptr_sort.get_ofs (vsize a.ty) e1
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

let h_bv_extract from_ to_ = un (Smt.bv_extract (Z.to_int to_) (Z.to_int from_))

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
  | F16 -> Smt.t_f16
  | F32 -> Smt.t_f32
  | F64 -> Smt.t_f64
  | F128 -> Smt.t_f128

let so_seq : smt_sort_op =
 fun ~sort_of_ty -> function
  | [ c ] -> Smt.t_seq (sort_of_ty c)
  | _ -> L.failwith "encode_sort: a sequence has one component"
