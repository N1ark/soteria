(* The host primitives of the view functions ([rules/view.kn]): the heads of the
   pretty-printer, the SMT operators and sorts, and the few functions that Kanon
   cannot express. They are ported from the printers and the [Enc] module of the
   SMT encoding of the first generation of the value language, over the types
   that Kanon generates.

   [Bv_prims] includes this module: the generated rules call all primitives
   there, and check them against their declarations. *)

open Rust_types

(* the aliases are private: [Bv_prims] has its own *)
open struct
  module L = Soteria.Logs.Import.L
  module Var = Soteria.Symex.Var
  module F = Floatml.AnyFloat
  module FloatPrecision = Soteria.Bv_values.Bv_base.FloatPrecision
  module FloatClass = Soteria.Bv_values.Bv_base.FloatClass
  module RoundingMode = Soteria.Bv_values.Bv_base.RoundingMode
  module Ptr_sort = Soteria.Bv_values.Encoding.Ptr_sort
  module Smt = Soteria.Smt
  module View_host = Iface.View_host
end

type pphead = View_host.pphead
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
  (* PATCH (Rust): the sorts of the rust module were the sorts of the extension,
     [TExtension X] printed by [pp_ext_ty] (ext_base.ml) *)
  | ( TEnum _ | TUnion _ | TTuple _ | TArray _ | TThinPtr | TFullPtr | TPtrMeta
    | TPolyType ) as x ->
      Format.fprintf ft "(@[<2>TExtension@ %a@])" pp_ext_ty x

and pp_ext_ty ft = function
  | TEnum ty -> Crate.pp_type_decl_ref ft ty
  | TUnion ty -> Crate.pp_type_decl_ref ft ty
  | TTuple tys -> Fmt.(brackets (list ~sep:semi pp_ty)) ft tys
  | TArray (ty, n) -> Fmt.pf ft "[%a; %a]" pp_ty ty Z.pp_print n
  | TThinPtr -> Fmt.string ft "TThinPtr"
  | TFullPtr -> Fmt.string ft "TFullPtr"
  | TPtrMeta -> Fmt.string ft "TPtrMeta"
  | TPolyType -> Fmt.string ft "TPolyType"
  | TBool | TFloat _ | TLoc _ | TPointer _ | TSeq _ | TBitVector _ ->
      assert false

(* The variables of the list, if they all are, and their range if their numbers
   are contiguous *)
let distinct_range (l : t list) : (Z.t * Z.t) option =
  let rec aux = function
    | acc, [] -> acc
    | Some l, { kind = Var v; _ } :: rest -> aux (Some (Var.to_int v :: l), rest)
    | _, _ -> None
  in
  (* PATCH (Rust): [Stdlib], as this library opens [Soteria_std], whose
     [Option.bind] takes its arguments the other way round *)
  Stdlib.Option.bind
    (aux (Some [], l))
    (fun l ->
      match List.sort Int.compare l with
      | [] -> None
      | hd :: _ as l ->
          let max = List.hd (List.rev l) in
          if max - hd + 1 = List.length l then Some (Z.of_int hd, Z.of_int max)
          else None)

let ph_text s : pphead = fun ft -> Fmt.string ft s
let ph_var x : pphead = fun ft -> Fmt.pf ft "V%a" Var.pp x
let ph_bool b : pphead = fun ft -> Fmt.pf ft "%b" b
let ph_float f : pphead = fun ft -> Fmt.pf ft "%sf" (F.to_string f)

let ph_bv ty bv : pphead =
 fun ft ->
  let size = vsize ty in
  if size mod 4 <> 0 then
    Fmt.pf ft "0b%s" (Z.format ("0" ^ string_of_int size ^ "b") bv)
  else Fmt.pf ft "0x%s" (Z.format ("0" ^ string_of_int (size / 4) ^ "x") bv)

let ph_exists vs : pphead =
 fun ft ->
  let var_pp ft (v, ty) = Fmt.pf ft "V%a:%a" Var.pp v pp_ty ty in
  Fmt.pf ft "∃ %a. " (Fmt.list ~sep:Fmt.comma var_pp) vs

let ph_lparen = ph_text "("
let ph_rparen = ph_text ")"
let ph_neq = ph_text " != "
let ph_distinct = ph_text "distinct"

let ph_distinct_range lo hi : pphead =
 fun ft -> Fmt.pf ft "distinct(V|%s-%s|)" (Z.to_string lo) (Z.to_string hi)

let pp_signed ft b = Fmt.string ft (if b then "s" else "u")

let pp_checked ft = function
  | { signed = false; unsigned = false } -> ()
  | { signed = true; unsigned = false } -> Fmt.string ft "cks"
  | { signed = false; unsigned = true } -> Fmt.string ft "cku"
  | { signed = true; unsigned = true } -> Fmt.string ft "ck"

(* {2 Unary operators} *)

let ph_not = ph_text "!"
let ph_fabs = ph_text "abs."
let ph_fneg = ph_text "neg."
let ph_fsqrt = ph_text "sqrt."
let ph_ptr_loc = ph_text "loc"
let ph_ptr_ofs = ph_text "ofs"
let ph_bv_of_bool n : pphead = fun ft -> Fmt.pf ft "b2bv[%a]" Z.pp_print n

let ph_bv_of_float rm signed n : pphead =
 fun ft ->
  Fmt.pf ft "f2%abv[%a,%a]" pp_signed signed RoundingMode.pp rm Z.pp_print n

let ph_float_of_bv rm signed p : pphead =
 fun ft ->
  Fmt.pf ft "%abv2f[%a,%a]" pp_signed signed RoundingMode.pp rm
    FloatPrecision.pp p

let ph_float_of_bv_raw p : pphead =
 fun ft -> Fmt.pf ft "bv2f[%a]" FloatPrecision.pp p

let ph_float_of_float rm p : pphead =
 fun ft -> Fmt.pf ft "f2f[%a,%a]" RoundingMode.pp rm FloatPrecision.pp p

let ph_bv_extract from to_ : pphead =
 fun ft -> Fmt.pf ft "extract[%a-%a]" Z.pp_print from Z.pp_print to_

let ph_bv_extend signed by : pphead =
 fun ft -> Fmt.pf ft "extend[%a%a]" pp_signed signed Z.pp_print by

let ph_bv_not = ph_text "!bv"

let ph_neg checked : pphead =
 fun ft -> Fmt.pf ft "-%s" (if checked then "ck" else "")

let ph_fis fc : pphead = fun ft -> Fmt.pf ft "fis(%a)" FloatClass.pp fc
let ph_fisneg = ph_text "fisneg"
let ph_fispos = ph_text "fispos"
let ph_fround rm : pphead = fun ft -> Fmt.pf ft "fround(%a)" RoundingMode.pp rm

(* {2 Binary and ternary operators} *)

let ph_ptr = ph_text "&"
let ph_and = ph_text "&&"
let ph_or = ph_text "||"
let ph_eq = ph_text "=="
let ph_feq = ph_text "==."
let ph_fleq = ph_text "<=."
let ph_flt = ph_text "<."
let ph_fadd = ph_text "+."
let ph_fsub = ph_text "-."
let ph_fmul = ph_text "*."
let ph_fdiv = ph_text "/."
let ph_frem = ph_text "rem."
let ph_fmin = ph_text "min."
let ph_fmax = ph_text "max."
let ph_add c : pphead = fun ft -> Fmt.pf ft "+%a" pp_checked c
let ph_sub c : pphead = fun ft -> Fmt.pf ft "-%a" pp_checked c
let ph_mul c : pphead = fun ft -> Fmt.pf ft "*%a" pp_checked c
let ph_div s : pphead = fun ft -> Fmt.pf ft "/%a" pp_signed s
let ph_rem s : pphead = fun ft -> Fmt.pf ft "rem%a" pp_signed s
let ph_mod = ph_text "mod"
let ph_add_ovf s : pphead = fun ft -> Fmt.pf ft "+%a_ovf" pp_signed s
let ph_sub_ovf s : pphead = fun ft -> Fmt.pf ft "-%a_ovf" pp_signed s
let ph_mul_ovf s : pphead = fun ft -> Fmt.pf ft "*%a_ovf" pp_signed s
let ph_lt s : pphead = fun ft -> Fmt.pf ft "<%a" pp_signed s
let ph_leq s : pphead = fun ft -> Fmt.pf ft "<=%a" pp_signed s
let ph_concat = ph_text "++"
let ph_bit_and = ph_text "&"
let ph_bit_or = ph_text "|"
let ph_bit_xor = ph_text "^"
let ph_shl = ph_text "<<"
let ph_lshr = ph_text "l>>"
let ph_ashr = ph_text "a>>"
let ph_fma = ph_text "fma"

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
