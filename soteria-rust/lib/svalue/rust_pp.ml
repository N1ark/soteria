(* The pretty-printer of the terms of the Rust language, over its generated
   types: the shared nodes are printed as in the C language (the output, break
   hints included, is that of the printer of the first generation of the value
   language), and the nodes of rust.kn as the old extension printed them. *)

open Rust_types
module Var = Soteria.Symex.Var
module F = Floatml.AnyFloat
module FloatPrecision = Soteria.Bv_values.Bv_base.FloatPrecision
module FloatClass = Soteria.Bv_values.Bv_base.FloatClass
module RoundingMode = Soteria.Bv_values.Bv_base.RoundingMode

let pp_signed ft b = Fmt.string ft (if b then "s" else "u")

let pp_checked ft = function
  | { signed = false; unsigned = false } -> ()
  | { signed = true; unsigned = false } -> Fmt.string ft "cks"
  | { signed = false; unsigned = true } -> Fmt.string ft "cku"
  | { signed = true; unsigned = true } -> Fmt.string ft "ck"

let pp_bv ft (ty : ty) bv =
  let size = Rust_prims.size_of ty in
  if size mod 4 <> 0 then
    Fmt.pf ft "0b%s" (Z.format ("0" ^ string_of_int size ^ "b") bv)
  else Fmt.pf ft "0x%s" (Z.format ("0" ^ string_of_int (size / 4) ^ "x") bv)

let pp_binder ft (v, ty) = Fmt.pf ft "V%a:%a" Var.pp v Rust_encoding.pp_ty ty

(* The variables of the list, if they all are, and their range if their numbers
   are contiguous *)
let distinct_range (l : t list) : (int * int) option =
  let rec aux = function
    | acc, [] -> acc
    | Some l, { kind = Var v; _ } :: rest -> aux (Some (Var.to_int v :: l), rest)
    | _, _ -> None
  in
  Stdlib.Option.bind
    (aux (Some [], l))
    (fun l ->
      match List.sort Int.compare l with
      | [] -> None
      | hd :: _ as l ->
          let max = List.hd (List.rev l) in
          if max - hd + 1 = List.length l then Some (hd, max) else None)

let pp_op1 ft = function
  | Not -> Fmt.string ft "!"
  | FAbs -> Fmt.string ft "abs."
  | FNeg -> Fmt.string ft "neg."
  | FSqrt -> Fmt.string ft "sqrt."
  | GetPtrLoc -> Fmt.string ft "loc"
  | GetPtrOfs -> Fmt.string ft "ofs"
  | BvOfBool n -> Fmt.pf ft "b2bv[%d]" n
  | BvOfFloat (rm, signed, n) ->
      Fmt.pf ft "f2%abv[%a,%d]" pp_signed signed RoundingMode.pp rm n
  | FloatOfBv (rm, signed, p) ->
      Fmt.pf ft "%abv2f[%a,%a]" pp_signed signed RoundingMode.pp rm
        FloatPrecision.pp p
  | FloatOfBvRaw p -> Fmt.pf ft "bv2f[%a]" FloatPrecision.pp p
  | FloatOfFloat (rm, p) ->
      Fmt.pf ft "f2f[%a,%a]" RoundingMode.pp rm FloatPrecision.pp p
  | BvExtract (from, to_) -> Fmt.pf ft "extract[%d-%d]" from to_
  | BvExtend (signed, by) -> Fmt.pf ft "extend[%a%d]" pp_signed signed by
  | BvNot -> Fmt.string ft "!bv"
  | Neg checked -> Fmt.pf ft "-%s" (if checked then "ck" else "")
  | FIs fc -> Fmt.pf ft "fis(%a)" FloatClass.pp fc
  | FIsNeg -> Fmt.string ft "fisneg"
  | FIsPos -> Fmt.string ft "fispos"
  | FRound rm -> Fmt.pf ft "fround(%a)" RoundingMode.pp rm
  | FullPtrInner -> Fmt.string ft "thin"
  | FullPtrMeta -> Fmt.string ft "meta"
  | IsVariant var -> Fmt.pf ft "is<%a>" Charon.Types.pp_variant_id var
  | ArrayField i -> Fmt.pf ft "[%d]" i

let pp_op2 ft = function
  | Ptr -> Fmt.string ft "&"
  | And -> Fmt.string ft "&&"
  | Or -> Fmt.string ft "||"
  | Eq -> Fmt.string ft "=="
  | FEq -> Fmt.string ft "==."
  | FLeq -> Fmt.string ft "<=."
  | FLt -> Fmt.string ft "<."
  | FAdd -> Fmt.string ft "+."
  | FSub -> Fmt.string ft "-."
  | FMul -> Fmt.string ft "*."
  | FDiv -> Fmt.string ft "/."
  | FRem -> Fmt.string ft "rem."
  | FMin -> Fmt.string ft "min."
  | FMax -> Fmt.string ft "max."
  | Add c -> Fmt.pf ft "+%a" pp_checked c
  | Sub c -> Fmt.pf ft "-%a" pp_checked c
  | Mul c -> Fmt.pf ft "*%a" pp_checked c
  | Div s -> Fmt.pf ft "/%a" pp_signed s
  | Rem s -> Fmt.pf ft "rem%a" pp_signed s
  | Mod -> Fmt.string ft "mod"
  | AddOvf s -> Fmt.pf ft "+%a_ovf" pp_signed s
  | SubOvf s -> Fmt.pf ft "-%a_ovf" pp_signed s
  | MulOvf s -> Fmt.pf ft "*%a_ovf" pp_signed s
  | Lt s -> Fmt.pf ft "<%a" pp_signed s
  | Leq s -> Fmt.pf ft "<=%a" pp_signed s
  | BvConcat -> Fmt.string ft "++"
  | BitAnd -> Fmt.string ft "&"
  | BitOr -> Fmt.string ft "|"
  | BitXor -> Fmt.string ft "^"
  | Shl -> Fmt.string ft "<<"
  | LShr -> Fmt.string ft "l>>"
  | AShr -> Fmt.string ft "a>>"

let pp_meta_part ft = function
  | PartLen -> Fmt.string ft "len"
  | PartVTable -> Fmt.string ft "vtable"

let rec pp ft (t : t) =
  match t.kind with
  | Var x -> Fmt.pf ft "V%a" Var.pp x
  | Bool b -> Fmt.pf ft "%b" b
  | Float f -> Fmt.pf ft "%sf" (F.to_string f)
  | BitVec z | LocLit z -> pp_bv ft t.ty z
  | Seq l -> Fmt.brackets (Fmt.list ~sep:Fmt.comma pp) ft l
  | Exists (bs, body) ->
      Fmt.pf ft "∃ %a. %a" (Fmt.list ~sep:Fmt.comma pp_binder) bs pp body
  | Op1 (Not, { kind = Op2 (Eq, a, b); _ }) -> Fmt.pf ft "(%a != %a)" pp a pp b
  | Op1 (IsVariant var, a) ->
      Fmt.pf ft "%a.is<%a>" pp a Charon.Types.pp_variant_id var
  | Op1 (ArrayField i, a) -> Fmt.pf ft "%a[%d]" pp a i
  | Op1 (op, a) -> Fmt.pf ft "%a(%a)" pp_op1 op pp a
  | Op2 (Ptr, a, b) -> Fmt.pf ft "%a(%a, %a)" pp_op2 Ptr pp a pp b
  | Op2 (op, a, b) -> Fmt.pf ft "(%a %a %a)" pp a pp_op2 op pp b
  | Op3 (Ite, c, a, b) -> Fmt.pf ft "(%a ? %a : %a)" pp c pp a pp b
  | Op3 (Fma, a, b, c) -> Fmt.pf ft "fma(%a, %a, %a)" pp a pp b pp c
  | OpN (Distinct, l) -> (
      match distinct_range l with
      | Some (lo, hi) -> Fmt.pf ft "distinct(V|%d-%d|)" lo hi
      | None -> Fmt.pf ft "distinct(%a)" (Fmt.list ~sep:Fmt.comma pp) l)
  | ThinPtr { ptr; ptag; _ } ->
      Fmt.pf ft "%a[%a]" pp ptr
        Fmt.(option ~none:(any "*") Rust_host.Ptr_tag.pp)
        ptag
  | FullPtr (p, m) -> Fmt.pf ft "Ptr(%a, %a)" pp p pp m
  | PtrMeta MetaUnit -> Fmt.string ft "()"
  | PtrMeta (MetaLen l) -> Fmt.pf ft "len(%a)" pp l
  | PtrMeta (MetaVTable l) -> Fmt.pf ft "vtable(%a)" pp l
  | Enum (var, vs) ->
      Fmt.pf ft "Enum(%a: %a)" Charon.Types.pp_variant_id var
        (Fmt.list ~sep:(Fmt.any ", ") pp)
        vs
  | Tuple vs -> Fmt.pf ft "(%a)" (Fmt.list ~sep:(Fmt.any ", ") pp) vs
  | Array vs ->
      Fmt.pf ft "[%a]"
        (Fmt.list ~sep:(Fmt.any ", ") pp)
        (Soteria.Soteria_std.Iarray.to_list vs)
  | Union bs ->
      Fmt.string ft "Union(";
      List.iteri (fun i b -> pp_block ft ~first:(i = 0) b) bs;
      Fmt.string ft ")"
  | PolyVal id -> Fmt.pf ft "PolyVal(%a)" Charon.Types.pp_type_var_id id
  | ThinPtrPart (part, a) ->
      Fmt.pf ft "%a.%a" pp a Rust_encoding.pp_ptr_part part
  | PtrMetaAs (part, a) -> Fmt.pf ft "%a.as<%a>" pp a pp_meta_part part
  | Field (i, a) -> Fmt.pf ft "%a.%d" pp a i
  | VariantField (var, i, a) ->
      Fmt.pf ft "%a.as<%a>.%d" pp a Charon.Types.pp_variant_id var i

and pp_block ft ~first (b : block) =
  if not first then Fmt.string ft ", ";
  Fmt.pf ft "(%a: " pp b.boffset;
  (match b.bvalue with
  | Scalar v -> pp ft v
  | Aggregate (v, ty) -> Fmt.pf ft "%a : %a" pp v Charon.Types.pp_ty ty);
  Fmt.pf ft "-%a)" pp b.bsize
