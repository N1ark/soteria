(** The primitives of the rules of [rules/*.bvr] that do not depend on the
    instance of {!Svalue.Make}; the others are in [Svalue.Make.Prims]. *)

open Logs.Import
open Hc
open Svalue_ast

let sort_by_tag (l : _ t list) =
  List.sort (fun l r -> Int.compare l.tag r.tag) l

let[@inline] size_of = function
  | TBitVector n -> n
  | TPointer n -> n
  | TLoc n -> n
  | _ -> L.failwith "Not a bit value"

let[@inline] size_of_ty ty = Z.of_int (size_of ty)

let fp_of_ty = function
  | TFloat fp -> fp
  | _ -> L.failwith "Unsupported float type"

type bv = { w : int; z : Z.t }

let[@inline] bv_of_lit (v : _ t) =
  match v.node.kind with
  | BitVec z -> { w = size_of v.node.ty; z }
  | _ -> L.failwith "bv_of_lit: not a literal"

let[@inline] width l = Z.of_int l.w
let[@inline] to_z signed l = if signed then Z.signed_extract l.z 0 l.w else l.z
let[@inline] masked w z = { w; z = Z.extract z 0 w }
let of_z n z = masked (Z.to_int n) z
let lit_add a b = masked a.w (Z.add a.z b.z)
let lit_sub a b = masked a.w (Z.sub a.z b.z)
let lit_mul a b = masked a.w (Z.mul a.z b.z)
let lit_neg a = masked a.w (Z.neg a.z)

let lit_udiv a b =
  let d = Z.extract b.z 0 a.w in
  if Z.equal d Z.zero then masked a.w Z.minus_one else masked a.w (Z.div a.z d)

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
let lit_concat l r = { w = l.w + r.w; z = Z.logor (Z.shift_left l.z r.w) r.z }
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
