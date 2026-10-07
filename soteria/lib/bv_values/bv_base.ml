(** Host types shared by the generated value languages: the types that the
    [[@ocaml "..."]] annotations of their [lang.knl] refer to. *)

open Logs.Import

(** Concrete floating-point values, of any of the four precisions. *)
module F = Floatml.AnyFloat

module Var = Symex.Var

module FloatPrecision = struct
  type t = F.precision = F16 | F32 | F64 | F128

  let equal = F.equal_precision
  let compare = F.compare_precision
  let hash = F.hash_precision
  let pp = F.pp_precision
  let show = F.show_precision
  let size = F.size
  let exponent_bits = F.exponent_bits
  let significand_bits = F.significand_bits

  let of_size n =
    match F.of_size n with
    | Some p -> p
    | None -> L.failwith "Invalid float size"
end

module FloatClass = struct
  type t = Normal | Subnormal | Zero | Infinite | NaN
  [@@deriving eq, show { with_path = false }, ord, hash]

  let as_fpclass = function
    | Normal -> FP_normal
    | Subnormal -> FP_subnormal
    | Zero -> FP_zero
    | Infinite -> FP_infinite
    | NaN -> FP_nan
end

module RoundingMode = struct
  type t = Floatml.rounding_mode =
    | NearestTiesToEven
    | Truncate
    | Ceil
    | Floor
    | NearestTiesToAway

  let equal = Floatml.equal_rounding_mode
  let compare = Floatml.compare_rounding_mode
  let hash = Floatml.hash_rounding_mode
  let pp = Floatml.pp_rounding_mode
  let show = Floatml.show_rounding_mode
end

(** The [Floatml] integer width for a bit-vector of [n] bits, if [Floatml] can
    convert that width to or from a float. *)
let int_size_of_size = function
  | 8 -> Some Floatml.Int8
  | 16 -> Some Floatml.Int16
  | 32 -> Some Floatml.Int32
  | 64 -> Some Floatml.Int64
  | 128 -> Some Floatml.Int128
  | _ -> None

(** For an arithmetic operation, records the signedness(es) in which it is known
    not to overflow, and so behaves like exact integer arithmetic. This is used
    to justify simplifications. *)
type checked = { signed : bool; unsigned : bool }
[@@deriving eq, show { with_path = false }, ord, hash]

let unchecked = { signed = false; unsigned = false }
let checked_both = { signed = true; unsigned = true }
let checked_signed = { signed = true; unsigned = false }
let checked_unsigned = { signed = false; unsigned = true }

let checked_of_signed signed =
  if signed then checked_signed else checked_unsigned

(** Whether [c] guarantees no overflow in the given signedness. *)
let checked_has ~signed c = if signed then c.signed else c.unsigned

(** Whether [c] guarantees no overflow in at least one signedness. *)
let is_checked c = c.signed || c.unsigned

(** The strongest flag justified by both [a] and [b], i.e. the intersection of
    their guarantees. Used when a simplification rebuilds an operation from two
    already-checked ones. [is_checked (checked_meet a b)] thus tells whether [a]
    and [b] share a signedness in which both are exact. *)
let checked_meet a b =
  { signed = a.signed && b.signed; unsigned = a.unsigned && b.unsigned }
