open Logs.Import
open Hc
open Soteria_std
module Var = Symex.Var

(** Concrete floating-point values, of any of the four precisions. *)
module F = Floatml.AnyFloat

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

module Nop = struct
  type t = Distinct [@@deriving eq, ord, hash]

  let pp ft = function Distinct -> Fmt.string ft "distinct"
  let show = Fmt.to_to_string pp
end

module Triop = struct
  type t = Fma | Ite [@@deriving eq, ord, hash]

  let pp ft = function Fma -> Fmt.string ft "fma" | Ite -> Fmt.string ft "ite"
  let show = Fmt.to_to_string pp
end

module Unop = struct
  type t =
    | Not
    | GetPtrLoc
    | GetPtrOfs
    | BvOfBool of int (* target bitvec size *)
    | BvOfFloat of RoundingMode.t * bool * int (* signed * target bitvec size *)
    | FloatOfBv of
        RoundingMode.t * bool * FloatPrecision.t (* signed * precision *)
    | FloatOfBvRaw of FloatPrecision.t
    | FloatOfFloat of RoundingMode.t * FloatPrecision.t (* target precision *)
    | BvExtract of int * int (* from idx (incl) * to idx (incl) *)
    | BvExtend of bool * int (* signed * by N bits *)
    | BvNot
    | Neg of bool
    (* is this negation overflow-checked (operand <> INT_MIN, so it behaves like
       exact integer negation)? for optimisations only *)
    | FAbs
    | FNeg
    | FSqrt
    | FIs of FloatClass.t
    | FIsNeg
    | FIsPos
    | FRound of RoundingMode.t
  [@@deriving eq, ord, hash]

  let pp_signed ft b = Fmt.string ft (if b then "s" else "u")

  let pp ft = function
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
    | FRound mode -> Fmt.pf ft "fround(%a)" RoundingMode.pp mode
end

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

module Binop = struct
  type t =
    (* Bool *)
    | And
    | Or
    (* Comparison *)
    | Eq
    (* Float comparison *)
    | FEq
    | FLeq
    | FLt
    (* Float arith *)
    | FAdd
    | FSub
    | FMul
    | FDiv
    | FRem
    | FMin
    | FMax
    (* BitVector arithmetic *)
    | Add of checked
      (* in which signedness(es) is this overflow-checked? for optimisations
         only *)
    | Sub of checked
      (* in which signedness(es) is this overflow-checked? for optimisations
         only *)
    | Mul of checked
      (* in which signedness(es) is this overflow-checked? for optimisations
         only *)
    | Div of bool (* signed *)
    | Rem of bool (* signed *)
    | Mod
    | AddOvf of bool (* signed *)
    | SubOvf of bool (* signed *)
    | MulOvf of bool (* signed *)
    | Lt of bool (* signed *)
    | Leq of bool (* signed *)
    (* Bitvector bit operations *)
    | BvConcat
    | BitAnd
    | BitOr
    | BitXor
    | Shl
    | LShr
    | AShr
  [@@deriving eq, show { with_path = false }, ord, hash]

  let pp_signed ft b = Fmt.string ft (if b then "s" else "u")

  let pp_checked ft = function
    | { signed = false; unsigned = false } -> ()
    | { signed = true; unsigned = false } -> Fmt.string ft "cks"
    | { signed = false; unsigned = true } -> Fmt.string ft "cku"
    | { signed = true; unsigned = true } -> Fmt.string ft "ck"

  let pp ft = function
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
    | Add checked -> Fmt.pf ft "+%a" pp_checked checked
    | Sub checked -> Fmt.pf ft "-%a" pp_checked checked
    | Mul checked -> Fmt.pf ft "*%a" pp_checked checked
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
end

type 'ty ty =
  | TBool
  | TFloat of FloatPrecision.t
  | TLoc of int
  | TPointer of int (* size of location and offset *)
  | TSeq of 'ty ty
  | TBitVector of int
  | TExtension of 'ty
[@@deriving eq, show { with_path = false }, ord]

let[@inline] hash_combine h x = (h * 65599) + x

let rec hash_ty hash_ext = function
  | TBool -> 1
  | TFloat p -> hash_combine 2 (FloatPrecision.size p)
  | TLoc n -> hash_combine 3 n
  | TPointer n -> hash_combine 4 n
  | TSeq ty -> hash_combine 5 (hash_ty hash_ext ty)
  | TBitVector n -> hash_combine 6 n
  | TExtension e -> hash_combine 7 (hash_ext e)

let pp_hash_consed pp_node ft t = pp_node ft t.node
let equal_hash_consed _ t1 t2 = Int.equal t1.tag t2.tag
let compare_hash_consed _ t1 t2 = Int.compare t1.tag t2.tag

(* The phantom ['ghost] parameter is never inhabited; it exists solely to make
   the values produced by one application of {!Make} type-incompatible with
   those of another. Since each (generative) application of {!Make} mints a
   fresh abstract [ghost], values hash-consed in one application's table can
   never be confused with another's. *)
type ('ghost, 't, 'ty) t_kind =
  | Var of Var.t
  | Bool of bool
  | Float of F.t
  | Ptr of ('ghost, 't, 'ty) t * ('ghost, 't, 'ty) t
  | BitVec of Z.t [@printer Fmt.of_to_string (Z.format "%#x")]
  | Seq of ('ghost, 't, 'ty) t list
  | Unop of Unop.t * ('ghost, 't, 'ty) t
  | Binop of Binop.t * ('ghost, 't, 'ty) t * ('ghost, 't, 'ty) t
  | Triop of
      Triop.t * ('ghost, 't, 'ty) t * ('ghost, 't, 'ty) t * ('ghost, 't, 'ty) t
  | Nop of Nop.t * ('ghost, 't, 'ty) t list
  | Exists of (Var.t * 'ty ty) list * ('ghost, 't, 'ty) t
  | Extension of 't

and ('ghost, 't, 'ty) t_node = { kind : ('ghost, 't, 'ty) t_kind; ty : 'ty ty }

and ('ghost, 't, 'ty) t = ('ghost, 't, 'ty) t_node hash_consed
[@@deriving show { with_path = false }, eq, ord]

let[@inline] equal a b = Int.equal a.tag b.tag
let[@inline] compare a b = Int.compare a.tag b.tag

(** How to embed a domain-specific {e extension} into the otherwise fixed svalue
    grammar. An extension contributes:
    - a new value leaf [t], reachable through the [Extension] node, and
    - a new type [ty], reachable through the [TExtension] type.

    {!Make} weaves these into the value/type definitions and threads the
    operations below through hash-consing, evaluation, substitution and SMT
    encoding, so the extension behaves like a first-class part of the grammar.
    Tools needing no extra leaves use {!Dummy_ext} instead.

    Throughout, [super_t] is the {e enclosing} svalue (the whole grammar,
    including this extension) and [super_ty] its type. Both stay polymorphic in
    the ['ghost] minted by {!Make}: an extension is defined before any
    application of {!Make}, so it cannot — and must not — name a concrete ghost.
    Each operation instead receives svalue-level callbacks already specialised
    to the embedding application's ghost, and applies them to the svalues nested
    inside an extension value. *)
module type Value_ext = sig
  (** [_ super_t] is the enclosing svalue *)
  type ('ghost, 't, 'ty) super_t := ('ghost, 't, 'ty) t

  (** [_ super_ty] is the enclosing svalue type *)
  type 'ty super_ty := 'ty ty

  (** Extension value leaves; appear in svalues through [Extension]. *)
  type 'ghost t [@@deriving eq, ord]

  (** Extension types; appear in svalue types through [TExtension]. *)
  type 'ghost ty [@@deriving eq, ord]

  type 'g super_ty := 'g ty super_ty
  type 'g super_t := ('g, 'g t, 'g ty) super_t

  val pp : 'g super_t Fmt.t -> 'g t Fmt.t
  val pp_ty : 'g ty Fmt.t
  val iter_vars : ('g super_t -> unit) -> 'g t -> unit
  val hash : 'g t -> int
  val hash_ty : 'g ty -> int

  (** [mk build ty x] is the value representing extension value [x] at type [ty]
      — typically [build (Extension x) ty], but the extension may normalise to a
      different svalue for simplifications.

      [build] hash-conses a node kind at a type in the embedding
      {{!Soteria.Bv_values.Svalue.Make}[Make]} application. It is provided as a
      helper. *)
  val mk :
    (('g, 'g t, 'g ty) t_kind -> 'g super_ty -> 'g super_t) ->
    'g super_ty ->
    'g t ->
    'g super_t

  (** [eval eval_super x] returns [x] with every enclosing svalue nested in it
      replaced by [eval_super] applied to it. This should {b not} attempt to
      re-apply smart constructors: if the returned value is not physically equal
      to the input, {!mk} will be applied to it, at which point smart
      constructors are used. *)
  val eval : ('g super_t -> 'g super_t) -> 'g t -> 'g t

  val apply_subst :
    (missing_var:(Var.t -> 'g super_ty -> 'g super_t) ->
    'subst ->
    'g super_t ->
    'g super_t * 'subst) ->
    missing_var:(Var.t -> 'g super_ty -> 'g super_t) ->
    'subst ->
    'g t ->
    'g t * 'subst

  (** [learn build learn_super subst x v] extends [subst] so that it maps the
      free variables of the extension value [x] in such a way that [x] and the
      value [v] become equal, or returns [None] if [x] cannot be inverted.

      [learn_super] performs the same operation on the svalues nested in [x],
      and [build] is as in {!mk}. *)
  val learn :
    (('g, 'g t, 'g ty) t_kind -> 'g super_ty -> 'g super_t) ->
    ('subst -> 'g super_t -> 'g super_t -> 'subst option) ->
    'subst ->
    'g t ->
    'g super_t ->
    'subst option

  (** [encode_ty encode_ty ty] is the SMT-LIB sort representing [ty];
      [encode_ty] encodes the types nested inside it. The encoder may use
      {{!Soteria.Solvers.Decls.declare}[Solvers.Decls.declare]} to introduce
      auxiliary declarations (e.g. algebraic datatypes) its encoding relies on.
  *)
  val encode_ty : ('g super_ty -> Smt.sexp) -> 'g ty -> Smt.sexp

  (** [encode_value encode_ty encode ~ty x] is the SMT-LIB term representing
      extension value [x], where [ty] is the type of the svalue whose kind is
      [Extension x]; [encode_ty] (resp. [encode]) encodes nested types (resp.
      values). Like {!encode_ty}, may call
      {{!Soteria.Solvers.Decls.declare}[Solvers.Decls.declare]}. *)
  val encode_value :
    ('g super_ty -> Smt.sexp) ->
    ('g super_t -> Smt.sexp) ->
    ty:'g super_ty ->
    'g t ->
    Smt.sexp
end

(** The empty extension: [t] and [ty] are uninhabited, so an svalue built with
    [Dummy_ext] never contains an [Extension] node nor a [TExtension] type, and
    every operation above is vacuous. This is the right choice for tools (such
    as soteria-c and soteria-rust) whose values need nothing beyond the built-in
    bit-vector / float / pointer grammar. *)
module Dummy_ext : Value_ext = struct
  type 'ghost t = | [@@deriving eq, ord]
  type 'ghost ty = | [@@deriving eq, ord]

  let iter_vars _ (x : _ t) = match x with _ -> .
  let hash (x : _ t) = match x with _ -> .
  let hash_ty (x : _ ty) = match x with _ -> .
  let pp _ _ (x : _ t) = match x with _ -> .
  let pp_ty _ (x : _ ty) = match x with _ -> .
  let mk _ _ (x : _ t) = match x with _ -> .
  let eval _ (x : _ t) = match x with _ -> .
  let apply_subst _ ~missing_var:_ _ (x : _ t) = match x with _ -> .
  let learn _ _ _ (x : _ t) _ = match x with _ -> .
  let encode_ty _ (x : _ ty) = match x with _ -> .
  let encode_value _ _ ~ty:_ (x : _ t) = match x with _ -> .
end
