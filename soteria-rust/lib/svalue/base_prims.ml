(* The host primitives of the rules ([rules/*.kn]), ported from [Prims] and the
   constants of [Svalue.Make] (soteria/lib/bv_values/svalue.ml), over the types
   that Kanon generates ([Bv_types]).

   The rule functions ([Bv_rules]) call this module and check it against the
   declarations of the rules ([prim] and [oracle] items), at their types: the
   integers of Kanon are [Z.t], and a bit-vector literal is a [Z.t] in [0, 2^n)
   of the width [n] of its sort, which the folds take as arguments, after the
   sorts of their operands. *)

open Rust_types
module L = Soteria.Logs.Import.L
module Var = Soteria.Symex.Var
module F = Floatml.AnyFloat
module FloatPrecision = Soteria.Bv_values.Svalue.FloatPrecision
module FloatClass = Soteria.Bv_values.Svalue.FloatClass

let sort_by_tag (l : t list) = List.sort (fun l r -> Int.compare l.tag r.tag) l

(* {1 Constants}

   The order of their creation is the order of their tags, which decides the
   order of the operands of commutative operators: it is that of the application
   of the old [Svalue.Make] functor: [v_true], [v_false], the zero literals of 1
   to 256 bits, then the one literals of 1 to 256 bits. *)

let v_true = node (Bool true) TBool
let v_false = node (Bool false) TBool

let mk_bv_int n bv =
  assert (n > 0);
  assert (Z.(zero <= bv && bv < one lsl n));
  node (BitVec bv) (TBitVector n)

(* Bitwidth -> [(1 lsl n) - 1] mask. Memoized to avoid re-allocating the mask
   bignum on each [mk_masked] call (expensive in pathological cases). *)
let mask_cache : Z.t Array.t = Array.init 256 (fun n -> Z.(pred (one lsl n)))
let mask_of_bits n = if n <= 255 then mask_cache.(n) else Z.(pred (one lsl n))

let mk_masked_int n bv =
  let mask = mask_of_bits n in
  node (BitVec (Z.logand bv mask)) (TBitVector n)

(* Index [n-1] holds the cached value for bitwidth [n]; we skip [n=0] because
   [mk_bv] asserts [n > 0]. *)
let zero_cache : t Array.t = Array.init 256 (fun n -> mk_bv_int (n + 1) Z.zero)

let[@inline] bv_zero_int n =
  if n <= 256 then zero_cache.(n - 1) else mk_bv_int n Z.zero

let one_cache : t Array.t = Array.init 256 (fun n -> mk_bv_int (n + 1) Z.one)

let[@inline] bv_one_int n =
  if n <= 256 then one_cache.(n - 1) else mk_bv_int n Z.one

(* {1 Primitives of the rules} *)

(* PATCH (Rust): the operands of the nodes of the rust module, left to right
   (the same as [operands] of the generated rules, which this module cannot
   call) *)
let rust_operands (k : kind) : t list =
  match k with
  | ThinPtr { ptr; psize; palign; _ } -> [ ptr; psize; palign ]
  | FullPtr (p, m) -> [ p; m ]
  | PtrMeta (MetaLen l | MetaVTable l) -> [ l ]
  | PtrMeta MetaUnit | PolyVal _ -> []
  | Enum (_, vs) | Tuple vs -> vs
  | Array vs -> Soteria.Soteria_std.Iarray.to_list vs
  | Union bs ->
      List.concat_map
        (fun { bvalue; boffset; bsize } ->
          let v = match bvalue with Scalar v | Aggregate (v, _) -> v in
          [ v; boffset; bsize ])
        bs
  | ThinPtrPart (_, a)
  | FullPtrInner a
  | FullPtrMeta a
  | PtrMetaAs (_, a)
  | Field (_, a)
  | VariantField (_, _, a)
  | IsVariant (_, a)
  | ArrayField (_, a) ->
      [ a ]
  | _ -> assert false

let used_binders_iter_vars (sv : t) (f : Var.t * ty -> unit) : unit =
  let rec aux ~ignore (sv : t) : unit =
    let aux' = aux ~ignore in
    match sv.kind with
    | Var v -> if Var.Set.mem v ignore then () else f (v, sv.ty)
    | Bool _ | Float _ | BitVec _ | LocLit _ -> ()
    | Op2 (_, l, r) ->
        aux' l;
        aux' r
    | Op1 (_, sv) -> aux' sv
    | Op3 (_, a, b, c) ->
        aux' a;
        aux' b;
        aux' c
    | OpN (_, l) | Seq l -> List.iter aux' l
    (* PATCH (Rust) *)
    | ( ThinPtr _ | FullPtr _ | PtrMeta _ | Enum _ | Tuple _ | Array _ | Union _
      | PolyVal _ | ThinPtrPart _ | FullPtrInner _ | FullPtrMeta _ | PtrMetaAs _
      | Field _ | VariantField _ | IsVariant _ | ArrayField _ ) as k ->
        List.iter aux' (rust_operands k)
    | Exists (vs, sv) ->
        let ignore =
          List.fold_left (fun ignore (v, _) -> Var.Set.add v ignore) ignore vs
        in
        aux ~ignore sv
  in
  aux ~ignore:Var.Set.empty sv

let used_binders binders body =
  let body_vars =
    Var.Hashset.of_iter (used_binders_iter_vars body |> Iter.map fst)
  in
  List.filter (fun (v, _) -> Var.Hashset.mem body_vars v) binders

let[@inline] size_of = function
  | TBitVector n -> n
  | TPointer n -> n
  | TLoc n -> n
  | _ -> L.failwith "Not a bit value"

let[@inline] size_of_ty ty = Z.of_int (size_of ty)
let mk_bv n z = mk_bv_int (Z.to_int n) z
let mk_masked n z = mk_masked_int (Z.to_int n) z
let bv_zero n = bv_zero_int (Z.to_int n)
let bv_one n = bv_one_int (Z.to_int n)

let fp_of_ty = function
  | TFloat fp -> fp
  | _ -> L.failwith "Unsupported float type"

(* {2 Folds on literals}

   The old folds took values with their width ([{ w; z }]); these take the sorts
   of their operands and the integers. *)

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
  match Soteria.Bv_values.Svalue.int_size_of_size (Z.to_int size) with
  | Some int_size -> F.float2int f int_size rounding ~signed
  | None -> None

let f_of_int rounding signed fp size z =
  match Soteria.Bv_values.Svalue.int_size_of_size (Z.to_int size) with
  | Some int_size -> Some (F.int2float z int_size fp rounding ~signed)
  | None -> None

(* The primitives of the view functions ([rules/view.kn]): the generated rules
   call and check all of them here *)
include Base_view_prims
