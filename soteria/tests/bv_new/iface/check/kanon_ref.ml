(** A hand-written OCaml REFERENCE implementation of {!Bv_iface.Kanon_fns} for
    the language of [Bv_new] (the C language in the new Kanon).

    It is the oracle of WP3a: the Kanon [fn]s of [rules/view.kn] must agree with
    it on every term (differential test at the level of the functions); and it
    lets WP3b and WP3c develop and test the generic layers before [view.kn]
    exists. The rules, the constants and the constructors are the real ones
    ([Bv_new.Rules], [Bv_new]); the view functions are ports of the code that
    they replace ([solver_lang.ml], [svalue.ml], [expr.ml]), written against the
    new constructors. Where the old printers exist they are reused (through a
    conversion of the operators) so that the pretty-printing is the old one by
    construction.

    Not intended to be fast. *)

open Bv_new.Types
module R = Bv_new.Rules
module Old = Soteria.Bv_values.Svalue
module Smt = Soteria.Smt
module Ptr_sort = Soteria.Bv_values.Encoding.Ptr_sort
module Var = Soteria.Symex.Var
module F = Floatml.AnyFloat
module FloatPrecision = Old.FloatPrecision
module View_host = Bv_iface.View_host
open View_host

type nonrec t = t
type nonrec ty = ty
type nonrec pphead = pphead
type smt_op = (t, ty) View_host.smt_op
type smt_sort_op = ty View_host.smt_sort_op

(* {1 RULES} *)

let sure_neq = R.sure_neq
let of_bool = R.of_bool
let b_and = R.b_and
let b_or = R.b_or
let b_not = R.b_not
let b_ite = R.b_ite
let sem_eq = R.sem_eq
let sem_eq_untyped = R.sem_eq_untyped
let b_distinct = R.b_distinct
let b_mk_exists = R.b_mk_exists
let bv_add = R.bv_add
let bv_sub = R.bv_sub
let bv_mul = R.bv_mul
let bv_div = R.bv_div
let bv_rem = R.bv_rem
let bv_mod = R.bv_mod
let bv_neg = R.bv_neg
let bv_add_overflows = R.bv_add_overflows
let bv_sub_overflows = R.bv_sub_overflows
let bv_mul_overflows = R.bv_mul_overflows
let bv_neg_overflows = R.bv_neg_overflows
let bv_lt = R.bv_lt
let bv_leq = R.bv_leq
let bv_concat = R.bv_concat
let bv_extend = R.bv_extend
let bv_extract = R.bv_extract
let bv_and = R.bv_and
let bv_or = R.bv_or
let bv_xor = R.bv_xor
let bv_shl = R.bv_shl
let bv_lshr = R.bv_lshr
let bv_ashr = R.bv_ashr
let bv_not = R.bv_not
let bv_of_bool = R.bv_of_bool
let bv_to_bool = R.bv_to_bool
let bv_not_bool = R.bv_not_bool
let bv_of_float = R.bv_of_float
let bv_to_float = R.bv_to_float
let bv_to_float_raw = R.bv_to_float_raw
let msb_of = R.msb_of
let float_is_floatclass = R.float_is_floatclass
let float_is_negative = R.float_is_negative
let float_is_positive = R.float_is_positive
let float_cast = R.float_cast
let float_eq = R.float_eq
let float_lt = R.float_lt
let float_leq = R.float_leq
let float_add = R.float_add
let float_sub = R.float_sub
let float_div = R.float_div
let float_mul = R.float_mul
let float_rem = R.float_rem
let float_fmod = R.float_fmod
let float_fmod_of_rem = R.float_fmod_of_rem
let float_min = R.float_min
let float_max = R.float_max
let float_abs = R.float_abs
let float_neg = R.float_neg
let float_sqrt = R.float_sqrt
let float_fma = R.float_fma
let float_round = R.float_round
let ptr_loc = R.ptr_loc
let ptr_ofs = R.ptr_ofs

(* {1 HOST} *)

let v_true = Bv_new.v_true
let v_false = Bv_new.v_false
let mk_var = Bv_new.mk_var
let mk_bv = Bv_new.mk_bv
let mk_masked = Bv_new.mk_masked
let bv_zero = Bv_new.bv_zero
let bv_one = Bv_new.bv_one
let mk_float = Bv_new.mk_float
let mk_loc = Bv_new.mk_loc
let mk_ptr = Bv_new.mk_ptr
let mk_seq s l = Bv_new.mk_seq ~seq_ty:s l

let rec to_old_ty : ty -> 'a Old.ty = function
  | TBool -> Old.TBool
  | TBitVector n -> Old.TBitVector n
  | TFloat p -> Old.TFloat p
  | TLoc n -> Old.TLoc n
  | TPointer n -> Old.TPointer n
  | TSeq s -> Old.TSeq (to_old_ty s)

(* the derived [show] of the old sorts *)
let pp_ty ft ty = Old.pp_ty (fun _ _ -> ()) ft (to_old_ty ty)

(* {1 VIEW: sorts} *)

let t_bool = TBool
let t_bv n = TBitVector (Z.to_int n)
let t_loc n = TLoc (Z.to_int n)
let t_ptr n = TPointer (Z.to_int n)
let t_float p = TFloat p
let t_seq s = TSeq s

let sized_ty = function
  | TBitVector n | TPointer n | TLoc n -> Some (Z.of_int n)
  | _ -> None

let as_bv_ty = function TBitVector n -> Some (Z.of_int n) | _ -> None
let as_float_ty = function TFloat p -> Some p | _ -> None
let as_seq_ty = function TSeq s -> Some s | _ -> None
let is_bool_ty = function TBool -> true | _ -> false

let size_of ty =
  match sized_ty ty with
  | Some n -> Z.to_int n
  | None -> failwith "Not a bit value"

(* {1 VIEW: recognisers} *)

let is_literal (v : t) =
  match v.kind with
  | Bool _ | BitVec _ | LocLit _ | Float _ -> true
  | _ -> false

let as_var (v : t) = match v.kind with Var x -> Some (x, v.ty) | _ -> None
let as_not (v : t) = match v.kind with Op1 (Not, x) -> Some x | _ -> None

let as_eq (v : t) =
  match v.kind with Op2 (Eq, l, r) -> Some (l, r) | _ -> None

let as_and (v : t) =
  match v.kind with Op2 (And, l, r) -> Some (l, r) | _ -> None

let as_or (v : t) =
  match v.kind with Op2 (Or, l, r) -> Some (l, r) | _ -> None

let as_ite (v : t) =
  match v.kind with Op3 (Ite, g, a, b) -> Some (g, a, b) | _ -> None

let as_lt (v : t) =
  match v.kind with Op2 (Lt _, l, r) -> Some (l, r) | _ -> None

let as_leq (v : t) =
  match v.kind with Op2 (Leq _, l, r) -> Some (l, r) | _ -> None

let as_distinct (v : t) =
  match v.kind with OpN (Distinct, l) -> Some l | _ -> None

let as_exists (v : t) =
  match v.kind with Exists (bs, b) -> Some (bs, b) | _ -> None

let as_ptr (v : t) =
  match v.kind with Op2 (Ptr, l, o) -> Some (l, o) | _ -> None

let as_bv_lit (v : t) = match v.kind with BitVec z -> Some z | _ -> None
let as_loc_lit (v : t) = match v.kind with LocLit z -> Some z | _ -> None
let as_float_lit (v : t) = match v.kind with Float f -> Some f | _ -> None

let rec conjuncts (v : t) : t list =
  match v.kind with Op2 (And, a, b) -> conjuncts a @ conjuncts b | _ -> [ v ]

let equal = equal_t

let implies_or_contradicts (q : t) (neg_q : t) (pc : t) : bool option =
  if equal q pc then Some true
  else if equal neg_q pc then Some false
  else
    match (q.kind, pc.kind) with
    (* [a < b] in PC implies [a <= b] *)
    | Op2 (Leq qs, qa, qb), Op2 (Lt ps, pa, pb)
      when qs = ps && equal qa pa && equal qb pb ->
        Some true
    (* [a < b] in PC implies ~[b <= a] and ~[b < a] *)
    | Op2 ((Lt qs | Leq qs), qa, qb), Op2 (Lt ps, pa, pb)
      when qs = ps && equal qa pb && equal qb pa ->
        Some false
    (* [a <= b] in PC implies ~[b < a] *)
    | Op2 (Lt qs, qa, qb), Op2 (Leq ps, pa, pb)
      when qs = ps && equal qa pb && equal qb pa ->
        Some false
    (* [a < b] (either direction) in PC implies ~[a = b] *)
    | Op2 (Eq, qa, qb), Op2 (Lt _, pa, pb)
      when (equal qa pa && equal qb pb) || (equal qa pb && equal qb pa) ->
        Some false
    (* [a < b] (either direction) in PC implies [~(a = b)] *)
    | Op1 (Not, { kind = Op2 (Eq, qa, qb); _ }), Op2 (Lt _, pa, pb)
      when (equal qa pa && equal qb pb) || (equal qa pb && equal qb pa) ->
        Some true
    | _ -> None

(* The intervals: [solver_lang.ml:303-445] *)
let pow2 n = Z.shift_left Z.one n
let neg_mod size x = Z.sub (pow2 size) x

(* [x mod 2^n], for [x] possibly negative *)
let to_bv n x = Z.(logand x (pred (shift_left one n)))

let rec as_range (v : t) : (Var.t * Z.t * (range_sign * (Z.t * Z.t))) option =
  let ( - ) = Z.sub and ( + ) = Z.add and ( < ) = Z.lt and ( <= ) = Z.leq in
  let one = Z.one in
  let ret x size r = Some (x, Z.of_int size, r) in
  match v.kind with
  (* Case 2: c1 <=u c2 + x *)
  | Op2
      ( ((Lt false | Leq false) as bop),
        { kind = BitVec c1; ty = TBitVector size; _ },
        ({
           kind =
             ( Var x
             | Op2 (Add _, { kind = Var x; _ }, { kind = BitVec _; _ })
             | Op2 (Add _, { kind = BitVec _; _ }, { kind = Var x; _ }) );
           _;
         } as rhs) ) ->
      let c1 = if bop = Lt false then Z.succ c1 else c1 in
      let c2 =
        match rhs.kind with
        | Var _ -> Z.zero
        | Op2 (Add _, { kind = BitVec c2; _ }, _)
        | Op2 (Add _, _, { kind = BitVec c2; _ }) ->
            c2
        | _ -> failwith "unreachable"
      in
      if c1 < c2 then
        ret x size (Outside, (neg_mod size c2, to_bv size (c1 - c2 - one)))
      else ret x size (Inside, (c1 - c2, to_bv size (neg_mod size c2 - one)))
  (* Case 3: c1 + x <=u c2 *)
  | Op2
      ( ((Lt false | Leq false) as bop),
        ({
           kind =
             ( Var x
             | Op2 (Add _, { kind = Var x; _ }, { kind = BitVec _; _ })
             | Op2 (Add _, { kind = BitVec _; _ }, { kind = Var x; _ }) );
           _;
         } as lhs),
        { kind = BitVec c2; ty = TBitVector size; _ } ) ->
      let c1 =
        match lhs.kind with
        | Var _ -> Z.zero
        | Op2 (Add _, { kind = BitVec c1; _ }, _)
        | Op2 (Add _, _, { kind = BitVec c1; _ }) ->
            c1
        | _ -> failwith "unreachable"
      in
      let c2 = if bop = Lt false then Z.pred c2 else c2 in
      if c1 <= c2 then ret x size (Outside, (c2 - c1 + one, neg_mod size one))
      else ret x size (Inside, (neg_mod size c1, neg_mod size c1 + c2))
  (* Case 4: x <=s c1 *)
  | Op2
      ( ((Lt true | Leq true) as bop),
        { kind = Var x; _ },
        { kind = BitVec c1; ty = TBitVector size; _ } ) ->
      let c1 = if bop = Lt true then Z.pred c1 else c1 in
      let mid = pow2 (Stdlib.( - ) size 1) in
      if c1 < mid then ret x size (Outside, (c1 + one, mid - one))
      else ret x size (Inside, (mid, c1))
  (* Case 5: c1 <=s x *)
  | Op2
      ( ((Lt true | Leq true) as bop),
        { kind = BitVec c1; ty = TBitVector size; _ },
        { kind = Var x; _ } ) ->
      let c1 = if bop = Lt true then Z.succ c1 else c1 in
      let mid = pow2 (Stdlib.( - ) size 1) in
      if c1 < mid then ret x size (Inside, (c1, mid - one))
      else ret x size (Outside, (mid, c1 - one))
  (* Simple equality *)
  | Op2 (Eq, { kind = BitVec x; ty = TBitVector size; _ }, { kind = Var y; _ })
  | Op2 (Eq, { kind = Var y; _ }, { kind = BitVec x; ty = TBitVector size; _ })
    ->
      ret y size (Inside, (x, x))
  | Op1 (Not, v) ->
      Option.map
        (fun (v1, size, (side, range)) ->
          ( v1,
            size,
            ((match side with Outside -> Inside | Inside -> Outside), range) ))
        (as_range v)
  | _ -> None

(* {1 VIEW: operands and rebuilding} *)

let operands (v : t) : t list =
  match v.kind with
  | Var _ | Bool _ | BitVec _ | LocLit _ | Float _ -> []
  | Seq l -> l
  | Exists (_, b) -> [ b ]
  | Op1 (_, a) -> [ a ]
  | Op2 (_, a, b) -> [ a; b ]
  | Op3 (_, a, b, c) -> [ a; b; c ]
  | OpN (_, l) -> l

let rebuild (v : t) (cs : t list) : t =
  let bad () = failwith "rebuild: wrong number of operands" in
  let z = Z.of_int in
  match (v.kind, cs) with
  | (Var _ | Bool _ | BitVec _ | LocLit _ | Float _), [] -> v
  | Seq _, l -> mk_seq v.ty l
  | Exists (bs, _), [ a ] -> b_mk_exists bs a
  | Op1 (op, _), [ a ] -> (
      match op with
      | Not -> b_not a
      | GetPtrLoc -> ptr_loc a
      | GetPtrOfs -> ptr_ofs a
      | BvOfBool n -> bv_of_bool (z n) a
      | BvOfFloat (rm, s, n) -> bv_of_float rm s (z n) a
      | FloatOfBv (rm, s, p) -> bv_to_float rm s p a
      | FloatOfBvRaw _ -> bv_to_float_raw a
      | FloatOfFloat (rm, p) -> float_cast rm p a
      | BvExtract (f, t) -> bv_extract (z f) (z t) a
      | BvExtend (s, k) -> bv_extend s (z k) a
      | BvNot -> bv_not a
      | Neg c -> bv_neg c a
      | FAbs -> float_abs a
      | FNeg -> float_neg a
      | FSqrt -> float_sqrt a
      | FIs fc -> float_is_floatclass fc a
      | FIsNeg -> float_is_negative a
      | FIsPos -> float_is_positive a
      | FRound rm -> float_round rm a)
  | Op2 (op, _, _), [ a; b ] -> (
      match op with
      | And -> b_and a b
      | Or -> b_or a b
      | Eq -> sem_eq a b
      | Add c -> bv_add c a b
      | Sub c -> bv_sub c a b
      | Mul c -> bv_mul c a b
      | Div s -> bv_div s a b
      | Rem s -> bv_rem s a b
      | Mod -> bv_mod a b
      | AddOvf s -> bv_add_overflows s a b
      | SubOvf s -> bv_sub_overflows s a b
      | MulOvf s -> bv_mul_overflows s a b
      | Lt s -> bv_lt s a b
      | Leq s -> bv_leq s a b
      | BvConcat -> bv_concat a b
      | BitAnd -> bv_and a b
      | BitOr -> bv_or a b
      | BitXor -> bv_xor a b
      | Shl -> bv_shl a b
      | LShr -> bv_lshr a b
      | AShr -> bv_ashr a b
      | FEq -> float_eq a b
      | FLeq -> float_leq a b
      | FLt -> float_lt a b
      | FAdd -> float_add a b
      | FSub -> float_sub a b
      | FMul -> float_mul a b
      | FDiv -> float_div a b
      | FRem -> float_rem a b
      | FMin -> float_min a b
      | FMax -> float_max a b
      | Ptr -> mk_ptr a b)
  | Op3 (op, _, _, _), [ a; b; c ] -> (
      match op with Ite -> b_ite a b c | Fma -> float_fma a b c)
  | OpN (Distinct, _), l -> b_distinct l
  | _ -> bad ()

let maps_operands (v : t) : bool =
  match v.kind with
  | Op1 _ -> true
  | Op2 (Ptr, _, _) -> false
  | Op2 _ -> true
  | _ -> false

(* {1 VIEW: cost and model search} *)

let node_cost (v : t) : Z.t =
  Z.of_int
    (match v.kind with
    | Var _ -> 3
    | Float _ -> 2
    | Seq _ -> 0
    | Exists _ -> 100_000
    | Bool _ | BitVec _ | LocLit _ -> 1
    | Op3 (Fma, _, _, _) -> 400
    | Op3 (Ite, _, _, _) -> 0
    | OpN (Distinct, _) -> 0
    | Op2 (op, _, _) -> (
        match op with
        | FRem -> 12900
        | Div true | Rem true | Mod -> 12700
        | Rem false -> 7100
        | Div false -> 3600
        | Mul _ -> 1900
        | FDiv -> 1300
        | FMul -> 345
        | MulOvf _ -> 200
        | FAdd | FSub -> 130
        | Sub _ -> 97
        | Add _ -> 75
        | Shl | LShr | AShr -> 35
        | FMin | FMax -> 24
        | FLt | FLeq | SubOvf true -> 12
        | AddOvf true -> 9
        | AddOvf false | SubOvf false | Lt _ | Leq _ -> 5
        | FEq -> 3
        | And | Or | Eq | BitAnd | BitOr | BitXor | BvConcat -> 1
        | Ptr -> 1)
    | Op1 (op, _) -> (
        match op with
        | BvOfFloat _ -> 1400
        | FSqrt -> 280
        | FloatOfFloat _ -> 255
        | FloatOfBv _ -> 78
        | FRound _ -> 65
        | Neg _ -> 10
        | FAbs | FNeg | FloatOfBvRaw _ -> 4
        | Not | GetPtrLoc | GetPtrOfs | BvNot | BvOfBool _ | BvExtend _
        | BvExtract _ | FIs _ | FIsNeg | FIsPos ->
            1))

let rec cost (v : t) : Z.t =
  match v.kind with
  | Op2 (Ptr, _, _) -> Z.one
  | _ ->
      List.fold_left
        (fun acc c -> Z.add acc (cost c))
        (node_cost v) (operands v)

let random_bound (s : ty) : Z.t option =
  match s with
  | TLoc n | TBitVector n -> Some (pow2 n)
  | TBool -> Some (Z.of_int 2)
  | TFloat p -> Some (pow2 (FloatPrecision.size p))
  | TPointer _ | TSeq _ -> None

let random_of_z (s : ty) (z : Z.t) : t option =
  match s with
  | TLoc n -> Some (mk_loc n z)
  | TBitVector n -> Some (mk_bv n z)
  | TBool -> Some (of_bool (Z.equal z Z.one))
  | TFloat p -> Some (mk_float (F.of_bits_z p z))
  | TPointer _ | TSeq _ -> None

(* {1 VIEW: SMT encoding} *)

module Enc = struct
  open Smt

  let rm_to_smt : Old.RoundingMode.t -> Smt.RoundingMode.t = function
    | NearestTiesToEven -> NearestTiesToEven
    | NearestTiesToAway -> NearestTiesToAway
    | Ceil -> Ceil
    | Floor -> Floor
    | Truncate -> Truncate

  let smt_of_unop ~ty : op1 -> sexp -> sexp = function
    | Not -> bool_not
    | FAbs -> fp_abs
    | FNeg -> fp_neg
    | FSqrt -> fp_sqrt
    | GetPtrLoc -> Ptr_sort.get_loc (size_of ty)
    | GetPtrOfs -> Ptr_sort.get_ofs (size_of ty)
    | BvOfBool n -> fun b -> ite b (bv_k n Z.one) (bv_k n Z.zero)
    | BvOfFloat (rm, true, n) -> sbv_of_float (rm_to_smt rm) n
    | BvOfFloat (rm, false, n) -> ubv_of_float (rm_to_smt rm) n
    | FloatOfBv (rm, true, fp) ->
        float_of_sbv (rm_to_smt rm) (FloatPrecision.size fp)
    | FloatOfBv (rm, false, fp) ->
        float_of_ubv (rm_to_smt rm) (FloatPrecision.size fp)
    | FloatOfBvRaw fp -> float_of_bv (FloatPrecision.size fp)
    | FloatOfFloat (rm, fp) ->
        float_of_float (rm_to_smt rm) (FloatPrecision.size fp)
    | BvExtract (from_, to_) -> bv_extract to_ from_
    | BvExtend (true, by) -> bv_sign_extend by
    | BvExtend (false, by) -> bv_zero_extend by
    | BvNot -> bv_not
    | Neg _ -> bv_neg
    | FIs fc -> fp_is (Old.FloatClass.as_fpclass fc)
    | FIsNeg -> fp_is_negative
    | FIsPos -> fp_is_positive
    | FRound rm -> fp_round (rm_to_smt rm)

  let smt_of_binop : op2 -> sexp -> sexp -> sexp = function
    | Eq -> eq
    | And -> bool_and
    | Or -> bool_or
    | FEq -> fp_eq
    | FLeq -> fp_leq
    | FLt -> fp_lt
    | FAdd -> fp_add
    | FSub -> fp_sub
    | FMul -> fp_mul
    | FDiv -> fp_div
    | FRem -> fp_rem
    | FMin -> fp_min
    | FMax -> fp_max
    | BitAnd -> bv_and
    | BitOr -> bv_or
    | BitXor -> bv_xor
    | Shl -> bv_shl
    | LShr -> bv_lshr
    | AShr -> bv_ashr
    | Add _ -> bv_add
    | Sub _ -> bv_sub
    | Mul _ -> bv_mul
    | Div true -> bv_sdiv
    | Div false -> bv_udiv
    | Rem true -> bv_srem
    | Rem false -> bv_urem
    | Mod -> bv_smod
    | AddOvf true -> bv_saddo
    | AddOvf false -> bv_uaddo
    | SubOvf true -> bv_ssubo
    | SubOvf false -> bv_usubo
    | MulOvf true -> bv_smulo
    | MulOvf false -> bv_umulo
    | Lt true -> bv_slt
    | Lt false -> bv_ult
    | Leq true -> bv_sleq
    | Leq false -> bv_uleq
    | BvConcat -> bv_concat
    | Ptr -> assert false

  let smt_of_triop : op3 -> sexp -> sexp -> sexp -> sexp = function
    | Fma -> fp_fma
    | Ite -> ite

  let encode_var v = atom (Var.to_string v)

  let encode_head (v : t) : smt_op =
   fun ~sort_of_ty ~encode_child ops ->
    match (v.kind, ops) with
    | Var x, [] -> encode_var x
    | Float f, [] ->
        let size =
          match v.ty with
          | TFloat p -> FloatPrecision.size p
          | _ -> failwith "float"
        in
        float_of_bv size (bv_k size (F.to_z f))
    | Bool b, [] -> bool_k b
    | (BitVec z | LocLit z), [] -> bv_k (size_of v.ty) z
    | Op2 (Ptr, _, _), [ l; o ] ->
        (* the old code applied the encoders as arguments: right to left *)
        let eo = encode_child o in
        let el = encode_child l in
        Ptr_sort.mk_ptr (size_of v.ty) el eo
    | Seq vs, _ -> (
        match vs with
        | [] -> failwith "need type to encode empty lists"
        | _ :: _ ->
            List.map (fun v -> seq_singl (encode_child v)) vs |> seq_concat)
    | Exists (vs, _), [ body ] ->
        let encode_binder (v, ty) = list [ encode_var v; sort_of_ty ty ] in
        (* the body first: the old code applied the encoders as arguments *)
        let body = encode_child body in
        exists (List.map encode_binder vs) body
    | Op1 (op, _), [ a ] ->
        let e1 = encode_child a in
        smt_of_unop ~ty:a.ty op e1
    | Op2 (op, _, _), [ a; b ] ->
        let e1 = encode_child a in
        let e2 = encode_child b in
        smt_of_binop op e1 e2
    | Op3 (op, _, _, _), [ a; b; c ] ->
        (* right to left, as the old code *)
        let e3 = encode_child c in
        let e2 = encode_child b in
        let e1 = encode_child a in
        smt_of_triop op e1 e2 e3
    | OpN (Distinct, _), vs -> distinct (List.map encode_child vs)
    | _ -> failwith "encode_head: wrong number of operands"

  let encode_sort (s : ty) : smt_sort_op =
   fun ~sort_of_ty comps ->
    match (s, comps) with
    | TBool, _ -> t_bool
    | TLoc n, _ -> t_bits n
    | TFloat F16, _ -> t_f16
    | TFloat F32, _ -> t_f32
    | TFloat F64, _ -> t_f64
    | TFloat F128, _ -> t_f128
    | TSeq _, [ c ] -> t_seq (sort_of_ty c)
    | TPointer n, _ -> Ptr_sort.sort n
    | TBitVector n, _ -> t_bits n
    | TSeq _, _ -> failwith "encode_sort: a sequence has one component"

  let sort_operands : ty -> ty list = function TSeq s -> [ s ] | _ -> []
end

let encode_head = Enc.encode_head
let encode_sort = Enc.encode_sort
let sort_operands = Enc.sort_operands

(* {1 VIEW: pretty-printing and learning} *)

let old_unop : op1 -> Old.Unop.t = function
  | Not -> Old.Unop.Not
  | GetPtrLoc -> Old.Unop.GetPtrLoc
  | GetPtrOfs -> Old.Unop.GetPtrOfs
  | BvOfBool n -> Old.Unop.BvOfBool n
  | BvOfFloat (rm, s, n) -> Old.Unop.BvOfFloat (rm, s, n)
  | FloatOfBv (rm, s, p) -> Old.Unop.FloatOfBv (rm, s, p)
  | FloatOfBvRaw p -> Old.Unop.FloatOfBvRaw p
  | FloatOfFloat (rm, p) -> Old.Unop.FloatOfFloat (rm, p)
  | BvExtract (f, t) -> Old.Unop.BvExtract (f, t)
  | BvExtend (s, k) -> Old.Unop.BvExtend (s, k)
  | BvNot -> Old.Unop.BvNot
  | Neg c -> Old.Unop.Neg c
  | FAbs -> Old.Unop.FAbs
  | FNeg -> Old.Unop.FNeg
  | FSqrt -> Old.Unop.FSqrt
  | FIs fc -> Old.Unop.FIs fc
  | FIsNeg -> Old.Unop.FIsNeg
  | FIsPos -> Old.Unop.FIsPos
  | FRound rm -> Old.Unop.FRound rm

let old_binop : op2 -> Old.Binop.t = function
  | And -> Old.Binop.And
  | Or -> Old.Binop.Or
  | Eq -> Old.Binop.Eq
  | Add c -> Old.Binop.Add c
  | Sub c -> Old.Binop.Sub c
  | Mul c -> Old.Binop.Mul c
  | Div s -> Old.Binop.Div s
  | Rem s -> Old.Binop.Rem s
  | Mod -> Old.Binop.Mod
  | AddOvf s -> Old.Binop.AddOvf s
  | SubOvf s -> Old.Binop.SubOvf s
  | MulOvf s -> Old.Binop.MulOvf s
  | Lt s -> Old.Binop.Lt s
  | Leq s -> Old.Binop.Leq s
  | BvConcat -> Old.Binop.BvConcat
  | BitAnd -> Old.Binop.BitAnd
  | BitOr -> Old.Binop.BitOr
  | BitXor -> Old.Binop.BitXor
  | Shl -> Old.Binop.Shl
  | LShr -> Old.Binop.LShr
  | AShr -> Old.Binop.AShr
  | FEq -> Old.Binop.FEq
  | FLeq -> Old.Binop.FLeq
  | FLt -> Old.Binop.FLt
  | FAdd -> Old.Binop.FAdd
  | FSub -> Old.Binop.FSub
  | FMul -> Old.Binop.FMul
  | FDiv -> Old.Binop.FDiv
  | FRem -> Old.Binop.FRem
  | FMin -> Old.Binop.FMin
  | FMax -> Old.Binop.FMax
  | Ptr -> assert false

let ph_text s : pphead = fun ft -> Fmt.string ft s

let pp_style (v : t) : pp_style =
  match v.kind with
  | Var x -> PAtom (fun ft -> Fmt.pf ft "V%a" Var.pp x)
  | Bool b -> PAtom (fun ft -> Fmt.pf ft "%b" b)
  | Float f -> PAtom (fun ft -> Fmt.pf ft "%sf" (F.to_string f))
  | BitVec bv | LocLit bv ->
      let size = size_of v.ty in
      PAtom
        (fun ft ->
          if size mod 4 <> 0 then
            Fmt.pf ft "0b%s" (Z.format ("0" ^ string_of_int size ^ "b") bv)
          else
            Fmt.pf ft "0x%s"
              (Z.format ("0" ^ string_of_int (size / 4) ^ "x") bv))
  | Seq _ -> PBrackets
  | Exists (vs, _) ->
      let var_pp ft (v, ty) = Fmt.pf ft "V%a:%a" Var.pp v pp_ty ty in
      PSeq
        [
          PText
            (fun ft -> Fmt.pf ft "∃ %a. " (Fmt.list ~sep:Fmt.comma var_pp) vs);
          PArg Z.zero;
        ]
  | Op1 (Not, { kind = Op2 (Eq, _, _); _ }) ->
      PSeq
        [
          PText (ph_text "(");
          PArgOf (Z.zero, Z.zero);
          PText (ph_text " != ");
          PArgOf (Z.zero, Z.one);
          PText (ph_text ")");
        ]
  | Op1 (op, _) -> PCall (fun ft -> Old.Unop.pp ft (old_unop op))
  | Op2 (Ptr, _, _) -> PCallPlain (ph_text "&")
  | Op2 (op, _, _) -> PIn (fun ft -> Old.Binop.pp ft (old_binop op))
  | Op3 (Ite, _, _, _) -> PIte
  | Op3 (Fma, _, _, _) -> PCallPlain (fun ft -> Old.Triop.pp ft Old.Triop.Fma)
  | OpN (Distinct, l) -> (
      let rec aux = function
        | acc, [] -> acc
        | Some l, { kind = Var v; _ } :: rest ->
            aux (Some (Var.to_int v :: l), rest)
        | _, _ -> None
      in
      let range =
        Option.bind
          (aux (Some [], l))
          (fun l ->
            match List.sort Int.compare l with
            | [] -> None
            | hd :: _ as l ->
                let max = List.hd (List.rev l) in
                if max - hd + 1 = List.length l then Some (hd, max) else None)
      in
      let head ft = Old.Nop.pp ft Old.Nop.Distinct in
      match range with
      | Some (min, max) ->
          PAtom (fun ft -> Fmt.pf ft "%t(V|%d-%d|)" head min max)
      | None -> PCall head)

let learn_alts (v : t) : learn_plan =
  let z = Z.of_int in
  match v.kind with
  | Op1 ((Not | BvNot | Neg _ | BvExtend _ | BvOfBool _), _) ->
      LAll ([], [ z 0 ])
  | Op2 ((Add _ | Sub _ | BitXor), _, _) -> LAlts [ (z 0, z 1); (z 1, z 0) ]
  | Op2 (BvConcat, _, _) -> LAll ([ z 1; z 0 ], [ z 0; z 1 ])
  | Op2 (Ptr, _, _) -> LAll ([], [ z 0; z 1 ])
  | _ -> LNone

let learn_value (e : t) (i : Z.t) (v : t) : t option =
  let i = Z.to_int i in
  let z = Z.of_int in
  match (e.kind, i) with
  | Op1 (Not, _), 0 -> Some (b_not v)
  | Op1 (BvNot, _), 0 -> Some (bv_not v)
  | Op1 (Neg _, _), 0 -> Some (bv_neg false v)
  | Op1 (BvExtend _, e'), 0 -> Some (bv_extract (z 0) (z (size_of e'.ty - 1)) v)
  | Op1 (BvOfBool _, _), 0 -> (
      match v.kind with
      | BitVec zv when Z.equal zv Z.zero -> Some v_false
      | BitVec zv when Z.equal zv Z.one -> Some v_true
      | _ -> None)
  | Op2 (Add _, _, e2), 0 -> Some (bv_sub R.unchecked v e2)
  | Op2 (Add _, e1, _), 1 -> Some (bv_sub R.unchecked v e1)
  | Op2 (Sub _, _, e2), 0 -> Some (bv_add R.unchecked v e2)
  | Op2 (Sub _, e1, _), 1 -> Some (bv_sub R.unchecked e1 v)
  | Op2 (BitXor, _, e2), 0 -> Some (bv_xor v e2)
  | Op2 (BitXor, e1, _), 1 -> Some (bv_xor v e1)
  | Op2 (BvConcat, e1, e2), 1 ->
      ignore e1;
      Some (bv_extract (z 0) (z (size_of e2.ty - 1)) v)
  | Op2 (BvConcat, e1, e2), 0 ->
      let size_e2 = size_of e2.ty and size_e1 = size_of e1.ty in
      Some (bv_extract (z size_e2) (z (size_e2 + size_e1 - 1)) v)
  | Op2 (Ptr, _, _), 0 -> Some (ptr_loc v)
  | Op2 (Ptr, _, _), 1 -> Some (ptr_ofs v)
  | _ -> None
