(** The OLD simplifier: [Typed.Make (Dummy_ext) ()], hand-written types, rules
    generated from the pinned Kanon.

    {!Raw_of_typed} exposes the raw rule functions ([Svalue.R.*]) of any
    instantiation. {!Api} is the old side proper: every entry point goes through
    the public typed API (BitVec.add, Float.minimum, Ptr.add_ofs...). *)

open Tm
module B = Soteria.Bv_values
module Sv = B.Svalue
module V = Soteria.Symex.Var

module Raw_of_typed
    (T : B.Typed.S)
    (N : sig
      val name : string
    end) : sig
  include Side.RAW

  val of_t : T.Svalue.t -> t
  val to_t : t -> T.Svalue.t
  val ty_of_sort : sort -> T.Svalue.ty
end
with type t = T.Svalue.t = struct
  module S = T.Svalue
  module R = S.R

  type t = S.t

  let of_t x = x
  let to_t x = x
  let name = N.name
  let tag (x : t) = x.tag

  let rec sort_of_ty : _ Sv.ty -> sort = function
    | TBool -> SBool
    | TFloat p -> SFloat p
    | TLoc n -> SLoc n
    | TPointer n -> SPtr n
    | TSeq t -> SSeq (sort_of_ty t)
    | TBitVector n -> SBv n
    | TExtension _ -> failwith "extension"

  let rec ty_of_sort : sort -> S.ty = function
    | SBool -> TBool
    | SFloat p -> TFloat p
    | SLoc n -> TLoc n
    | SPtr n -> TPointer n
    | SSeq t -> TSeq (ty_of_sort t)
    | SBv n -> TBitVector n

  let sort_of (x : t) = sort_of_ty x.node.ty
  let pp (x : t) = Fmt.str "%a" S.pp x

  let unop : Sv.Unop.t -> node = function
    | Not -> N_not
    | GetPtrLoc -> N_ptr_loc
    | GetPtrOfs -> N_ptr_ofs
    | BvOfBool n -> N_bv_of_bool n
    | BvOfFloat (rm, s, n) -> N_bv_of_float (rm, s, n)
    | FloatOfBv (rm, s, p) -> N_float_of_bv (rm, s, p)
    | FloatOfBvRaw p -> N_float_of_bv_raw p
    | FloatOfFloat (rm, p) -> N_float_of_float (rm, p)
    | BvExtract (i, j) -> N_extract (i, j)
    | BvExtend (s, k) -> N_extend (s, k)
    | BvNot -> N_bvnot
    | Neg c -> N_neg c
    | FAbs -> N_fabs
    | FNeg -> N_fneg
    | FSqrt -> N_fsqrt
    | FIs fc -> N_fis fc
    | FIsNeg -> N_fisneg
    | FIsPos -> N_fispos
    | FRound rm -> N_fround rm

  let ck (c : Sv.checked) = (c.signed, c.unsigned)

  let binop : Sv.Binop.t -> node = function
    | And -> N_and
    | Or -> N_or
    | Eq -> N_eq
    | FEq -> N_feq
    | FLeq -> N_fleq
    | FLt -> N_flt
    | FAdd -> N_fadd
    | FSub -> N_fsub
    | FMul -> N_fmul
    | FDiv -> N_fdiv
    | FRem -> N_frem
    | FMin -> N_fmin
    | FMax -> N_fmax
    | Add c -> N_add (ck c)
    | Sub c -> N_sub (ck c)
    | Mul c -> N_mul (ck c)
    | Div s -> N_div s
    | Rem s -> N_rem s
    | Mod -> N_mod
    | AddOvf s -> N_addovf s
    | SubOvf s -> N_subovf s
    | MulOvf s -> N_mulovf s
    | Lt s -> N_lt s
    | Leq s -> N_leq s
    | BvConcat -> N_concat
    | BitAnd -> N_bitand
    | BitOr -> N_bitor
    | BitXor -> N_bitxor
    | Shl -> N_shl
    | LShr -> N_lshr
    | AShr -> N_ashr

  let view (x : t) : t view =
    match x.node.kind with
    | Var v -> VVar (V.to_int v, sort_of x)
    | Bool b -> VBool b
    | Float f -> VFloat (Sv.F.precision f, Sv.F.to_z f)
    | Ptr (l, o) -> VPtr (l, o)
    | BitVec z -> (
        match x.node.ty with
        | TBitVector n -> VBv (n, z)
        | TLoc n -> VLoc (n, z)
        | _ -> failwith "bad literal sort")
    | Seq l -> VSeq l
    | Unop (o, a) -> VNode (unop o, [ a ])
    | Binop (o, a, b) -> VNode (binop o, [ a; b ])
    | Triop (Fma, a, b, c) -> VNode (N_fma, [ a; b; c ])
    | Triop (Ite, a, b, c) -> VNode (N_ite, [ a; b; c ])
    | Nop (Distinct, l) -> VNode (N_distinct, l)
    | Exists (bs, b) ->
        VExists (List.map (fun (v, ty) -> (V.to_int v, sort_of_ty ty)) bs, b)
    | Extension _ -> failwith "extension"

  let mk_var i s = S.mk_var (V.of_int i) (ty_of_sort s)
  let mk_bool b = S.Bool.of_bool b
  let mk_bv n z = S.mk_bv n z
  let mk_loc n z = S.Ptr.loc_of_z n z
  let mk_float p z = S.Float.mk_bits p z
  let mk_ptr l o = S.Ptr.mk l o
  let mk_seq s l = S.SSeq.mk ~seq_ty:(ty_of_sort s) l
  let b_and = R.b_and
  let b_or = R.b_or
  let b_not = R.b_not
  let b_ite = R.b_ite
  let sem_eq = R.sem_eq
  let sem_eq_untyped = R.sem_eq_untyped
  let b_distinct = R.b_distinct

  let b_mk_exists bs body =
    R.b_mk_exists (List.map (fun (v, s) -> (V.of_int v, ty_of_sort s)) bs) body

  let c (s, u) : Sv.checked = { signed = s; unsigned = u }
  let bv_add ck = R.bv_add (c ck)
  let bv_sub ck = R.bv_sub (c ck)
  let bv_mul ck = R.bv_mul (c ck)
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
  let bv_extend s k = R.bv_extend s (Z.of_int k)
  let bv_extract i j = R.bv_extract (Z.of_int i) (Z.of_int j)
  let bv_and = R.bv_and
  let bv_or = R.bv_or
  let bv_xor = R.bv_xor
  let bv_shl = R.bv_shl
  let bv_lshr = R.bv_lshr
  let bv_ashr = R.bv_ashr
  let bv_not = R.bv_not
  let bv_of_bool n = R.bv_of_bool (Z.of_int n)
  let bv_to_bool = R.bv_to_bool
  let bv_not_bool = R.bv_not_bool
  let bv_of_float rm s n = R.bv_of_float rm s (Z.of_int n)
  let bv_to_float = R.bv_to_float
  let bv_to_float_raw = R.bv_to_float_raw
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
  let float_abs = R.float_abs
  let float_neg = R.float_neg
  let float_fma = R.float_fma
  let float_fmod_of_rem = R.float_fmod_of_rem
  let float_fmod = R.float_fmod
  let float_min = R.float_min
  let float_max = R.float_max
  let float_sqrt = R.float_sqrt
  let float_round = R.float_round
  let ptr_loc = R.ptr_loc
  let ptr_ofs = R.ptr_ofs
end

(** The old side proper: the public typed API of one instantiation. *)
module Api
    (T : B.Typed.S)
    (N : sig
      val name : string
    end) : Side.SIDE = struct
  module Raw = Raw_of_typed (T) (N)
  include (Raw : Side.BASE with type t = Raw.t)
  open Side

  let t = T.type_
  let u = T.untyped

  let ck (s, un) : T.checked =
    if s && un then T.checked_both
    else if s then T.checked_of_signed true
    else if un then T.checked_of_signed false
    else T.unchecked

  module BV = T.BitVec
  module F = T.Float

  let exists_1 ~not_in s mk =
    let ty = T.type_type (Raw.ty_of_sort s) in
    u (T.exists_1 ~not_in:(t not_in) ty (fun v -> t (mk (u v))))

  let bin f args =
    let a, b = force2 args in
    u (f (t a) (t b))

  let un f args = u (f (t (force1 args)))

  let apply (op : op) (args : Raw.t Lazy.t list) : Raw.t =
    match op with
    | And -> bin T.Infix.( &&@ ) args
    | Or -> bin T.Infix.( ||@ ) args
    | Not -> un T.not args
    | Ite ->
        let a, b, c = force3 args in
        u (T.ite (t a) (t b) (t c))
    | SemEq -> bin T.sem_eq args
    | SemEqUntyped -> bin T.sem_eq_untyped args
    | Distinct -> u (T.distinct (List.map t (force_all args)))
    | AndLazy -> (
        match args with
        | [ a; b ] ->
            let a = Lazy.force a in
            u (T.Bool.and_lazy (t a) (fun () -> t (Lazy.force b)))
        | _ -> invalid_arg "and_lazy")
    | OrLazy -> (
        match args with
        | [ a; b ] ->
            let a = Lazy.force a in
            u (T.Bool.or_lazy (t a) (fun () -> t (Lazy.force b)))
        | _ -> invalid_arg "or_lazy")
    | Conj -> u (T.Bool.conj (List.map t (force_all args)))
    | Exists1 _ -> invalid_arg "Exists1 is built by Build"
    | BvAdd c -> bin (BV.add ~checked:(ck c)) args
    | BvSub c -> bin (BV.sub ~checked:(ck c)) args
    | BvMul c -> bin (BV.mul ~checked:(ck c)) args
    | BvDiv signed -> bin (fun a b -> BV.div ~signed a (BV.cast_nonzero b)) args
    | BvRem signed -> bin (fun a b -> BV.rem ~signed a (BV.cast_nonzero b)) args
    | BvMod -> bin BV.mod_ args
    | BvNeg checked -> un (BV.neg ~checked) args
    | BvAddOvf signed -> bin (BV.add_overflows ~signed) args
    | BvSubOvf signed -> bin (BV.sub_overflows ~signed) args
    | BvMulOvf signed -> bin (BV.mul_overflows ~signed) args
    | BvNegOvf -> un BV.neg_overflows args
    | BvLt signed -> bin (BV.lt ~signed) args
    | BvLeq signed -> bin (BV.leq ~signed) args
    | BvGt signed -> bin (BV.gt ~signed) args
    | BvGeq signed -> bin (BV.geq ~signed) args
    | BvConcat -> bin BV.concat args
    | BvExtend (signed, k) -> un (BV.extend ~signed k) args
    | BvExtract (i, j) -> un (BV.extract i j) args
    | BvAnd -> bin BV.and_ args
    | BvOr -> bin BV.or_ args
    | BvXor -> bin BV.xor args
    | BvShl -> bin BV.shl args
    | BvLShr -> bin BV.lshr args
    | BvAShr -> bin BV.ashr args
    | BvNot -> un BV.not args
    | BvOfBool n -> un (BV.of_bool n) args
    | BvToBool -> un BV.to_bool args
    | BvNotBool -> un BV.not_bool args
    | BvOfFloat (rounding, signed, size) ->
        un (BV.of_float ~rounding ~signed ~size) args
    | BvToFloat (rounding, signed, fp) ->
        un (BV.to_float ~rounding ~signed ~fp) args
    | BvToFloatRaw -> un BV.to_float_raw args
    | FEq -> bin F.eq args
    | FLt -> bin F.lt args
    | FLeq -> bin F.leq args
    | FGt -> bin F.gt args
    | FGeq -> bin F.geq args
    | FAdd -> bin F.add args
    | FSub -> bin F.sub args
    | FMul -> bin F.mul args
    | FDiv -> bin F.div args
    | FRem -> bin F.rem args
    | FFmod -> bin F.fmod args
    | FFmodOfRem ->
        let a, b, c = force3 args in
        u (F.fmod_of_rem (t a) (t b) (t c))
    | FFma ->
        let a, b, c = force3 args in
        u (F.fma (t a) (t b) (t c))
    | FMin -> bin F.min args
    | FMax -> bin F.max args
    | FMinimum -> bin F.minimum args
    | FMaximum -> bin F.maximum args
    | FAbs -> un F.abs args
    | FNeg -> un F.neg args
    | FSqrt -> un F.sqrt args
    | FIsFloatClass fc ->
        un
          (match fc with
          | Normal -> F.is_normal
          | Subnormal -> F.is_subnormal
          | Zero -> F.is_zero
          | Infinite -> F.is_infinite
          | NaN -> F.is_nan)
          args
    | FCast (rounding, fp) -> un (F.cast ~rounding ~fp) args
    | FRound rm -> un (F.round rm) args
    | FIsNegative -> un F.is_negative args
    | FIsPositive -> un F.is_positive args
    | PtrMk -> bin T.Ptr.mk args
    | PtrLoc -> un T.Ptr.loc args
    | PtrOfs -> un T.Ptr.ofs args
    | PtrAddOfs -> bin T.Ptr.add_ofs args
    | PtrNull n -> u (T.Ptr.null n)
    | PtrIsNullLoc -> un T.Ptr.is_null_loc args
    | PtrIsNull -> un T.Ptr.is_null args
    | PtrIsAtNullLoc -> un T.Ptr.is_at_null_loc args
    | SeqMk s ->
        let l = force_all args in
        u (T.SSeq.mk ~seq_ty:(T.type_type (Raw.ty_of_sort s)) (List.map t l))
end

(** The two old-side instantiations: [A] is the reference old side; [B] is a
    separate table, used as a stand-in for the new side until [bv_new] exists
    (old vs old: validates {!Iso}, the generators and {!Side.Compose}). *)
module A_typed = B.Typed.Make (Sv.Dummy_ext) ()

module B_typed = B.Typed.Make (Sv.Dummy_ext) ()
