(** The interface that a simplifier must offer to the harness, and the
    compositions of raw rule functions that the public APIs define on top of
    them.

    - {!BASE}: terms, leaves, and a structural {!Tm.view} (what {!Iso} walks).
    - {!RAW}: the raw rule functions (the generated smart constructors: [b_and],
      [bv_add], ...), as plain functions on terms. The new side provides these
      from [bv_new]; the old side from [Svalue.R].
    - {!SIDE}: what {!Build} needs: [apply] one public entry point.

    The old side implements {!SIDE} directly through the public typed API
    ({!Old_side}); the new side implements it with {!Compose}, written once here
    after the OCaml of the old public API (soteria/lib/bv_values/svalue.ml and
    typed.ml). *)

open Tm

module type BASE = sig
  type t

  val name : string
  val tag : t -> int
  val view : t -> t view
  val sort_of : t -> sort
  val pp : t -> string

  (** {2 Leaves and raw (non-simplifying) constructors} *)

  val mk_var : int -> sort -> t
  val mk_bool : bool -> t
  val mk_bv : int -> Z.t -> t
  val mk_loc : int -> Z.t -> t

  (* from the IEEE bits *)
  val mk_float : prec -> Z.t -> t
  val mk_ptr : t -> t -> t

  (* from the sequence sort *)
  val mk_seq : sort -> t list -> t
end

module type RAW = sig
  include BASE

  val b_and : t -> t -> t
  val b_or : t -> t -> t
  val b_not : t -> t
  val b_ite : t -> t -> t -> t
  val sem_eq : t -> t -> t
  val sem_eq_untyped : t -> t -> t
  val b_distinct : t list -> t
  val b_mk_exists : (int * sort) list -> t -> t
  val bv_add : checked -> t -> t -> t
  val bv_sub : checked -> t -> t -> t
  val bv_mul : checked -> t -> t -> t
  val bv_div : bool -> t -> t -> t
  val bv_rem : bool -> t -> t -> t
  val bv_mod : t -> t -> t
  val bv_neg : bool -> t -> t
  val bv_add_overflows : bool -> t -> t -> t
  val bv_sub_overflows : bool -> t -> t -> t
  val bv_mul_overflows : bool -> t -> t -> t
  val bv_neg_overflows : t -> t
  val bv_lt : bool -> t -> t -> t
  val bv_leq : bool -> t -> t -> t
  val bv_concat : t -> t -> t
  val bv_extend : bool -> int -> t -> t
  val bv_extract : int -> int -> t -> t
  val bv_and : t -> t -> t
  val bv_or : t -> t -> t
  val bv_xor : t -> t -> t
  val bv_shl : t -> t -> t
  val bv_lshr : t -> t -> t
  val bv_ashr : t -> t -> t
  val bv_not : t -> t
  val bv_of_bool : int -> t -> t
  val bv_to_bool : t -> t
  val bv_not_bool : t -> t
  val bv_of_float : RM.t -> bool -> int -> t -> t
  val bv_to_float : RM.t -> bool -> prec -> t -> t
  val bv_to_float_raw : t -> t
  val float_is_floatclass : FC.t -> t -> t
  val float_is_negative : t -> t
  val float_is_positive : t -> t
  val float_cast : RM.t -> prec -> t -> t
  val float_eq : t -> t -> t
  val float_lt : t -> t -> t
  val float_leq : t -> t -> t
  val float_add : t -> t -> t
  val float_sub : t -> t -> t
  val float_div : t -> t -> t
  val float_mul : t -> t -> t
  val float_rem : t -> t -> t
  val float_abs : t -> t
  val float_neg : t -> t
  val float_fma : t -> t -> t -> t
  val float_fmod_of_rem : t -> t -> t -> t
  val float_fmod : t -> t -> t
  val float_min : t -> t -> t
  val float_max : t -> t -> t
  val float_sqrt : t -> t
  val float_round : RM.t -> t -> t
  val ptr_loc : t -> t
  val ptr_ofs : t -> t
end

module type SIDE = sig
  include BASE

  (** One public entry point on its (lazily built) arguments. Strict operators
      force their arguments left to right. *)
  val apply : op -> t Lazy.t list -> t

  val exists_1 : not_in:t -> sort -> (t -> t) -> t
end

(** Free variables (the ids of the variables that are not bound) of a term,
    through the view; the same traversal as [Svalue.iter_vars]. *)
let max_free_var (type a) (module B : BASE with type t = a) (x : a) : int =
  let m = ref 0 in
  let module S = Set.Make (Int) in
  let rec go ignore (x : a) =
    match B.view x with
    | VVar (i, _) -> if not (S.mem i ignore) then m := max !m i
    | VBool _ | VBv _ | VLoc _ | VFloat _ -> ()
    | VPtr (a, b) ->
        go ignore a;
        go ignore b
    | VNode (_, l) | VSeq l -> List.iter (go ignore) l
    | VExists (vs, b) ->
        go (List.fold_left (fun s (v, _) -> S.add v s) ignore vs) b
  in
  go S.empty x;
  !m

let force1 = function [ a ] -> Lazy.force a | _ -> invalid_arg "arity 1"

let force2 = function
  | [ a; b ] ->
      let a = Lazy.force a in
      let b = Lazy.force b in
      (a, b)
  | _ -> invalid_arg "arity 2"

let force3 = function
  | [ a; b; c ] ->
      let a = Lazy.force a in
      let b = Lazy.force b in
      let c = Lazy.force c in
      (a, b, c)
  | _ -> invalid_arg "arity 3"

let force_all l =
  (* [List.map] evaluates in an unspecified order for the stdlib: do it by
     hand *)
  let rec go = function
    | [] -> []
    | x :: r ->
        let x = Lazy.force x in
        x :: go r
  in
  go l

(** The compositions of the public API on top of the raw rules. Each is the
    transcription of the corresponding OCaml in svalue.ml / typed.ml, with the
    evaluation order of the original (OCaml evaluates the arguments of a call
    right to left, which fixes the order in which intermediate nodes, hence
    tags, are created). *)
module Compose (R : RAW) : SIDE with type t = R.t = struct
  include (R : BASE with type t = R.t)

  let fp_of x =
    match R.sort_of x with SFloat p -> p | _ -> failwith "fp_of: not a float"

  let size_of x =
    match R.sort_of x with
    | SBv n | SLoc n | SPtr n -> n
    | _ -> failwith "size_of: not a bit value"

  (* [Float.nan fp = mk_raw fp (F.nan fp)] *)
  let float_nan fp =
    R.mk_float fp
      (Soteria.Bv_values.Svalue.F.to_z (Soteria.Bv_values.Svalue.F.nan fp))

  (* Svalue.Bool.and_lazy / or_lazy *)
  let and_lazy v1 f =
    match R.view v1 with
    | VBool false -> R.mk_bool false
    | _ -> R.b_and v1 (f ())

  let or_lazy v1 f =
    match R.view v1 with VBool true -> R.mk_bool true | _ -> R.b_or v1 (f ())

  (* Svalue.Bool.conj *)
  let conj l = List.fold_left R.b_and (R.mk_bool true) l

  (* Svalue.Float.minimum, with [Bool.ite c x @@ rest] = [ite c x rest]: the
     arguments of [ite] are evaluated right to left. *)
  let minimum v1 v2 =
    let c4 = R.float_is_negative v1 in
    let r3 = R.b_ite c4 v1 v2 in
    let c3 = R.float_lt v2 v1 in
    let r2 = R.b_ite c3 v2 r3 in
    let c2 = R.float_lt v1 v2 in
    let r1 = R.b_ite c2 v1 r2 in
    let n = float_nan (fp_of v1) in
    let nan2 = R.float_is_floatclass FC.NaN v2 in
    let nan1 = R.float_is_floatclass FC.NaN v1 in
    let c1 = R.b_or nan1 nan2 in
    R.b_ite c1 n r1

  (* Svalue.Float.maximum *)
  let maximum v1 v2 =
    let c4 = R.float_is_negative v1 in
    let r3 = R.b_ite c4 v2 v1 in
    let c3 = R.float_lt v2 v1 in
    let r2 = R.b_ite c3 v1 r3 in
    let c2 = R.float_lt v1 v2 in
    let r1 = R.b_ite c2 v2 r2 in
    let n = float_nan (fp_of v1) in
    let nan2 = R.float_is_floatclass FC.NaN v2 in
    let nan1 = R.float_is_floatclass FC.NaN v1 in
    let c1 = R.b_or nan1 nan2 in
    R.b_ite c1 n r1

  (* Svalue.Ptr.decompose / add_ofs; [(loc p, ofs p)] is evaluated right to
     left *)
  let decompose p =
    match R.view p with
    | VPtr (l, o) -> (l, o)
    | _ ->
        let o = R.ptr_ofs p in
        let l = R.ptr_loc p in
        (l, o)

  let add_ofs p o =
    let loc, ofs = decompose p in
    let s = R.bv_add (false, false) ofs o in
    R.mk_ptr loc s

  let null_loc n = R.mk_loc n Z.zero

  let null n =
    let z = R.mk_bv n Z.zero in
    let l = null_loc n in
    R.mk_ptr l z

  let is_null_loc l =
    let n = null_loc (size_of l) in
    R.sem_eq l n

  let is_null p =
    let n = null (size_of p) in
    R.sem_eq p n

  let exists_1 ~not_in ty mk =
    (* Svalue.Bool.exists_n for one binder *)
    let base = max_free_var (module R) not_in + 10_000 in
    let v = R.mk_var base ty in
    let body = mk v in
    R.b_mk_exists [ (base, ty) ] body

  let apply (op : op) (args : t Lazy.t list) : t =
    match op with
    | And ->
        let a, b = force2 args in
        R.b_and a b
    | Or ->
        let a, b = force2 args in
        R.b_or a b
    | Not -> R.b_not (force1 args)
    | Ite ->
        let a, b, c = force3 args in
        R.b_ite a b c
    | SemEq ->
        let a, b = force2 args in
        R.sem_eq a b
    | SemEqUntyped ->
        let a, b = force2 args in
        R.sem_eq_untyped a b
    | Distinct -> R.b_distinct (force_all args)
    | AndLazy -> (
        match args with
        | [ a; b ] ->
            let a = Lazy.force a in
            and_lazy a (fun () -> Lazy.force b)
        | _ -> invalid_arg "and_lazy")
    | OrLazy -> (
        match args with
        | [ a; b ] ->
            let a = Lazy.force a in
            or_lazy a (fun () -> Lazy.force b)
        | _ -> invalid_arg "or_lazy")
    | Conj -> conj (force_all args)
    | Exists1 _ -> invalid_arg "Exists1 is built by Build"
    | BvAdd c ->
        let a, b = force2 args in
        R.bv_add c a b
    | BvSub c ->
        let a, b = force2 args in
        R.bv_sub c a b
    | BvMul c ->
        let a, b = force2 args in
        R.bv_mul c a b
    | BvDiv s ->
        let a, b = force2 args in
        R.bv_div s a b
    | BvRem s ->
        let a, b = force2 args in
        R.bv_rem s a b
    | BvMod ->
        let a, b = force2 args in
        R.bv_mod a b
    | BvNeg c -> R.bv_neg c (force1 args)
    | BvAddOvf s ->
        let a, b = force2 args in
        R.bv_add_overflows s a b
    | BvSubOvf s ->
        let a, b = force2 args in
        R.bv_sub_overflows s a b
    | BvMulOvf s ->
        let a, b = force2 args in
        R.bv_mul_overflows s a b
    | BvNegOvf -> R.bv_neg_overflows (force1 args)
    | BvLt s ->
        let a, b = force2 args in
        R.bv_lt s a b
    | BvLeq s ->
        let a, b = force2 args in
        R.bv_leq s a b
    | BvGt s ->
        (* BitVec.gt ~signed a b = lt ~signed b a *)
        let a, b = force2 args in
        R.bv_lt s b a
    | BvGeq s ->
        let a, b = force2 args in
        R.bv_leq s b a
    | BvConcat ->
        let a, b = force2 args in
        R.bv_concat a b
    | BvExtend (s, k) -> R.bv_extend s k (force1 args)
    | BvExtract (i, j) -> R.bv_extract i j (force1 args)
    | BvAnd ->
        let a, b = force2 args in
        R.bv_and a b
    | BvOr ->
        let a, b = force2 args in
        R.bv_or a b
    | BvXor ->
        let a, b = force2 args in
        R.bv_xor a b
    | BvShl ->
        let a, b = force2 args in
        R.bv_shl a b
    | BvLShr ->
        let a, b = force2 args in
        R.bv_lshr a b
    | BvAShr ->
        let a, b = force2 args in
        R.bv_ashr a b
    | BvNot -> R.bv_not (force1 args)
    | BvOfBool n -> R.bv_of_bool n (force1 args)
    | BvToBool -> R.bv_to_bool (force1 args)
    | BvNotBool -> R.bv_not_bool (force1 args)
    | BvOfFloat (rm, s, n) -> R.bv_of_float rm s n (force1 args)
    | BvToFloat (rm, s, p) -> R.bv_to_float rm s p (force1 args)
    | BvToFloatRaw -> R.bv_to_float_raw (force1 args)
    | FEq ->
        let a, b = force2 args in
        R.float_eq a b
    | FLt ->
        let a, b = force2 args in
        R.float_lt a b
    | FLeq ->
        let a, b = force2 args in
        R.float_leq a b
    | FGt ->
        let a, b = force2 args in
        R.float_lt b a
    | FGeq ->
        let a, b = force2 args in
        R.float_leq b a
    | FAdd ->
        let a, b = force2 args in
        R.float_add a b
    | FSub ->
        let a, b = force2 args in
        R.float_sub a b
    | FMul ->
        let a, b = force2 args in
        R.float_mul a b
    | FDiv ->
        let a, b = force2 args in
        R.float_div a b
    | FRem ->
        let a, b = force2 args in
        R.float_rem a b
    | FFmod ->
        let a, b = force2 args in
        R.float_fmod a b
    | FFmodOfRem ->
        let a, b, c = force3 args in
        R.float_fmod_of_rem a b c
    | FFma ->
        let a, b, c = force3 args in
        R.float_fma a b c
    | FMin ->
        let a, b = force2 args in
        R.float_min a b
    | FMax ->
        let a, b = force2 args in
        R.float_max a b
    | FMinimum ->
        let a, b = force2 args in
        minimum a b
    | FMaximum ->
        let a, b = force2 args in
        maximum a b
    | FAbs -> R.float_abs (force1 args)
    | FNeg -> R.float_neg (force1 args)
    | FSqrt -> R.float_sqrt (force1 args)
    | FIsFloatClass fc -> R.float_is_floatclass fc (force1 args)
    | FCast (rm, p) -> R.float_cast rm p (force1 args)
    | FRound rm -> R.float_round rm (force1 args)
    | FIsNegative -> R.float_is_negative (force1 args)
    | FIsPositive -> R.float_is_positive (force1 args)
    | PtrMk ->
        let a, b = force2 args in
        R.mk_ptr a b
    | PtrLoc -> R.ptr_loc (force1 args)
    | PtrOfs -> R.ptr_ofs (force1 args)
    | PtrAddOfs ->
        let a, b = force2 args in
        add_ofs a b
    | PtrNull n -> null n
    | PtrIsNullLoc -> is_null_loc (force1 args)
    | PtrIsNull -> is_null (force1 args)
    | PtrIsAtNullLoc ->
        (* is_at_null_loc p = is_null_loc (loc p) *)
        is_null_loc (R.ptr_loc (force1 args))
    | SeqMk s -> R.mk_seq s (force_all args)
end

(** The term-level builder shared by both sides: replays a [Tm.t] depth-first,
    left to right. *)
module Build (S : SIDE) = struct
  let rec build (env : S.t list) (tm : Tm.t) : S.t =
    match tm with
    | Var (i, s) -> S.mk_var i s
    | Bool b -> S.mk_bool b
    | Bv (n, z) -> S.mk_bv n z
    | Loc (n, z) -> S.mk_loc n z
    | Float (p, z) -> S.mk_float p z
    | Bound (i, _) -> List.nth env i
    | Op (Exists1 s, [ not_in; body ]) ->
        let not_in = build env not_in in
        S.exists_1 ~not_in s (fun v -> build (env @ [ v ]) body)
    | Op (Exists1 _, _) -> invalid_arg "Exists1 arity"
    | Op (op, args) -> S.apply op (List.map (fun a -> lazy (build env a)) args)

  let build tm = build [] tm
end
