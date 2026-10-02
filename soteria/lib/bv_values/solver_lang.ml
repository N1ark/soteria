(** What a symbolic value language must provide for {!Bv_solver}, {!Analyses}
    and {!Encoding}. The solver layer treats [t] and [ty] as abstract: it never
    inspects a node, a kind or a sort, it only calls the functions below.

    All functions are pure, except the [encode_*] ones, which may perform
    {!Solvers.Decls.Declare}. *)
module type S = sig
  type t
  type ty

  (** {2 Identity, hashing, printing} *)

  (** Equality of values; O(1) for hash-consed values. *)
  val equal : t -> t -> bool

  (** Unique id (the hash-consing tag); the key of the Patricia maps of the
      analyses. *)
  val unique_tag : t -> int

  (** Hash tables keyed on values: memo of SMT encodings and of sat checks. *)
  module Hashtbl : Stdlib.Hashtbl.S with type key = t

  val pp : t Fmt.t

  (** {2 Constructors}

      All of them go through the simplifying smart constructors. *)

  val v_true : t
  val v_false : t
  val of_bool : bool -> t
  val not_ : t -> t
  val and_ : t -> t -> t
  val or_ : t -> t -> t

  (** Boolean-guarded [ite]. *)
  val ite : t -> t -> t -> t

  (** Semantic equality, [==@]. *)
  val sem_eq : t -> t -> t

  val mk_var : Symex.Var.t -> ty -> t

  (** The type of [n]-bit bit-vectors. *)
  val t_bv : int -> ty

  (** [bv_mk n z] is the [n]-bit bit-vector literal [z]. *)
  val bv_mk : int -> Z.t -> t

  (** Unsigned [<=] on bit-vectors, [<=@]. *)
  val bv_uleq : t -> t -> t

  (** {2 Recognisers}

      Each returns the parts of a value of the given shape, and [None] for any
      other value. *)

  (** A constant that needs no further simplification: a boolean, bit-vector or
      float literal (not a pointer or a sequence). *)
  val is_literal : t -> bool

  (** Whether the value has the boolean type. *)
  val is_bool : t -> bool

  (** [Some (x, ty)] iff the value is the variable [x] of type [ty]. *)
  val as_var : t -> (Symex.Var.t * ty) option

  (** [Some n] iff [ty] is exactly the type of [n]-bit bit-vectors (not
      locations or pointers). *)
  val as_bv_ty : ty -> int option

  val as_not : t -> t option
  val as_eq : t -> (t * t) option
  val as_and : t -> (t * t) option
  val as_or : t -> (t * t) option
  val as_ite : t -> (t * t * t) option

  (** A strict comparison, whatever its signedness. *)
  val as_lt : t -> (t * t) option

  (** A non-strict comparison, whatever its signedness. *)
  val as_leq : t -> (t * t) option

  (** [Some l] iff the value is a [distinct] of the (possibly empty) list [l].
  *)
  val as_distinct : t -> t list option

  (** [A && B && C] iterates over [A], [B], [C], left to right, flattening
      nested conjunctions only. *)
  val split_ands : t -> t Iter.t

  (** Syntactic disequality that is certain: different types, or distinct
      literals. *)
  val sure_neq : t -> t -> bool

  (** [implies_or_contradicts ~q ~neg_q pc] is [Some true] if the path condition
      conjunct [pc] implies [q], [Some false] if it implies [neg_q], and [None]
      otherwise. [neg_q] must be [not_ q]. This runs for every slot of the path
      condition, on every simplified value: it must not allocate on the [None]
      path. *)
  val implies_or_contradicts : q:t -> neg_q:t -> t -> bool option

  (** {2 Interval analysis} *)

  type sign = Pos | Neg

  (** [as_range v = Some (x, size, (sign, (lo, hi)))] iff [v] states that the
      [size]-bit variable [x] is inside ([Pos]) or outside ([Neg]) the inclusive
      range [[lo, hi]]. *)
  val as_range : t -> (Symex.Var.t * int * (sign * (Z.t * Z.t))) option

  (** {2 Rewriting} *)

  (** Normalises a value bottom-up through the smart constructors, replacing
      variables with [eval_var]. If evaluation fails (e.g. a division by zero),
      returns the original value. With [force], evaluation proceeds even if no
      sub-value changed. *)
  val eval : ?force:bool -> ?eval_var:(t -> Symex.Var.t -> ty -> t) -> t -> t

  (** If the value is a unary or binary operation, applies [f] to its operands,
      left to right, and rebuilds it with the same operator through the smart
      constructors; returns the value itself if no operand changed. Any other
      value is returned unchanged, without calling [f]. *)
  val map_operands : (t -> t) -> t -> t

  (** {2 Variables} *)

  (** Iterates over the free variables of a value, with their types. *)
  val iter_vars : t -> (Symex.Var.t * ty -> unit) -> unit

  (** {2 Cost model} *)

  (** Estimated cost of bit-blasting the value: one unit is roughly a thousand
      bytes of Z3's encoding. Not memoised. *)
  val cost : t -> int

  (** {2 Model search} *)

  (** [random_value ty] is a generator of random values of type [ty], if there
      is one. *)
  val random_value : ty -> (unit -> t) option

  (** {2 SMT encoding} *)

  (** Encodes a type, given the (recursive) encoder of nested types. *)
  val encode_ty : sort_of_ty:(ty -> Smt.sexp) -> ty -> Smt.sexp

  (** Encodes one value, given the encoder of nested types and the (memoised)
      encoder of its children. The order in which [encode_child] is called
      determines the order of the emitted declarations. *)
  val encode_node :
    sort_of_ty:(ty -> Smt.sexp) -> encode_child:(t -> Smt.sexp) -> t -> Smt.sexp
end

module Make
    (Ext : Svalue.Value_ext)
    (V :
      module type of Svalue.Make (Ext) ())
        (Eval : module type of Eval.Make (Ext) (V)) :
      S with type t = V.t and type ty = V.ty =
    struct
  open Logs.Import
  open Soteria_std
  open Svalue

  type t = V.t
  type ty = V.ty

  module Enc = struct
    open Smt
    open Svalue

    let encode_ty ~(sort_of_ty : V.ty -> sexp) : V.ty -> sexp = function
      | TBool -> t_bool
      | TLoc n -> t_bits n
      | TFloat F16 -> t_f16
      | TFloat F32 -> t_f32
      | TFloat F64 -> t_f64
      | TFloat F128 -> t_f128
      | TSeq ty -> t_seq (sort_of_ty ty)
      | TPointer n -> Ptr_sort.sort n
      | TBitVector n -> t_bits n
      | TExtension x -> V.Ext.encode_ty sort_of_ty x

    let rm_to_smt : RoundingMode.t -> Smt.RoundingMode.t = function
      | NearestTiesToEven -> NearestTiesToEven
      | NearestTiesToAway -> NearestTiesToAway
      | Ceil -> Ceil
      | Floor -> Floor
      | Truncate -> Truncate

    let smt_of_unop ~ty : Unop.t -> sexp -> sexp = function
      | Not -> bool_not
      | FAbs -> fp_abs
      | FNeg -> fp_neg
      | FSqrt -> fp_sqrt
      | GetPtrLoc -> Ptr_sort.get_loc (V.size_of ty)
      | GetPtrOfs -> Ptr_sort.get_ofs (V.size_of ty)
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
      | FIs fc -> fp_is (FloatClass.as_fpclass fc)
      | FIsNeg -> fp_is_negative
      | FIsPos -> fp_is_positive
      | FRound rm -> fp_round (rm_to_smt rm)

    let smt_of_binop : Binop.t -> sexp -> sexp -> sexp = function
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

    let smt_of_triop : Triop.t -> sexp -> sexp -> sexp -> sexp = function
      | Fma -> fp_fma
      | Ite -> ite

    let encode_var v = atom (Var.to_string v)

    let encode_node ~(sort_of_ty : V.ty -> sexp) ~(encode_child : V.t -> sexp)
        (v : V.t) =
      match v.node.kind with
      | Var v -> encode_var v
      | Float f ->
          let size = FloatPrecision.size (V.precision_of_f v.node.ty) in
          float_of_bv size (bv_k size (Floatml.AnyFloat.to_z f))
      | Bool b -> bool_k b
      | BitVec z ->
          let n = V.size_of v.node.ty in
          bv_k n z
      | Ptr (l, o) ->
          Ptr_sort.mk_ptr (V.size_of v.node.ty) (encode_child l)
            (encode_child o)
      | Seq vs -> (
          match vs with
          | [] -> L.failwith "need type to encode empty lists"
          | _ :: _ ->
              List.map (fun v -> seq_singl (encode_child v)) vs |> seq_concat)
      | Exists (vs, sv) ->
          let encode_binder (v, ty) = list [ encode_var v; sort_of_ty ty ] in
          exists (List.map encode_binder vs) (encode_child sv)
      | Unop (unop, v1) ->
          let e1 = encode_child v1 in
          smt_of_unop ~ty:v1.node.ty unop e1
      | Binop (binop, v1, v2) ->
          let v1 = encode_child v1 in
          let v2 = encode_child v2 in
          smt_of_binop binop v1 v2
      | Triop (op, v1, v2, v3) ->
          smt_of_triop op (encode_child v1) (encode_child v2) (encode_child v3)
      | Nop (Distinct, vs) ->
          let vs = List.map encode_child vs in
          distinct vs
      | Extension x ->
          V.Ext.encode_value sort_of_ty encode_child ~ty:v.node.ty x
  end

  module Range = struct
    (* we only include stuff from Z we want *)
    open struct
      let one = Z.one
      let ( - ) = Z.sub
      let ( + ) = Z.add
      let ( < ) = Z.lt
      let ( <= ) = Z.leq
      let pow2 n = Z.shift_left Z.one n
      let ( ~- ) size x = pow2 size - x

      (** [to_bv size x] if [x < 0], returns the corresponding unsigned
          bitvector representation of [x] with size [size]. E.g. for [size = 8],
          [-1] would be represented as [255]. *)
      let to_bv n x = Z.(x land pred (one lsl n))
    end

    type sign = Pos | Neg

    let rec as_range (v : V.t) =
      (* For the inequalities, see https://ceur-ws.org/Vol-1617/paper8.pdf *)
      match v.node.kind with
      (*
       *  Case 2: c1 <=u c2 + x
       *  • c1 < c2 => ~[ -c2; c1 - c2 - 1 ]
       *  • c1 >= c2 => [ c1 - c2; -c2 - 1 ]
       *)
      | Binop
          ( ((Lt false | Leq false) as bop),
            { node = { kind = BitVec c1; ty = TBitVector size }; _ },
            {
              node =
                {
                  kind =
                    ( Var v
                    | Binop
                        ( Add _,
                          { node = { kind = Var v; _ }; _ },
                          { node = { kind = BitVec _; _ }; _ } )
                    | Binop
                        ( Add _,
                          { node = { kind = BitVec _; _ }; _ },
                          { node = { kind = Var v; _ }; _ } ) ) as rhs;
                  _;
                };
              _;
            } ) ->
          let c1 = if bop = Lt false then Z.succ c1 else c1 in
          let c2 =
            match rhs with
            | Var _ -> Z.zero
            | Binop (Add _, { node = { kind = BitVec c2; _ }; _ }, _)
            | Binop (Add _, _, { node = { kind = BitVec c2; _ }; _ }) ->
                c2
            | _ -> L.failwith "unreachable"
          in
          (* We need to be careful and use [to_bv] to ensure we don't end up
             with ranges with negative number (BAD!) *)
          if c1 < c2 then
            Some (v, size, (Neg, (~-size c2, to_bv size (c1 - c2 - one))))
          else Some (v, size, (Pos, (c1 - c2, to_bv size (~-size c2 - one))))
      (*
       *  Case 3: c1 + x <=u c2
       *  • c1 <= c2 => ~[ c2 - c1 + 1; -c1 - 1 ]
       *  • c1 > c2 => [ -c1; -c1 + c2 ]
       *)
      | Binop
          ( ((Lt false | Leq false) as bop),
            {
              node =
                {
                  kind =
                    ( Var v
                    | Binop
                        ( Add _,
                          { node = { kind = Var v; _ }; _ },
                          { node = { kind = BitVec _; _ }; _ } )
                    | Binop
                        ( Add _,
                          { node = { kind = BitVec _; _ }; _ },
                          { node = { kind = Var v; _ }; _ } ) ) as lhs;
                  _;
                };
              _;
            },
            { node = { kind = BitVec c2; ty = TBitVector size }; _ } ) ->
          let c1 =
            match lhs with
            | Var _ -> Z.zero
            | Binop (Add _, { node = { kind = BitVec c1; _ }; _ }, _)
            | Binop (Add _, _, { node = { kind = BitVec c1; _ }; _ }) ->
                c1
            | _ -> L.failwith "unreachable"
          in
          let c2 = if bop = Lt false then Z.pred c2 else c2 in
          if c1 <= c2 then Some (v, size, (Neg, (c2 - c1 + one, ~-size one)))
          else Some (v, size, (Pos, (~-size c1, ~-size c1 + c2)))
      (*
       *  Case 4: x <=s c1
       *  • c1 < 2^{n-1} => ~[ c1 + 1; 2^{n-1} - 1 ]
       *  • c1 >= 2^{n-1} => [ 2^{n-1}; c1 ]
       *)
      | Binop
          ( ((Lt true | Leq true) as binop),
            { node = { kind = Var v; _ }; _ },
            { node = { kind = BitVec c1; ty = TBitVector size }; _ } ) ->
          let c1 = if binop = Lt true then Z.pred c1 else c1 in
          let mid = pow2 Stdlib.(size - 1) in
          if c1 < mid then Some (v, size, (Neg, (c1 + one, mid - one)))
          else Some (v, size, (Pos, (mid, c1)))
      (*
       *  Case 5: c1 <=s x
       *  • c1 < 2^{n-1} => [ c1; 2^{n-1} - 1 ]
       *  • c1 >= 2^{n-1} => ~[ 2^{n-1}; c1 - 1 ]
       *)
      | Binop
          ( ((Lt true | Leq true) as binop),
            { node = { kind = BitVec c1; ty = TBitVector size }; _ },
            { node = { kind = Var v; _ }; _ } ) ->
          let c1 = if binop = Lt true then Z.succ c1 else c1 in
          let mid = Z.shift_left Z.one Stdlib.(size - 1) in

          if c1 < mid then Some (v, size, (Pos, (c1, mid - one)))
          else Some (v, size, (Neg, (mid, c1 - one)))
      (* Simple equality *)
      | Binop
          ( Eq,
            { node = { kind = BitVec x; ty = TBitVector size }; _ },
            { node = { kind = Var v; _ }; _ } )
      | Binop
          ( Eq,
            { node = { kind = Var v; _ }; _ },
            { node = { kind = BitVec x; ty = TBitVector size }; _ } ) ->
          Some (v, size, (Pos, (x, x)))
      (* This only works for a single fact; we can't apply this to [!(A && B)],
         since that's a disjunction! *)
      | Unop (Not, v) ->
          Option.map
            (fun (v1, size, (sign, range)) ->
              (v1, size, ((if sign = Neg then Pos else Neg), range)))
            (as_range v)
      | _ -> None
  end

  let equal = V.equal
  let unique_tag = V.unique_tag

  module Hashtbl = V.Hashtbl

  let pp = V.pp
  let v_true = V.Bool.v_true
  let v_false = V.Bool.v_false
  let of_bool = V.Bool.of_bool
  let not_ = V.Bool.not
  let and_ = V.Bool.and_
  let or_ = V.Bool.or_
  let ite = V.Bool.ite
  let sem_eq = V.Bool.sem_eq
  let mk_var = V.mk_var
  let t_bv = V.t_bv
  let bv_mk = V.BitVec.mk
  let bv_uleq = V.BitVec.leq ~signed:false

  let is_literal (v : V.t) =
    match v.node.kind with Bool _ | BitVec _ | Float _ -> true | _ -> false

  let is_bool (v : V.t) = match v.node.ty with TBool -> true | _ -> false

  let as_var (v : V.t) =
    match v.node.kind with Var x -> Some (x, v.node.ty) | _ -> None

  let as_bv_ty : V.ty -> int option = function
    | TBitVector n -> Some n
    | _ -> None

  let as_not (v : V.t) =
    match v.node.kind with Unop (Not, x) -> Some x | _ -> None

  let as_eq (v : V.t) =
    match v.node.kind with Binop (Eq, l, r) -> Some (l, r) | _ -> None

  let as_and (v : V.t) =
    match v.node.kind with Binop (And, l, r) -> Some (l, r) | _ -> None

  let as_or (v : V.t) =
    match v.node.kind with Binop (Or, l, r) -> Some (l, r) | _ -> None

  let as_ite (v : V.t) =
    match v.node.kind with Triop (Ite, g, t, e) -> Some (g, t, e) | _ -> None

  let as_lt (v : V.t) =
    match v.node.kind with Binop (Lt _, l, r) -> Some (l, r) | _ -> None

  let as_leq (v : V.t) =
    match v.node.kind with Binop (Leq _, l, r) -> Some (l, r) | _ -> None

  let as_distinct (v : V.t) =
    match v.node.kind with Nop (Distinct, l) -> Some l | _ -> None

  let split_ands = V.Bool.split_ands
  let sure_neq = V.sure_neq

  let[@inline] implies_or_contradicts ~(q : V.t) ~(neg_q : V.t) (pc : V.t) :
      bool option =
    if equal q pc then Some true
    else if equal neg_q pc then Some false
    else
      match (q.node.kind, pc.node.kind) with
      (* [a < b] in PC implies [a <= b] *)
      | Binop (Leq qs, qa, qb), Binop (Lt ps, pa, pb)
        when qs = ps && equal qa pa && equal qb pb ->
          Some true
      (* [a < b] in PC implies ~[b <= a] and ~[b < a] *)
      | Binop ((Lt qs | Leq qs), qa, qb), Binop (Lt ps, pa, pb)
        when qs = ps && equal qa pb && equal qb pa ->
          Some false
      (* [a <= b] in PC implies ~[b < a] *)
      | Binop (Lt qs, qa, qb), Binop (Leq ps, pa, pb)
        when qs = ps && equal qa pb && equal qb pa ->
          Some false
      (* [a < b] (either direction) in PC implies ~[a = b] *)
      | Binop (Eq, qa, qb), Binop (Lt _, pa, pb)
        when (equal qa pa && equal qb pb) || (equal qa pb && equal qb pa) ->
          Some false
      (* [a < b] (either direction) in PC implies [~(a = b)] *)
      | ( Unop (Not, { node = { kind = Binop (Eq, qa, qb); _ }; _ }),
          Binop (Lt _, pa, pb) )
        when (equal qa pa && equal qb pb) || (equal qa pb && equal qb pa) ->
          Some true
      | _ -> None

  type sign = Range.sign = Pos | Neg

  let as_range = Range.as_range
  let eval = Eval.eval

  let map_operands f (v : V.t) =
    match v.node.kind with
    | Binop (op, l, r) ->
        let l' = f l in
        let r' = f r in
        if equal l l' && equal r r' then v else Eval.eval_binop op l' r'
    | Unop (op, x) ->
        let x' = f x in
        if equal x x' then v else Eval.eval_unop op x'
    | _ -> v

  let iter_vars = V.iter_vars

  (** One unit is roughly a thousand bytes of Z3's bit-blasted encoding of the
      operator, measured at 32 bits with
      [(then simplify fpa2bv simplify bit-blast)] *)
  let rec cost (v : V.t) : int =
    match v.node.kind with
    | Binop (op, l, r) -> cost_binop op + cost l + cost r
    | Unop (op, v) -> cost_unop op + cost v
    | Triop (op, a, b, c) -> cost_triop op + cost a + cost b + cost c
    | Nop (_, vs) -> costs vs
    | Var _ -> 3
    | Float _ -> 2
    | Seq vs -> costs vs
    | Exists (_, sv) ->
        (* quantifiers escape the bit-blasting the costs below measure, so they
           outrank every operator *)
        cost sv + 100_000
    | Ptr _ | Bool _ | BitVec _ -> 1
    (* TODO: cost for extensions *)
    | Extension _ -> 100_000

  and costs vs = List.fold_left (fun acc v -> acc + cost v) 0 vs
  and cost_triop : Triop.t -> int = function Fma -> 400 | Ite -> 0

  and cost_binop : Binop.t -> int = function
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

  and cost_unop : Unop.t -> int = function
    | BvOfFloat _ -> 1400
    | FSqrt -> 280
    | FloatOfFloat _ -> 255
    | FloatOfBv _ -> 78
    | FRound _ -> 65
    | Neg _ -> 10
    | FAbs | FNeg | FloatOfBvRaw _ -> 4
    | Not | GetPtrLoc | GetPtrOfs | BvNot | BvOfBool _ | BvExtend _
    | BvExtract _ | FIs _ | FIsNeg | FIsPos ->
        1

  let random_value : V.ty -> (unit -> V.t) option = function
    | TLoc n ->
        let max = Z.(shift_left one n) in
        Some (fun () -> V.Ptr.loc_of_z n (Z.random_int max))
    | TBitVector n ->
        let max = Z.(shift_left one n) in
        Some (fun () -> V.BitVec.mk n (Z.random_int max))
    | TBool -> Some (fun () -> V.Bool.of_bool (Random.bool ()))
    | TFloat p ->
        let max = Z.(shift_left one (FloatPrecision.size p)) in
        Some (fun () -> V.Float.mk_bits p (Z.random_int max))
    (* TODO: figure this out *)
    | TPointer _ | TSeq _ | TExtension _ -> None

  let encode_ty = Enc.encode_ty
  let encode_node = Enc.encode_node
end
