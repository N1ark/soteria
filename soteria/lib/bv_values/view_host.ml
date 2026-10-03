(** The host types of the view functions ([rules/view.knl]), shared by every
    language and by the generic host code. Kanon declares them again in
    [view.knl] with [[@ocaml "View_host.learn_plan"]] and the same constructors,
    so that the generated [Types] re-export them
    ([type learn_plan = View_host.learn_plan = LNone | ...], like the [fp] and
    [checked] of the C language) and OCaml checks that the declarations agree;
    the generic code and every language then see one nominal type.

    They must not mention the generated types ([Bv_types]), which mention them:
    [t] and [ty] are type parameters of {!smt_op}. *)

(** The SMT operator of the encoding of a term, built by [encode_head] (see
    {!Kanon_fns.Kanon_fns.encode_head}). [op ~sort_of_ty ~encode_child operands]
    returns the SMT term, given the encoder of sorts, the (memoised) encoder of
    terms and the operands of the term, left to right. The operator decides
    when, and in which order, the sorts and the operands are encoded: this order
    is the order of the emitted [Decls], and it must be that of the code that it
    replaces (design 3.6.9). *)
type ('t, 'ty) smt_op =
  sort_of_ty:('ty -> Smt.sexp) ->
  encode_child:('t -> Smt.sexp) ->
  't list ->
  Smt.sexp

(** Same for sorts: [op ~sort_of_ty components] where [components] are the sorts
    that the sort is made of, left to right ([TSeq s] has [[s]]). *)
type 'ty smt_sort_op = sort_of_ty:('ty -> Smt.sexp) -> 'ty list -> Smt.sexp

(** Which side of the range [as_range] is. *)
type range_sign = Inside | Outside

(** How to learn the operands of a term from its value ([learn_alts]).

    - [LNone]: not invertible.
    - [LAlts l]: [l] is a list of [(known, target)] operand indices. Try them in
      order: the first whose operand [known] is already known by the
      substitution is chosen, and the operand [target] is learned from
      [learn_value]; if none, fail. ([Add], [Sub], [BitXor].)
    - [LAll (eager, order)]: learn every operand of [order], in this order; the
      value of an operand is [learn_value], computed just before it is learned,
      except for the operands of [eager] whose values are computed, in the order
      of [eager], before anything is learned. If a value is [None], fail.
      ([Not], [BvNot], [Neg], [BvExtend], [BvOfBool]: [LAll ([], [0])]; [Ptr]:
      [LAll ([], [0; 1])]; [BvConcat]: [LAll ([1; 0], [0; 1])], because the old
      code built the low half before the high half; the [Tuple] of Rust:
      [LAll ([], [0 .. n-1])].) *)
type learn_plan =
  | LNone
  | LAlts of (Z.t * Z.t) list
  | LAll of Z.t list * Z.t list
