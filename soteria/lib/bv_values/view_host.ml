(** The host types of the view functions ([rules/view.knl]), shared by every
    language and by the generic host code. Kanon declares them again in
    [view.knl] with [[@ocaml "View_host.pp_style"]] and the same constructors,
    so that the generated [Types] re-export them
    ([type pp_style = View_host.pp_style = PAtom of pphead | ...], like the [fp]
    and [checked] of the C language) and OCaml checks that the declarations
    agree; the generic code and every language then see one nominal type.

    They must not mention the generated types ([Bv_types]), which mention them:
    [t] and [ty] are type parameters of {!smt_op}. *)

(** A piece of text of the pretty-printer: a [pphead] is printed by applying it
    to the formatter. It may emit break hints and open or close boxes. *)
type pphead = Format.formatter -> unit

(** The SMT operator of the encoding of a term, built by [encode_head] (see
    {!Kanon_fns.Kanon_fns.encode_head}). [op ~sort_of_ty ~encode_child operands]
    returns the SMT term, given the encoder of sorts, the (memoised) encoder of
    terms and the operands of the term, left to right. The operator decides
    when, and in which order, the sorts and the operands are encoded: this order
    is the order of the emitted [Decls], and it must be that of the code that it
    replaces (design 3.6.9). *)
type ('t, 'ty) smt_op =
  sort_of_ty:('ty -> Soteria.Smt.sexp) ->
  encode_child:('t -> Soteria.Smt.sexp) ->
  't list ->
  Soteria.Smt.sexp

(** Same for sorts: [op ~sort_of_ty components] where [components] are the sorts
    that the sort is made of, left to right ([TSeq s] has [[s]]). *)
type 'ty smt_sort_op =
  sort_of_ty:('ty -> Soteria.Smt.sexp) -> 'ty list -> Soteria.Smt.sexp

(** Which side of the range [as_range] is. *)
type range_sign = Inside | Outside

(** A piece of a {!PSeq} pretty-printing template. [PArg i]: the [i]th operand
    (from 0), pretty-printed. [PArgOf (i, j)]: the [j]th operand of the [i]th
    operand. [PArgs h]: all the operands, separated by [h]. *)
type ppiece =
  | PText of pphead
  | PArg of Z.t
  | PArgOf of Z.t * Z.t
  | PArgs of pphead

(** How to pretty-print a term; the operands are those of [operands], printed by
    the generic printer ({!Pp_v}) with the exact [Fmt] formats below.

    - [PAtom h]: [h]; the operands are not printed. (svalue.ml:101-143: [Var]
      ["V%a"], [Bool], [Float], [BitVec].)
    - [PCall h]: [Fmt.pf ft "%a(%a)" h (Fmt.list ~sep:Fmt.comma pp) operands].
      ([Unop], [Nop], with a break hint in the separator.)
    - [PCallPlain h]: the same with the separator [Fmt.any ", "], which has no
      break hint. ([Triop Fma] ["%a(%a, %a, %a)"], [Ptr] ["&(%a, %a)"].)
    - [PIn h]: [Fmt.pf ft "(%a %a %a)" pp a h pp b] for two operands. ([Binop].)
    - [PIte]: [Fmt.pf ft "(%a ? %a : %a)"] for three operands.
    - [PBrackets]:
      [Fmt.pf ft "%a" (Fmt.brackets (Fmt.list ~sep:Fmt.comma pp)) operands]
      ([Seq]; note the box of [Fmt.brackets]).
    - [PSeq l]: the pieces of [l], in order, with no break hint of their own:
      the escape for every other format. ([Exists] ["∃ %a. %a"], [Not (Eq _)]
      printed [(a != b)] with [PArgOf (0, 0)] and [PArgOf (0, 1)], and every
      format of the extensions.) *)
type pp_style =
  | PAtom of pphead
  | PCall of pphead
  | PCallPlain of pphead
  | PIn of pphead
  | PIte
  | PBrackets
  | PSeq of ppiece list

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
