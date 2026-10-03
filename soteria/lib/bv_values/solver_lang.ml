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
