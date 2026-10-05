(** The parts of the public interface of a typed layer that Kanon does not
    generate. The typed layer of a language is the typed interface that Kanon
    generates for it (the [S] of [kanon ocaml-typed], [Bv_typed.S] for C), whose
    modules [Bool], [Bitvec], [Float] and [Ptr] it extends with the signatures
    below, and the items of [Common]; see [typed.mli]. They are implemented by
    [Typed_extras]. The constructors of the terms are not exposed: a user
    matches on the terms with the generated destructors ([Bool.as_not]) or the
    recognisers of [Value_lang.Base]. The tags are those that Kanon generates,
    which are the same polymorphic variants in every language. *)

open Deps

module type Common = sig
  type +'a t
  type +'a ty

  module Svalue : Svalue_sugar.S
  module Eval : Eval.S with type t = Svalue.t and type ty = Svalue.ty
  module Lang : Solver_lang.S with type t = Svalue.t and type ty = Svalue.ty
  module FloatPrecision = Svalue.FloatPrecision
  module FloatClass = Svalue.FloatClass
  module RoundingMode = Svalue.RoundingMode

  (** {2 Phantom types} *)

  module T : sig
    (** The tags of the sorts of the language ([Bv_typed.Tag]). A symbolic
        integer is a bit-vector, whose subsorts are the integers known to be
        non-zero or to be zero: the predicates [TNonzero] and [TZero] of the
        rules. *)

    type sint = Bv_typed.Tag.tbitvector

    (** A symbolic integer known to be non-zero. *)
    type nonzero = Bv_typed.Tag.tnonzero

    (** A symbolic integer known to be zero. *)
    type zero = Bv_typed.Tag.tzero

    type sfloat = Bv_typed.Tag.tfloat
    type sbool = Bv_typed.Tag.tbool
    type sptr = Bv_typed.Tag.tpointer
    type sloc = Bv_typed.Tag.tloc
    type cval = [ sint | sptr | sfloat ]
    type any = [ sint | sfloat | sbool | sptr | sloc ]

    val pp_sint : Format.formatter -> sint -> unit
    val pp_nonzero : Format.formatter -> nonzero -> unit
    val pp_zero : Format.formatter -> zero -> unit
    val pp_sfloat : Format.formatter -> sfloat -> unit
    val pp_sbool : Format.formatter -> sbool -> unit
    val pp_sptr : Format.formatter -> sptr -> unit
    val pp_sloc : Format.formatter -> sloc -> unit
    val pp_cval : Format.formatter -> cval -> unit
    val pp_any : Format.formatter -> any -> unit
    val hash_sint : sint -> int
    val hash_nonzero : nonzero -> int
    val hash_zero : zero -> int
    val hash_sfloat : sfloat -> int
    val hash_sbool : sbool -> int
    val hash_sptr : sptr -> int
    val hash_sloc : sloc -> int
    val hash_cval : cval -> int
    val hash_any : any -> int
  end

  open T

  type sbool = T.sbool

  (** In which signedness(es) a checked arithmetic operation is known not to
      overflow. *)
  type checked = Bv_base.checked = { signed : bool; unsigned : bool }

  val checked_both : checked
  val unchecked : checked
  val checked_of_signed : bool -> checked

  (** {2 Sorts} *)

  val pp_ty :
    (Format.formatter -> 'a ty -> unit) -> Format.formatter -> 'a ty -> unit

  val ppa_ty : Format.formatter -> 'a ty -> unit
  val equal_ty : 'a ty -> 'b ty -> bool
  val is_bool_ty : 'a ty -> bool

  (** {2 Values} *)

  val get_ty : 'a t -> Svalue.ty
  val mk_var : Var.t -> 'a ty -> 'a t
  val iter_vars : 'a t -> (Var.t * 'b ty -> unit) -> unit
  val type_checked : Svalue.t -> 'a ty -> 'a t option
  val cast_checked : 'a t -> 'b ty -> 'b t option
  val cast_checked2 : 'a t -> 'b t -> ('c t * 'c t * 'c ty) option
  val cast_float : 'a t -> [> sfloat ] t option
  val cast_int : 'a t -> ([> sint ] t * int) option
  val size_of_int : [< sint ] t -> int
  val untyped_list : 'a t list -> Svalue.t list
  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
  val ppa : Format.formatter -> 'a t -> unit
  val equal : 'a t -> 'a t -> bool
  val compare : ([< any ] as 'a) t -> 'a t -> int
  val hash : ('a -> int) -> 'a t -> int
  val hasha : 'a t -> int
  val unique_tag : [< any ] t -> int

  (** The equality of two terms of any tags, [Bool.eq] *)
  val sem_eq : 'a t -> 'b t -> sbool t

  val sem_eq_untyped : 'a t -> 'b t -> sbool t

  (** [Bool.not_], as [Symex.Value.S] names it *)
  val not : [< sbool ] t -> [> sbool ] t

  module Infix : sig
    (* equality *)
    val ( ==@ ) : 'a t -> 'b t -> [> sbool ] t
    val ( ==?@ ) : [< any ] t -> [< any ] t -> [> sbool ] t

    (* inequality -- [$] indicates signed *)
    val ( >@ ) : [< sint ] t -> [< sint ] t -> [> sbool ] t
    val ( >$@ ) : [< sint ] t -> [< sint ] t -> [> sbool ] t
    val ( >=@ ) : [< sint ] t -> [< sint ] t -> [> sbool ] t
    val ( >=$@ ) : [< sint ] t -> [< sint ] t -> [> sbool ] t
    val ( <@ ) : [< sint ] t -> [< sint ] t -> [> sbool ] t
    val ( <$@ ) : [< sint ] t -> [< sint ] t -> [> sbool ] t
    val ( <=@ ) : [< sint ] t -> [< sint ] t -> [> sbool ] t
    val ( <=$@ ) : [< sint ] t -> [< sint ] t -> [> sbool ] t

    (* booleans *)
    val ( &&@ ) : [< sbool ] t -> [< sbool ] t -> [> sbool ] t
    val ( ||@ ) : [< sbool ] t -> [< sbool ] t -> [> sbool ] t

    (* arithmetic -- [$] indicates signed unsigned division and remainder cannot
       overflow so we consider they always result in-bounds (can overflow for
       signed with [MIN / -1]) *)
    val ( +@ ) : [< sint ] t -> [< sint ] t -> [> sint ] t
    val ( -@ ) : [< sint ] t -> [< sint ] t -> [> sint ] t
    val ( ~- ) : [< sint ] t -> [> sint ] t
    val ( *@ ) : [< sint ] t -> [< sint ] t -> [> sint ] t
    val ( /@ ) : [< sint ] t -> [< nonzero ] t -> [> sint ] t
    val ( /$@ ) : [< sint ] t -> [< nonzero ] t -> [> sint ] t
    val ( %@ ) : [< sint ] t -> [< nonzero ] t -> [> sint ] t
    val ( %$@ ) : [< sint ] t -> [< nonzero ] t -> [> sint ] t

    (* arithmetic operations with overflow ignored *)
    val ( +!@ ) : [< sint ] t -> [< sint ] t -> [> sint ] t
    val ( -!@ ) : [< sint ] t -> [< sint ] t -> [> sint ] t
    val ( *!@ ) : [< sint ] t -> [< sint ] t -> [> sint ] t
    val ( ~-! ) : [< sint ] t -> [> sint ] t

    (* checked arithmetic operations with overflow ignored *)
    val ( +!!@ ) : [< sint ] t -> [< sint ] t -> [> sint ] t
    val ( -!!@ ) : [< sint ] t -> [< sint ] t -> [> sint ] t
    val ( *!!@ ) : [< sint ] t -> [< sint ] t -> [> sint ] t
    val ( ~-!! ) : [< sint ] t -> [> sint ] t

    (* arithmetic operations for checked operations *)
    val ( +?@ ) : [< sint ] t -> [< sint ] t -> [> sint ] t * [> sbool ] t
    val ( +$?@ ) : [< sint ] t -> [< sint ] t -> [> sint ] t * [> sbool ] t
    val ( -?@ ) : [< sint ] t -> [< sint ] t -> [> sint ] t * [> sbool ] t
    val ( -$?@ ) : [< sint ] t -> [< sint ] t -> [> sint ] t * [> sbool ] t
    val ( *?@ ) : [< sint ] t -> [< sint ] t -> [> sint ] t * [> sbool ] t
    val ( *$?@ ) : [< sint ] t -> [< sint ] t -> [> sint ] t * [> sbool ] t
    val ( ~-? ) : [< sint ] t -> [> sint ] t * [> sbool ] t

    (* bit operations *)
    val ( <<@ ) : [< sint ] t -> [< sint ] t -> [> sint ] t
    val ( >>@ ) : [< sint ] t -> [< sint ] t -> [> sint ] t
    val ( >>>@ ) : [< sint ] t -> [< sint ] t -> [> sint ] t
    val ( ^@ ) : [< sint ] t -> [< sint ] t -> [> sint ] t
    val ( &@ ) : [< sint ] t -> [< sint ] t -> [> sint ] t
    val ( |@ ) : [< sint ] t -> [< sint ] t -> [> sint ] t

    (* float operations *)
    val ( ==.@ ) : [< sfloat ] t -> [< sfloat ] t -> [> sbool ] t
    val ( >.@ ) : [< sfloat ] t -> [< sfloat ] t -> [> sbool ] t
    val ( >=.@ ) : [< sfloat ] t -> [< sfloat ] t -> [> sbool ] t
    val ( <.@ ) : [< sfloat ] t -> [< sfloat ] t -> [> sbool ] t
    val ( <=.@ ) : [< sfloat ] t -> [< sfloat ] t -> [> sbool ] t
    val ( +.@ ) : [< sfloat ] t -> [< sfloat ] t -> [> sfloat ] t
    val ( -.@ ) : [< sfloat ] t -> [< sfloat ] t -> [> sfloat ] t
    val ( *.@ ) : [< sfloat ] t -> [< sfloat ] t -> [> sfloat ] t
    val ( /.@ ) : [< sfloat ] t -> [< sfloat ] t -> [> sfloat ] t
  end

  module Expr :
    Symex.Value.Expr
      with type 'a v := 'a t
       and type 'a ty := 'a ty
       and type t = Svalue.t
end

(** What the typed layer adds to the generated module [Bool]. *)
module type Bool = sig
  type +'a t
  type +'a ty

  val v_true : [> Bv_typed.Tag.tbool ] t
  val v_false : [> Bv_typed.Tag.tbool ] t
  val of_bool : bool -> [> Bv_typed.Tag.tbool ] t
  val to_bool : 'a t -> bool option

  (** Similar to [and_], but the rhs is only evaluated if the lhs is not the
      concrete false. In other words, this is a short-circuiting and. Avoids
      some errors, like a division by zero in [0 != x && n / x] when [x] is [0].
  *)
  val and_lazy :
    [< Bv_typed.Tag.tbool ] t ->
    (unit -> [< Bv_typed.Tag.tbool ] t) ->
    [> Bv_typed.Tag.tbool ] t

  (** Similar to [or_], but the rhs is only evaluated if the lhs is not the
      concrete true. In other words, this is a short-circuiting or. Avoids some
      errors, like a division by zero in [0 == x || n / x] when [x] is [0]. *)
  val or_lazy :
    [< Bv_typed.Tag.tbool ] t ->
    (unit -> [< Bv_typed.Tag.tbool ] t) ->
    [> Bv_typed.Tag.tbool ] t

  val conj : [< Bv_typed.Tag.tbool ] t list -> [> Bv_typed.Tag.tbool ] t

  val split_ands :
    [< Bv_typed.Tag.tbool ] t -> ([> Bv_typed.Tag.tbool ] t -> unit) -> unit

  val distinct_seq : 'a t Seq.t -> [> Bv_typed.Tag.tbool ] t

  val exists_1 :
    not_in:_ t ->
    'a ty ->
    ('a t -> [< Bv_typed.Tag.tbool ] t) ->
    [> Bv_typed.Tag.tbool ] t

  val exists_2 :
    not_in:_ t ->
    'a ty ->
    'b ty ->
    ('a t -> 'b t -> [< Bv_typed.Tag.tbool ] t) ->
    [> Bv_typed.Tag.tbool ] t

  val exists_3 :
    not_in:_ t ->
    'a ty ->
    'b ty ->
    'c ty ->
    ('a t -> 'b t -> 'c t -> [< Bv_typed.Tag.tbool ] t) ->
    [> Bv_typed.Tag.tbool ] t
end

(** What the typed layer adds to the generated module [Bitvec]. *)
module type Bitvec = sig
  type +'a t

  val mk : int -> Z.t -> [> Bv_typed.Tag.tbitvector ] t
  val mk_masked : int -> Z.t -> [> Bv_typed.Tag.tbitvector ] t
  val mki : int -> int -> [> Bv_typed.Tag.tbitvector ] t
  val mki_masked : int -> int -> [> Bv_typed.Tag.tbitvector ] t
  val mk_nz : int -> Z.t -> [> Bv_typed.Tag.tnonzero ] t
  val mki_nz : int -> int -> [> Bv_typed.Tag.tnonzero ] t
  val zero : int -> [> Bv_typed.Tag.tzero ] t
  val one : int -> [> Bv_typed.Tag.tnonzero ] t

  (** [bv_to_z signed bits z] reads the bit-vector [z] of [bits] bits as an
      integer of that signedness. *)
  val bv_to_z : bool -> int -> Z.t -> Z.t

  (** The value of a bit-vector literal or of a location literal. *)
  val to_z : 'a t -> Z.t option

  (** The index of the most significant bit that can be set. *)
  val msb_of : [< Bv_typed.Tag.tbitvector ] t -> int

  (** Reinterprets an integer as known to be non-zero. The caller is responsible
      for ensuring the value is indeed non-zero (e.g. an alignment). *)
  val cast_nonzero :
    [< Bv_typed.Tag.tbitvector ] t -> [> Bv_typed.Tag.tnonzero ] t

  (** The operation checked in the signedness [signed], and its overflow. *)
  val add_checked :
    signed:bool ->
    [< Bv_typed.Tag.tbitvector ] t ->
    [< Bv_typed.Tag.tbitvector ] t ->
    [> Bv_typed.Tag.tbitvector ] t * [> Bv_typed.Tag.tbool ] t

  val sub_checked :
    signed:bool ->
    [< Bv_typed.Tag.tbitvector ] t ->
    [< Bv_typed.Tag.tbitvector ] t ->
    [> Bv_typed.Tag.tbitvector ] t * [> Bv_typed.Tag.tbool ] t

  val mul_checked :
    signed:bool ->
    [< Bv_typed.Tag.tbitvector ] t ->
    [< Bv_typed.Tag.tbitvector ] t ->
    [> Bv_typed.Tag.tbitvector ] t * [> Bv_typed.Tag.tbool ] t

  val neg_checked :
    [< Bv_typed.Tag.tbitvector ] t ->
    [> Bv_typed.Tag.tbitvector ] t * [> Bv_typed.Tag.tbool ] t
end

(** What the typed layer adds to the generated module [Float]. *)
module type Float = sig
  type +'a t

  val mk : Bv_base.FloatPrecision.t -> string -> [> Bv_typed.Tag.tfloat ] t
  val mk_bits : Bv_base.FloatPrecision.t -> Z.t -> [> Bv_typed.Tag.tfloat ] t
  val of_z : Bv_base.FloatPrecision.t -> Z.t -> [> Bv_typed.Tag.tfloat ] t

  (** We cannot represent a symbolic float as a bitvector, for lack of an
      SMT-LIB function for it. However, we can return the bitvector
      representation of a float if it is concrete. *)
  val to_bits_opt :
    [< Bv_typed.Tag.tfloat ] t -> [> Bv_typed.Tag.tbitvector ] t option

  val to_float_opt : [< Bv_typed.Tag.tfloat ] t -> float option
  val sign_bit_opt : [< Bv_typed.Tag.tfloat ] t -> bool option

  val approx :
    (float -> float) ->
    [< Bv_typed.Tag.tfloat ] t ->
    [> Bv_typed.Tag.tfloat ] t option

  val approx2 :
    (float -> float -> float) ->
    [< Bv_typed.Tag.tfloat ] t ->
    [< Bv_typed.Tag.tfloat ] t ->
    [> Bv_typed.Tag.tfloat ] t option

  val zero : Bv_base.FloatPrecision.t -> [> Bv_typed.Tag.tfloat ] t
  val neg_zero : Bv_base.FloatPrecision.t -> [> Bv_typed.Tag.tfloat ] t
  val one : Bv_base.FloatPrecision.t -> [> Bv_typed.Tag.tfloat ] t
  val nan : Bv_base.FloatPrecision.t -> [> Bv_typed.Tag.tfloat ] t
  val infinity : Bv_base.FloatPrecision.t -> [> Bv_typed.Tag.tfloat ] t
  val neg_infinity : Bv_base.FloatPrecision.t -> [> Bv_typed.Tag.tfloat ] t
  val fp_of : [< Bv_typed.Tag.tfloat ] t -> Bv_base.FloatPrecision.t

  (** The IEEE 754-2019 [minimum]: unlike [min] a NaN propagates, and [-0.0] is
      strictly below [+0.0]. This is equivalent to:
      {@ocaml[
      let minimum x y =
        if is_nan x || is_nan y then nan
        else if lt x y then x
        else if gt x y then y
        else if is_negative x then x
        else y
      ]} *)
  val minimum :
    [< Bv_typed.Tag.tfloat ] t ->
    [< Bv_typed.Tag.tfloat ] t ->
    [> Bv_typed.Tag.tfloat ] t

  (** IEEE-754-2019 [maximum]. See [minimum] for the differences with [max]. *)
  val maximum :
    [< Bv_typed.Tag.tfloat ] t ->
    [< Bv_typed.Tag.tfloat ] t ->
    [> Bv_typed.Tag.tfloat ] t
end

(** What the typed layer adds to the generated module [Ptr]. *)
module type Ptr = sig
  type +'a t

  val mk :
    [< Bv_typed.Tag.tloc ] t ->
    [< Bv_typed.Tag.tbitvector ] t ->
    [> Bv_typed.Tag.tpointer ] t

  val decompose :
    [< Bv_typed.Tag.tpointer ] t ->
    [> Bv_typed.Tag.tloc ] t * [> Bv_typed.Tag.tbitvector ] t

  val add_ofs :
    [< Bv_typed.Tag.tpointer ] t ->
    [< Bv_typed.Tag.tbitvector ] t ->
    [> Bv_typed.Tag.tpointer ] t

  val loc_of_int : int -> int -> [> Bv_typed.Tag.tloc ] t
  val loc_of_z : int -> Z.t -> [> Bv_typed.Tag.tloc ] t
  val null : int -> [> Bv_typed.Tag.tpointer ] t
  val null_loc : int -> [> Bv_typed.Tag.tloc ] t
  val is_null_loc : [< Bv_typed.Tag.tloc ] t -> [> Bv_typed.Tag.tbool ] t
  val is_null : [< Bv_typed.Tag.tpointer ] t -> [> Bv_typed.Tag.tbool ] t
  val is_at_null_loc : [< Bv_typed.Tag.tpointer ] t -> [> Bv_typed.Tag.tbool ] t
end

(** What [Bv_solver]'s functors consume of a typed layer. It does not mention
    [Svalue] nor [Eval]: the solver never uses them. *)
module type Solver_value = sig
  module Lang : Solver_lang.S

  module T : sig
    type sint = Bv_typed.Tag.tbitvector
    type sbool = Bv_typed.Tag.tbool
  end

  include Symex.Value.S with type sbool = T.sbool

  (** {2 Extra operations beyond [Symex.Value.S]} *)

  val untype_type : 'a ty -> Lang.ty
  val type_ : Lang.t -> 'a t
  val untyped : 'a t -> Lang.t
end
