(** The "sugar" of the untyped layer: the [Bool], [BitVec], [Float], [Ptr],
    [SSeq] and [Infix] modules, sorts, [iter_vars], [pp_ty]... over any language
    {!Value_lang.S}: the [Svalue] member of {!Typed_intf.S} ([Typed.Svalue]). It
    was written as a port of [svalue.ml:50-900] of the first generation of the
    value language, with these differences, none of them behavioural:
    - no [kind], [t_kind], [t_node], [node], [( <| )], [Unop]/[Binop]/[Triop]/
      [Nop], [R], [Ext], [Prims]: the generic code does not see constructors.
      The two sites of soteria-c use {!Value_lang.Base.as_eq} and [as_bitvec]
      (design 3.5);
    - [Ptr.mk] and [SSeq.mk] go through {!Kanon_fns.Kanon_fns.mk_ptr} and
      [mk_seq]; [Ptr.null_loc], [Ptr.loc_of_z] through [mk_loc];
    - [BitVec.to_z] still returns the value of a location literal ([LocLit]).

    (The [Typed] sugar is a port of [svalue.ml:591-900].) *)

module type S = sig
  type t
  type ty

  module Var = Symex.Var
  module F = Floatml.AnyFloat
  module FloatPrecision = Bv_base.FloatPrecision
  module FloatClass = Bv_base.FloatClass
  module RoundingMode = Bv_base.RoundingMode

  type checked = Bv_base.checked = { signed : bool; unsigned : bool }

  val unchecked : checked
  val checked_both : checked
  val checked_of_signed : bool -> checked

  (** {2 Sorts} *)

  val t_bool : ty
  val t_float : FloatPrecision.t -> ty
  val t_f16 : ty
  val t_f32 : ty
  val t_f64 : ty
  val t_f128 : ty
  val t_loc : int -> ty
  val t_ptr : int -> ty
  val t_seq : ty -> ty
  val t_bv : int -> ty
  val is_float : ty -> bool
  val is_bv : ty -> bool
  val is_bool_ty : ty -> bool

  (** Fails ("Not a float") on other sorts. *)
  val precision_of_f : ty -> FloatPrecision.t

  (** The size of a bit-vector, pointer or location sort; fails ("Not a bit
      value") on others. *)
  val size_of : ty -> int

  val pp_ty : ty Fmt.t
  val equal_ty : ty -> ty -> bool

  (** {2 Values} *)

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val unique_tag : t -> int
  val pp : t Fmt.t

  module Hashtbl : Stdlib.Hashtbl.S with type key = t

  val mk_var : Var.t -> ty -> t

  (** The free variables, binder aware. *)
  val iter_vars : t -> (Var.t * ty -> unit) -> unit

  val sure_neq : t -> t -> bool

  (** {2 Booleans} *)

  module Bool : sig
    val v_true : t
    val v_false : t
    val to_bool : t -> bool option
    val of_bool : bool -> t
    val and_ : t -> t -> t
    val and_lazy : t -> (unit -> t) -> t
    val or_ : t -> t -> t
    val or_lazy : t -> (unit -> t) -> t
    val conj : t list -> t
    val not : t -> t
    val split_ands : t -> t Iter.t
    val distinct : t list -> t
    val distinct_seq : t Seq.t -> t
    val ite : t -> t -> t -> t

    (** Do not use this directly when instantiating your own binders, use
        [exists_n] or its variants *)
    val mk_exists : (Var.t * ty) list -> t -> t

    val exists_n : not_in:t -> ty list -> (t list -> t) -> t
    val exists_1 : not_in:t -> ty -> (t -> t) -> t
    val exists_2 : not_in:t -> ty -> ty -> (t -> t -> t) -> t
    val exists_3 : not_in:t -> ty -> ty -> ty -> (t -> t -> t -> t) -> t
    val sem_eq : t -> t -> t
    val sem_eq_untyped : t -> t -> t
  end

  (** {2 Bit vectors} *)

  module BitVec : sig
    (* constructor *)
    val mk : int -> Z.t -> t
    val mk_masked : int -> Z.t -> t
    val mki : int -> int -> t
    val zero : int -> t
    val one : int -> t
    val bv_to_z : bool -> int -> Z.t -> Z.t

    (** The value of a bit-vector literal or of a location literal. *)
    val to_z : t -> Z.t option

    val msb_of : t -> int

    (* arithmetic *)
    val add : ?checked:checked -> t -> t -> t
    val sub : ?checked:checked -> t -> t -> t
    val mul : ?checked:checked -> t -> t -> t
    val div : signed:bool -> t -> t -> t
    val rem : signed:bool -> t -> t -> t
    val mod_ : t -> t -> t
    val neg : ?checked:bool -> t -> t

    (* overflow checks *)
    val add_overflows : signed:bool -> t -> t -> t
    val sub_overflows : signed:bool -> t -> t -> t
    val mul_overflows : signed:bool -> t -> t -> t
    val neg_overflows : t -> t

    (* inequalities *)
    val lt : signed:bool -> t -> t -> t
    val leq : signed:bool -> t -> t -> t
    val gt : signed:bool -> t -> t -> t
    val geq : signed:bool -> t -> t -> t

    (* bitvec manipulation *)
    val concat : t -> t -> t
    val extend : signed:bool -> int -> t -> t
    val extract : int -> int -> t -> t

    (* bitwise operations *)
    val and_ : t -> t -> t
    val or_ : t -> t -> t
    val xor : t -> t -> t
    val shl : t -> t -> t
    val lshr : t -> t -> t
    val ashr : t -> t -> t
    val not : t -> t

    (* bool-bv conversions *)
    val of_bool : int -> t -> t
    val to_bool : t -> t
    val not_bool : t -> t

    (* float-bv conversions *)
    val of_float : rounding:RoundingMode.t -> signed:bool -> size:int -> t -> t

    val to_float :
      rounding:RoundingMode.t -> signed:bool -> fp:FloatPrecision.t -> t -> t

    val to_float_raw : t -> t
  end

  (** {2 Floating point} *)

  module Float : sig
    (** The raw node constructor; all others go through it. The precision is
        that of the float. *)
    val mk_raw : FloatPrecision.t -> F.t -> t

    val mk : FloatPrecision.t -> string -> t
    val mk_bits : FloatPrecision.t -> Z.t -> t
    val of_z : FloatPrecision.t -> Z.t -> t
    val to_bits_opt : t -> t option
    val to_float_opt : t -> float option
    val sign_bit_opt : t -> bool option
    val approx : (float -> float) -> t -> t option
    val approx2 : (float -> float -> float) -> t -> t -> t option
    val zero : FloatPrecision.t -> t
    val neg_zero : FloatPrecision.t -> t
    val one : FloatPrecision.t -> t
    val nan : FloatPrecision.t -> t
    val infinity : FloatPrecision.t -> t
    val neg_infinity : FloatPrecision.t -> t
    val fp_of : t -> FloatPrecision.t

    (* conversion between precisions *)
    val cast : rounding:RoundingMode.t -> fp:FloatPrecision.t -> t -> t

    (* arithmetic *)
    val add : t -> t -> t
    val sub : t -> t -> t
    val mul : t -> t -> t
    val div : t -> t -> t
    val rem : t -> t -> t
    val fmod : t -> t -> t
    val fmod_of_rem : t -> t -> t -> t
    val fma : t -> t -> t -> t
    val min : t -> t -> t
    val max : t -> t -> t
    val minimum : t -> t -> t
    val maximum : t -> t -> t
    val abs : t -> t
    val neg : t -> t
    val sqrt : t -> t
    val round : RoundingMode.t -> t -> t

    (* comparisons *)
    val eq : t -> t -> t
    val lt : t -> t -> t
    val leq : t -> t -> t
    val gt : t -> t -> t
    val geq : t -> t -> t

    (* classification *)
    val is_floatclass : FloatClass.t -> t -> t
    val is_normal : t -> t
    val is_subnormal : t -> t
    val is_zero : t -> t
    val is_infinite : t -> t
    val is_nan : t -> t
    val is_negative : t -> t
    val is_positive : t -> t
  end

  (** {2 Pointers} *)

  module Ptr : sig
    val mk : t -> t -> t
    val loc : t -> t
    val null_loc : int -> t
    val is_null_loc : t -> t
    val loc_of_z : int -> Z.t -> t
    val loc_of_int : int -> int -> t
    val ofs : t -> t
    val decompose : t -> t * t
    val add_ofs : t -> t -> t
    val null : int -> t
    val is_null : t -> t
    val is_at_null_loc : t -> t
  end

  (** {2 Sequences} *)

  module SSeq : sig
    val mk : seq_ty:ty -> t list -> t
    val inner_ty : ty -> ty
  end

  (** {2 Infix operators} *)

  module Infix : sig
    val bv_z : int -> Z.t -> t
    val ptr : t -> t -> t
    val seq : seq_ty:ty -> t list -> t
    val ( ==@ ) : t -> t -> t
    val ( ==?@ ) : t -> t -> t
    val ( &&@ ) : t -> t -> t
    val ( ||@ ) : t -> t -> t
    val ( >@ ) : t -> t -> t
    val ( >=@ ) : t -> t -> t
    val ( <@ ) : t -> t -> t
    val ( <=@ ) : t -> t -> t
    val ( >$@ ) : t -> t -> t
    val ( >=$@ ) : t -> t -> t
    val ( <$@ ) : t -> t -> t
    val ( <=$@ ) : t -> t -> t
    val ( +@ ) : t -> t -> t
    val ( -@ ) : t -> t -> t
    val ( ~- ) : t -> t
    val ( *@ ) : t -> t -> t
    val ( /@ ) : t -> t -> t
    val ( /$@ ) : t -> t -> t
    val ( %@ ) : t -> t -> t
    val ( %$@ ) : t -> t -> t
    val ( <<@ ) : t -> t -> t
    val ( >>@ ) : t -> t -> t
    val ( >>>@ ) : t -> t -> t
    val ( ^@ ) : t -> t -> t
    val ( &@ ) : t -> t -> t
    val ( |@ ) : t -> t -> t
    val ( ==.@ ) : t -> t -> t
    val ( >.@ ) : t -> t -> t
    val ( >=.@ ) : t -> t -> t
    val ( <.@ ) : t -> t -> t
    val ( <=.@ ) : t -> t -> t
    val ( +.@ ) : t -> t -> t
    val ( -.@ ) : t -> t -> t
    val ( *.@ ) : t -> t -> t
    val ( /.@ ) : t -> t -> t
  end
end

module Make (V : Value_lang.S) : S with type t = V.t and type ty = V.ty = struct
  module L = Logs.Import.L
  module K = V.K
  module Var = Symex.Var
  module F = Floatml.AnyFloat
  module FloatPrecision = Bv_base.FloatPrecision
  module FloatClass = Bv_base.FloatClass
  module RoundingMode = Bv_base.RoundingMode

  type t = V.t
  type ty = V.ty
  type checked = Bv_base.checked = { signed : bool; unsigned : bool }

  let unchecked = Bv_base.unchecked
  let checked_both = Bv_base.checked_both
  let checked_of_signed = Bv_base.checked_of_signed

  (* {2 Sorts} *)

  let t_bool = K.t_bool
  let t_float = K.t_float
  let t_f16 = t_float F16
  let t_f32 = t_float F32
  let t_f64 = t_float F64
  let t_f128 = t_float F128
  let t_loc n = K.t_loc (Z.of_int n)
  let t_ptr n = K.t_ptr (Z.of_int n)
  let t_seq = K.t_seq
  let t_bv = V.t_bv
  let is_float ty = Option.is_some (K.as_tfloat ty)
  let is_bv ty = Option.is_some (K.as_tbitvector ty)
  let is_bool_ty = K.is_tbool

  let precision_of_f ty =
    match K.as_tfloat ty with
    | Some p -> p
    | None -> L.failwith "Not a float: %a" K.pp_ty ty

  let[@inline] size_of ty =
    match K.sized_ty ty with
    | Some n -> Z.to_int n
    | None -> L.failwith "Not a bit value"

  let pp_ty = K.pp_ty
  let equal_ty = V.equal_ty

  (* {2 Values} *)

  let equal = V.equal
  let compare = V.compare
  let hash = V.hash
  let unique_tag = V.unique_tag
  let pp = V.pp

  module Hashtbl = V.Hashtbl

  let mk_var = V.mk_var
  let iter_vars = V.iter_vars
  let sure_neq = V.sure_neq

  (* {2 Booleans} *)

  module Bool = struct
    let v_true = V.v_true
    let v_false = V.v_false

    let[@inline] to_bool t =
      if equal t v_true then Some true
      else if equal t v_false then Some false
      else None

    (* avoid re-alloc and re-hashconsing *)
    let of_bool = V.of_bool
    let and_ = K.b_and
    let or_ = K.b_or
    let not = K.b_not
    let ite = K.b_ite
    let sem_eq = K.sem_eq
    let mk_exists = K.b_mk_exists

    (** * [exists_n ~not_in tys mk] creates an existential with [length tys]
        variables of types [tys], that are not in [not_in], and with body
        created by [mk : t list -> t] which takes the created variables as input
        in the same order as [tys]. *)
    let exists_n ~not_in tys mk =
      (* FIXME: see the old [Svalue.Bool.exists_n] *)
      let max = ref 0 in
      iter_vars not_in (fun (v, _) -> max := Int.max !max (Var.to_int v));
      (* We create something high to note those are actually existentials and
         reduce chances of conflict *)
      let base = !max + 10_000 in
      let binders = List.mapi (fun i ty -> (Var.of_int (base + i), ty)) tys in
      let binders_vs = List.map (fun (v, ty) -> mk_var v ty) binders in
      let body = mk binders_vs in
      mk_exists binders body

    let exists_1 ~not_in ty mk =
      exists_n ~not_in [ ty ] (function
        | [ v ] -> mk v
        | _ -> L.failwith "exists_1: unreachable")

    let exists_2 ~not_in ty1 ty2 mk =
      exists_n ~not_in [ ty1; ty2 ] (function
        | [ v1; v2 ] -> mk v1 v2
        | _ -> L.failwith "exists_2: unreachable")

    let exists_3 ~not_in ty1 ty2 ty3 mk =
      exists_n ~not_in [ ty1; ty2; ty3 ] (function
        | [ v1; v2; v3 ] -> mk v1 v2 v3
        | _ -> L.failwith "exists_3: unreachable")

    let sem_eq_untyped = K.sem_eq_untyped
    let and_lazy v1 v2 = if equal v1 v_false then v_false else and_ v1 (v2 ())
    let or_lazy v1 v2 = if equal v1 v_true then v_true else or_ v1 (v2 ())
    let conj l = List.fold_left and_ v_true l
    let split_ands = V.split_ands
    let distinct_seq s = K.b_distinct (List.of_seq s)
    let distinct l = K.b_distinct l
  end

  (* {2 Bit vectors} *)

  module BitVec = struct
    let mk = K.mk_bv
    let mk_masked = K.mk_masked
    let mki n i = mk n (Z.of_int i)
    let zero = K.bv_zero
    let one = K.bv_one

    (** [bv_to_z signed bits z] parses a BitVector [z], for a given bitwidth
        [bits], with [signed], into an integer. *)
    let bv_to_z signed bits z = if signed then Z.signed_extract z 0 bits else z

    let to_z v =
      match K.as_bitvec v with Some _ as z -> z | None -> K.as_loclit v

    let msb_of v = Z.to_int (K.msb_of v)
    let add ?(checked = unchecked) v1 v2 = K.bv_add checked v1 v2
    let sub ?(checked = unchecked) v1 v2 = K.bv_sub checked v1 v2
    let mul ?(checked = unchecked) v1 v2 = K.bv_mul checked v1 v2
    let div ~signed v1 v2 = K.bv_div signed v1 v2
    let rem ~signed v1 v2 = K.bv_rem signed v1 v2
    let mod_ = K.bv_mod
    let neg ?(checked = false) v = K.bv_neg checked v
    let add_overflows ~signed v1 v2 = K.bv_add_overflows signed v1 v2
    let sub_overflows ~signed v1 v2 = K.bv_sub_overflows signed v1 v2
    let mul_overflows ~signed v1 v2 = K.bv_mul_overflows signed v1 v2
    let neg_overflows = K.bv_neg_overflows
    let lt ~signed v1 v2 = K.bv_lt signed v1 v2
    let leq ~signed v1 v2 = K.bv_leq signed v1 v2
    let gt ~signed v1 v2 = lt ~signed v2 v1
    let geq ~signed v1 v2 = leq ~signed v2 v1
    let concat = K.bv_concat
    let extend ~signed extend_by v = K.bv_extend signed (Z.of_int extend_by) v
    let extract from_ to_ v = K.bv_extract (Z.of_int from_) (Z.of_int to_) v
    let and_ = K.bv_and
    let or_ = K.bv_or
    let xor = K.bv_xor
    let shl = K.bv_shl
    let lshr = K.bv_lshr
    let ashr = K.bv_ashr
    let not = K.bv_not
    let of_bool n b = K.bv_of_bool (Z.of_int n) b
    let to_bool = K.bv_to_bool
    let not_bool = K.bv_not_bool

    let of_float ~rounding ~signed ~size v =
      K.bv_of_float rounding signed (Z.of_int size) v

    let to_float ~rounding ~signed ~fp v = K.bv_to_float rounding signed fp v
    let to_float_raw = K.bv_to_float_raw
  end

  (* {2 Floating point} *)

  module Float = struct
    let fp_of v =
      match K.as_tfloat (V.type_of v) with
      | Some fp -> fp
      | None -> L.failwith "Unsupported float type"

    let mk_raw (_ : FloatPrecision.t) f = K.mk_float f

    let mk fp s =
      match F.of_string_opt fp s with
      | Some f -> mk_raw fp f
      | None -> L.failwith "Invalid float literal: %S" s

    let mk_bits fp z = mk_raw fp (F.of_bits_z fp z)

    (* A mathematical integer, rounded to [fp]; a magnitude too large for the
       format gives an infinity. Unlike {!BitVec.to_float} the argument is not
       the contents of a bit-vector, so it is not reduced to any width. *)
    let of_z fp z = mk_raw fp (F.of_z fp z)
    let to_float_opt v = Option.map F.to_float (K.as_float v)

    let sign_bit_opt v =
      match K.as_float v with
      | Some f ->
          Some (Z.testbit (F.to_z f) (FloatPrecision.size (fp_of v) - 1))
      | None -> None

    let approx f v =
      Option.map
        (fun x ->
          let fp = fp_of v in
          mk_raw fp (F.of_float fp (f x)))
        (to_float_opt v)

    let approx2 f v1 v2 =
      Soteria_std.Option.map2
        (fun x1 x2 ->
          let fp = fp_of v1 in
          mk_raw fp (F.of_float fp (f x1 x2)))
        (to_float_opt v1) (to_float_opt v2)

    let zero fp = mk_raw fp (F.zero fp)
    let neg_zero fp = mk_raw fp (F.neg_zero fp)
    let one fp = mk_raw fp (F.one fp)
    let nan fp = mk_raw fp (F.nan fp)
    let infinity fp = mk_raw fp (F.infinity fp)
    let neg_infinity fp = mk_raw fp (F.neg_infinity fp)

    let to_bits_opt v =
      match K.as_float v with
      | Some f ->
          let size = FloatPrecision.size (fp_of v) in
          Some (BitVec.mk_masked size (F.to_z f))
      | None -> None

    let is_floatclass fc sv = K.float_is_floatclass fc sv
    let is_normal = is_floatclass Normal
    let is_subnormal = is_floatclass Subnormal
    let is_infinite = is_floatclass Infinite
    let is_nan = is_floatclass NaN
    let is_zero = is_floatclass Zero
    let is_negative = K.float_is_negative
    let is_positive = K.float_is_positive
    let cast ~rounding ~fp v = K.float_cast rounding fp v
    let eq = K.float_eq
    let lt = K.float_lt
    let leq = K.float_leq
    let gt v1 v2 = lt v2 v1
    let geq v1 v2 = leq v2 v1
    let add = K.float_add
    let sub = K.float_sub
    let div = K.float_div
    let mul = K.float_mul
    let rem = K.float_rem
    let abs = K.float_abs
    let neg = K.float_neg
    let fma = K.float_fma
    let fmod_of_rem = K.float_fmod_of_rem
    let fmod = K.float_fmod
    let min = K.float_min
    let max = K.float_max

    (* The IEEE 754-2019 [minimum]/[maximum]: unlike {!min}/{!max} a NaN
       propagates, and [-0.0] is strictly below [+0.0]. SMT-Lib has neither, so
       they are built from comparisons. *)
    let minimum v1 v2 =
      Bool.ite (Bool.or_ (is_nan v1) (is_nan v2)) (nan (fp_of v1))
      @@ Bool.ite (lt v1 v2) v1
      @@ Bool.ite (lt v2 v1) v2
      @@ Bool.ite (is_negative v1) v1 v2

    let maximum v1 v2 =
      Bool.ite (Bool.or_ (is_nan v1) (is_nan v2)) (nan (fp_of v1))
      @@ Bool.ite (lt v1 v2) v2
      @@ Bool.ite (lt v2 v1) v1
      @@ Bool.ite (is_negative v1) v2 v1

    let sqrt = K.float_sqrt
    let round rm sv = K.float_round rm sv
  end

  (* {2 Pointers} *)

  module Ptr = struct
    let mk = K.mk_ptr
    let loc = K.ptr_loc
    let null_loc n = K.mk_loc n Z.zero
    let is_null_loc l = Bool.sem_eq l (null_loc (size_of (V.type_of l)))
    let loc_of_z n z = K.mk_loc n z
    let loc_of_int n i = loc_of_z n (Z.of_int i)
    let ofs = K.ptr_ofs

    let decompose p =
      match K.as_ptr p with Some (l, o) -> (l, o) | None -> (loc p, ofs p)

    let add_ofs p o =
      let loc, ofs = decompose p in
      mk loc (BitVec.add ofs o)

    let null n = mk (null_loc n) (BitVec.zero n)
    let is_null p = Bool.sem_eq p (null (size_of (V.type_of p)))
    let is_at_null_loc p = is_null_loc (loc p)
  end

  (* {2 Sequences} *)

  module SSeq = struct
    let mk ~seq_ty l = K.mk_seq seq_ty l

    let inner_ty ty =
      match K.as_tseq ty with
      | Some ty -> ty
      | None -> L.failwith "Expected a sequence type"
  end

  (* {2 Infix operators} *)

  module Infix = struct
    let bv_z = BitVec.mk
    let ptr = Ptr.mk
    let seq = SSeq.mk
    let ( ==@ ) = Bool.sem_eq
    let ( ==?@ ) = Bool.sem_eq_untyped
    let ( &&@ ) = Bool.and_
    let ( ||@ ) = Bool.or_
    let ( >@ ) = BitVec.gt ~signed:false
    let ( >=@ ) = BitVec.geq ~signed:false
    let ( <@ ) = BitVec.lt ~signed:false
    let ( <=@ ) = BitVec.leq ~signed:false
    let ( >$@ ) = BitVec.gt ~signed:true
    let ( >=$@ ) = BitVec.geq ~signed:true
    let ( <$@ ) = BitVec.lt ~signed:true
    let ( <=$@ ) = BitVec.leq ~signed:true
    let ( +@ ) = BitVec.add ~checked:unchecked
    let ( -@ ) = BitVec.sub ~checked:unchecked
    let ( ~- ) v = BitVec.neg v
    let ( *@ ) = BitVec.mul ~checked:unchecked
    let ( /@ ) = BitVec.div ~signed:false
    let ( /$@ ) = BitVec.div ~signed:true
    let ( %@ ) = BitVec.rem ~signed:false
    let ( %$@ ) = BitVec.rem ~signed:true
    let ( <<@ ) = BitVec.shl
    let ( >>@ ) = BitVec.lshr
    let ( >>>@ ) = BitVec.ashr
    let ( ^@ ) = BitVec.xor
    let ( &@ ) = BitVec.and_
    let ( |@ ) = BitVec.or_
    let ( ==.@ ) = Float.eq
    let ( >.@ ) = Float.gt
    let ( >=.@ ) = Float.geq
    let ( <.@ ) = Float.lt
    let ( <=.@ ) = Float.leq
    let ( +.@ ) = Float.add
    let ( -.@ ) = Float.sub
    let ( *.@ ) = Float.mul
    let ( /.@ ) = Float.div
  end
end
