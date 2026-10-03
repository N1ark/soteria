(** The successor of {!Solver_lang.S} as the contract of a value language: the
    concrete record of its terms ({!Term}), the view that the generic functors
    consume ({!Base}), and the complete language ({!S}) that the solver and the
    typed layer consume.
    {v
      Types (generated)          satisfies Term (concrete record)
      Rules + prims + glue       satisfy Kanon_fns        (kanon_fns.ml)
            |
            |  Value_lang.Make (T) (K)            : Base   (this file)
            v
      Pp_v.Make (Base)  : pp       Eval_v.Make (Base) : eval
            |                                |
            |  Lang_v.Make (T) (K)           |          (lang_v.ml)
            v                                v
      Value_lang.S = Base + pp + eval   (a subtype of Solver_lang.S)
            |
            v
      Svalue_sugar_v, Expr_v, Typed_v, and Analyses / Bv_solver / Encoding
    v}

    {!Base} and {!S} differ in [pp] and [eval] only: they are produced by the
    generic printer and evaluator, which consume {!Base} (and could not consume
    {!S} that contains them). *)

open Deps

(** The concrete record of the terms of a generated language, as in design E9.
    The generated [Types] of Kanon satisfies it (checked by [check/]): generic
    code gets the field accesses, so [equal], [unique_tag], [type_of] and
    [compare] cost nothing, but [kind] stays abstract, so that no generic
    function can match a constructor: each of those is a {!Kanon_fns} function,
    a prim, or per-language. *)
module type Term = sig
  type kind
  type ty
  type t = { kind : kind; ty : ty; tag : int }

  (** The hash-consing constructor; the tags are 0, 1, 2... in the order of
      creation. *)
  val node : kind -> ty -> t

  val equal_t : t -> t -> bool
  val hash_t : t -> int
  val equal_ty : ty -> ty -> bool
  val hash_ty : ty -> int
end

(** What the generic drivers consume ({!Pp_v}, {!Eval_v}): the identity of
    terms, the functions of {!Kanon_fns} ([K]), and the members of
    {!Solver_lang.S} that need nothing more than these. *)
module type Base = sig
  type t
  type ty

  (** The functions of the language. *)
  module K : Kanon_fns.Kanon_fns with type t = t and type ty = ty

  (** {2 Identity (from [Term]; O(1))} *)

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val unique_tag : t -> int
  val type_of : t -> ty
  val equal_ty : ty -> ty -> bool
  val hash_ty : ty -> int

  module Hashtbl : Stdlib.Hashtbl.S with type key = t

  (** {2 The members of [Solver_lang.S], except [pp] and [eval]}

      See {!Solver_lang.S} for their documentation. *)

  val v_true : t
  val v_false : t
  val of_bool : bool -> t
  val not_ : t -> t
  val and_ : t -> t -> t
  val or_ : t -> t -> t
  val ite : t -> t -> t -> t
  val sem_eq : t -> t -> t
  val mk_var : Var.t -> ty -> t

  (** [= K.t_bv (Z.of_int n)] *)
  val t_bv : int -> ty

  (** [= K.mk_bv] *)
  val bv_mk : int -> Z.t -> t

  (** [= K.bv_leq false] *)
  val bv_uleq : t -> t -> t

  val is_literal : t -> bool

  (** [= K.is_bool_ty (type_of v)] *)
  val is_bool : t -> bool

  val as_var : t -> (Var.t * ty) option

  (** [= Option.map Z.to_int (K.as_bv_ty s)] *)
  val as_bv_ty : ty -> int option

  val as_not : t -> t option
  val as_eq : t -> (t * t) option
  val as_and : t -> (t * t) option
  val as_or : t -> (t * t) option
  val as_ite : t -> (t * t * t) option
  val as_lt : t -> (t * t) option
  val as_leq : t -> (t * t) option
  val as_distinct : t -> t list option

  (** Via [K.as_and], with no list: the old [Bool.split_ands]. *)
  val split_ands : t -> t Iter.t

  val sure_neq : t -> t -> bool

  (** [= K.implies_or_contradicts q neg_q pc]; keep it [[@inline]]. *)
  val implies_or_contradicts : q:t -> neg_q:t -> t -> bool option

  type sign = Pos | Neg

  (** [K.as_range], with [Inside] for [Pos], [Outside] for [Neg] and the size as
      an [int]. *)
  val as_range : t -> (Var.t * int * (sign * (Z.t * Z.t))) option

  (** The old [map_operands]: [K.maps_operands v], else [v] itself; the operands
      [cs] of [v] are mapped left to right and [v] is rebuilt with [K.rebuild]
      iff one changed. *)
  val map_operands : (t -> t) -> t -> t

  (** Replaces [Svalue.iter_vars] ([svalue.ml:71-93]): the free variables,
      binder aware, via [K.as_var], [K.as_exists] and [K.operands], left to
      right. *)
  val iter_vars : t -> (Var.t * ty -> unit) -> unit

  (** [= Z.to_int (K.cost v)] *)
  val cost : t -> int

  (** From [K.random_bound] and [K.random_of_z], see there. *)
  val random_value : ty -> (unit -> t) option

  (** [= (K.encode_sort ty) ~sort_of_ty (K.sort_operands ty)] *)
  val encode_ty : sort_of_ty:(ty -> Smt.sexp) -> ty -> Smt.sexp

  (** [= (K.encode_head v) ~sort_of_ty ~encode_child (K.operands v)] *)
  val encode_node :
    sort_of_ty:(ty -> Smt.sexp) -> encode_child:(t -> Smt.sexp) -> t -> Smt.sexp
end

(** The complete language: {!Base} plus the members of {!Solver_lang.S} that the
    drivers provide. A subtype of {!Solver_lang.S} (checked in [check/]), so
    [Analyses], [Bv_solver] and [Encoding] consume it unchanged. *)
module type S = sig
  include Base

  (** The pretty-printer of terms, {!Pp_v}. *)
  val pp : t Fmt.t

  (** The normaliser, {!Eval_v}: see {!Solver_lang.S.eval}. *)
  val eval : ?force:bool -> ?eval_var:(t -> Var.t -> ty -> t) -> t -> t
end

(** [Make (T) (K)] is {!Base}: no constructor is mentioned. Written by the
    architect as the reference implementation; WP3b owns it from now on. *)
module Make
    (T : Term)
    (K : Kanon_fns.Kanon_fns with type t = T.t and type ty = T.ty) :
  Base with type t = T.t and type ty = T.ty = struct
  type t = T.t
  type ty = T.ty

  module K = K

  let equal (a : t) (b : t) = Int.equal a.tag b.tag
  let compare (a : t) (b : t) = Int.compare a.tag b.tag
  let hash (a : t) = a.tag
  let unique_tag (a : t) = a.tag
  let type_of (a : t) = a.ty
  let equal_ty = T.equal_ty
  let hash_ty = T.hash_ty

  module Hashtbl = Stdlib.Hashtbl.Make (struct
    type nonrec t = t

    let equal = equal
    let hash = hash
  end)

  let v_true = K.v_true
  let v_false = K.v_false
  let of_bool = K.of_bool
  let not_ = K.b_not
  let and_ = K.b_and
  let or_ = K.b_or
  let ite = K.b_ite
  let sem_eq = K.sem_eq
  let mk_var = K.mk_var
  let t_bv n = K.t_bv (Z.of_int n)
  let bv_mk = K.mk_bv
  let bv_uleq = K.bv_leq false
  let is_literal = K.is_literal
  let is_bool (v : t) = K.is_bool_ty v.ty
  let as_var = K.as_var
  let as_bv_ty s = Option.map Z.to_int (K.as_bv_ty s)
  let as_not = K.as_not
  let as_eq = K.as_eq
  let as_and = K.as_and
  let as_or = K.as_or
  let as_ite = K.as_ite
  let as_lt = K.as_lt
  let as_leq = K.as_leq
  let as_distinct = K.as_distinct

  (* [A && B && C] iterates over [A], [B], [C], left to right *)
  let rec split_ands (v : t) (f : t -> unit) : unit =
    match K.as_and v with
    | Some (l, r) ->
        split_ands l f;
        split_ands r f
    | None -> f v

  let sure_neq = K.sure_neq

  let[@inline] implies_or_contradicts ~(q : t) ~(neg_q : t) (pc : t) :
      bool option =
    K.implies_or_contradicts q neg_q pc

  type sign = Pos | Neg

  let as_range (v : t) =
    match K.as_range v with
    | None -> None
    | Some (x, size, (side, range)) ->
        let sign : sign = match side with Inside -> Pos | Outside -> Neg in
        Some (x, Z.to_int size, (sign, range))

  let map_operands (f : t -> t) (v : t) : t =
    if not (K.maps_operands v) then v
    else
      let cs = K.operands v in
      let rec map_changed = function
        | [] -> ([], false)
        | x :: rest ->
            let x' = f x in
            let rest', changed = map_changed rest in
            (x' :: rest', changed || not (equal x x'))
      in
      (* [f] is applied left to right: [x'] is computed before [rest'] *)
      let cs', changed = map_changed cs in
      if changed then K.rebuild v cs' else v

  let iter_vars (sv : t) (f : Var.t * ty -> unit) : unit =
    let rec aux ~ignore (sv : t) : unit =
      match K.as_var sv with
      | Some (x, s) -> if Var.Set.mem x ignore then () else f (x, s)
      | None -> (
          match K.as_exists sv with
          | Some (vs, body) ->
              let ignore =
                List.fold_left
                  (fun ignore (x, _) -> Var.Set.add x ignore)
                  ignore vs
              in
              aux ~ignore body
          | None -> List.iter (aux ~ignore) (K.operands sv))
    in
    aux ~ignore:Var.Set.empty sv

  let cost (v : t) : int = Z.to_int (K.cost v)

  let random_value (ty : ty) : (unit -> t) option =
    match K.random_bound ty with
    | None -> None
    | Some bound ->
        let of_z z =
          match K.random_of_z ty z with
          | Some v -> v
          | None -> failwith "random_value: no value of this sort"
        in
        if K.is_bool_ty ty then Some (fun () -> K.of_bool (Random.bool ()))
        else Some (fun () -> of_z (Z.random_int bound))

  let encode_ty ~sort_of_ty (s : ty) : Smt.sexp =
    (K.encode_sort s) ~sort_of_ty (K.sort_operands s)

  let encode_node ~sort_of_ty ~encode_child (v : t) : Smt.sexp =
    (K.encode_head v) ~sort_of_ty ~encode_child (K.operands v)
end
