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
                                 Eval.Make (Base) : eval
                                         |
            |  Lang_make.Make (T) (K)     |          (lang_make.ml)
            v                             v
      Value_lang.S = Base + eval   (a subtype of Solver_lang.S)
            |
            v
      Svalue_sugar, Expr, Typed, and Analyses / Bv_solver / Encoding
    v}

    {!Base} and {!S} differ in [eval] only: it is produced by the generic
    evaluator, which consumes {!Base} (and could not consume {!S} that contains
    it). *)

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

(** What the generic drivers consume ({!Eval}): the identity of terms, the
    functions of {!Kanon_fns} ([K]), and the members of {!Solver_lang.S} that
    need nothing more than these. *)
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

  (** {2 The members of [Solver_lang.S], except [eval]}

      See {!Solver_lang.S} for their documentation. *)

  (** [= K.pp] *)
  val pp : t Fmt.t

  val v_true : t
  val v_false : t
  val of_bool : bool -> t
  val not_ : t -> t
  val and_ : t -> t -> t
  val or_ : t -> t -> t
  val ite : t -> t -> t -> t
  val sem_eq : t -> t -> t
  val mk_var : Var.t -> ty -> t

  (** [= K.Bitvec.t_bitvector n] *)
  val t_bv : int -> ty

  (** [= K.mk_bv] *)
  val bv_mk : int -> Z.t -> t

  (** [= K.Bitvec.leq false] *)
  val bv_uleq : t -> t -> t

  val is_literal : t -> bool

  (** [= K.Bool.is_tbool (type_of v)] *)
  val is_bool : t -> bool

  val as_var : t -> (Var.t * ty) option

  (** [= K.Bitvec.as_tbitvector s] *)
  val as_bv_ty : ty -> int option

  val as_not : t -> t option
  val as_eq : t -> (t * t) option
  val as_and : t -> (t * t) option
  val as_or : t -> (t * t) option
  val as_ite : t -> (t * t * t) option
  val as_lt : t -> (t * t) option
  val as_leq : t -> (t * t) option
  val as_distinct : t -> t list option

  (** Via [K.Bool.as_and], with no list: the old [Bool.split_ands]. *)
  val split_ands : t -> t Iter.t

  val sure_neq : t -> t -> bool

  (** [= K.View.implies_or_contradicts q neg_q pc]; keep it [[@inline]]. *)
  val implies_or_contradicts : q:t -> neg_q:t -> t -> bool option

  type sign = Pos | Neg

  (** [K.View.as_range], with [Inside] for [Pos], [Outside] for [Neg] and the
      size as an [int]. *)
  val as_range : t -> (Var.t * int * (sign * (Z.t * Z.t))) option

  (** The children of [v], left to right ([K.iter_children]). *)
  val children : t -> t list

  (** [f] applied to the children of [v], left to right, and [v] rebuilt from
      them with [K.map_children] if [force] or one changed (physically); [v]
      itself otherwise, and if it has no children. *)
  val map_children_changed : force:bool -> (t -> t) -> t -> t

  (** The old [map_operands]: [map_children_changed ~force:false f v] if
      [K.View.maps_operands v], else [v] itself. *)
  val map_operands : (t -> t) -> t -> t

  (** Replaces [Svalue.iter_vars] ([svalue.ml:71-93]): the free variables,
      binder aware, via [K.Core.as_var], [K.Exists.as_exists] and
      [K.iter_children], left to right. *)
  val iter_vars : t -> (Var.t * ty -> unit) -> unit

  (** [K.View.head_cost v], plus the costs of the children of [v] if
      [K.View.costs_operands v] *)
  val cost : t -> int

  (** From [K.View.random_bound] and [K.View.random_of_z], see there. *)
  val random_value : ty -> (unit -> t) option

  (** [= (K.View.encode_sort ty) ~sort_of_ty (K.View.sort_operands ty)] *)
  val encode_ty : sort_of_ty:(ty -> Smt.sexp) -> ty -> Smt.sexp

  (** [= (K.View.encode_head v) ~sort_of_ty ~encode_child cs], [cs] the children
      of [v] *)
  val encode_node :
    sort_of_ty:(ty -> Smt.sexp) -> encode_child:(t -> Smt.sexp) -> t -> Smt.sexp
end

(** The complete language: {!Base} plus the members of {!Solver_lang.S} that the
    drivers provide. A subtype of {!Solver_lang.S} (checked in [check/]), so
    [Analyses], [Bv_solver] and [Encoding] consume it unchanged. *)
module type S = sig
  include Base

  (** The normaliser, {!Eval}: see {!Solver_lang.S.eval}. *)
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

  let pp = K.pp
  let v_true = K.v_true
  let v_false = K.v_false
  let of_bool = K.Bool.of_bool
  let not_ = K.Bool.not_
  let and_ = K.Bool.and_
  let or_ = K.Bool.or_
  let ite = K.Bool.ite
  let sem_eq = K.Bool.eq
  let mk_var = K.mk_var
  let t_bv n = K.Bitvec.t_bitvector n
  let bv_mk = K.mk_bv
  let bv_uleq = K.Bitvec.leq false
  let is_literal = K.View.is_literal
  let is_bool (v : t) = K.Bool.is_tbool v.ty
  let as_var (v : t) = Option.map (fun x -> (x, v.ty)) (K.Core.as_var v)
  let as_bv_ty = K.Bitvec.as_tbitvector
  let as_not = K.Bool.as_not
  let as_eq = K.Bool.as_eq
  let as_and = K.Bool.as_and
  let as_or = K.Bool.as_or
  let as_ite = K.Bool.as_ite
  let as_lt v = Option.map (fun (_, l, r) -> (l, r)) (K.Bitvec.as_lt v)
  let as_leq v = Option.map (fun (_, l, r) -> (l, r)) (K.Bitvec.as_leq v)
  let as_distinct = K.Bool.as_distinct

  (* [A && B && C] iterates over [A], [B], [C], left to right *)
  let rec split_ands (v : t) (f : t -> unit) : unit =
    match K.Bool.as_and v with
    | Some (l, r) ->
        split_ands l f;
        split_ands r f
    | None -> f v

  let sure_neq = K.Bool.sure_neq

  let[@inline] implies_or_contradicts ~(q : t) ~(neg_q : t) (pc : t) :
      bool option =
    K.View.implies_or_contradicts q neg_q pc

  type sign = Pos | Neg

  let as_range (v : t) =
    match K.View.as_range v with
    | None -> None
    | Some (x, size, (side, range)) ->
        let sign : sign = match side with Inside -> Pos | Outside -> Neg in
        Some (x, Z.to_int size, (sign, range))

  (* the children of [v], left to right *)
  let children (v : t) : t list =
    let cs = ref [] in
    K.iter_children (fun c -> cs := c :: !cs) v;
    List.rev !cs

  let map_children_changed ~force (f : t -> t) (v : t) : t =
    let changed = ref false in
    let cs = ref [] in
    K.iter_children
      (fun c ->
        let c' = f c in
        if c' != c then changed := true;
        cs := c' :: !cs)
      v;
    match !cs with
    | [] -> v
    | _ when not (force || !changed) -> v
    | rev_cs ->
        (* [map_children] replaces the children in the order of
           [iter_children] *)
        let cs = ref (List.rev rev_cs) in
        K.map_children
          (fun _ ->
            match !cs with
            | c :: rest ->
                cs := rest;
                c
            | [] -> assert false)
          v

  let map_operands (f : t -> t) (v : t) : t =
    if not (K.View.maps_operands v) then v
    else map_children_changed ~force:false f v

  let iter_vars (sv : t) (f : Var.t * ty -> unit) : unit =
    let rec aux ~ignore (sv : t) : unit =
      match K.Core.as_var sv with
      | Some x -> if Var.Set.mem x ignore then () else f (x, sv.ty)
      | None -> (
          match K.Exists.as_exists sv with
          | Some (vs, body) ->
              let ignore =
                List.fold_left
                  (fun ignore (x, _) -> Var.Set.add x ignore)
                  ignore vs
              in
              aux ~ignore body
          | None -> K.iter_children (aux ~ignore) sv)
    in
    aux ~ignore:Var.Set.empty sv

  let rec cost (v : t) : int =
    let c = Z.to_int (K.View.head_cost v) in
    if K.View.costs_operands v then (
      let c = ref c in
      K.iter_children (fun x -> c := !c + cost x) v;
      !c)
    else c

  let random_value (ty : ty) : (unit -> t) option =
    match K.View.random_bound ty with
    | None -> None
    | Some bound ->
        let of_z z =
          match K.View.random_of_z ty z with
          | Some v -> v
          | None -> failwith "random_value: no value of this sort"
        in
        if K.Bool.is_tbool ty then
          Some (fun () -> K.Bool.of_bool (Random.bool ()))
        else Some (fun () -> of_z (Z.random_int bound))

  let encode_ty ~sort_of_ty (s : ty) : Smt.sexp =
    (K.View.encode_sort s) ~sort_of_ty (K.View.sort_operands s)

  let encode_node ~sort_of_ty ~encode_child (v : t) : Smt.sexp =
    (K.View.encode_head v) ~sort_of_ty ~encode_child (children v)
end
