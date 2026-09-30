open Soteria_std
open Hc
module Var = Symex.Var

type ty = TBool | TInt [@@deriving eq, show { with_path = false }, ord]

let t_bool = TBool
let t_int = TInt

module Nop = struct
  type t = Distinct [@@deriving eq, show { with_path = false }, ord]
end

module Unop = struct
  let equal_fpclass = ( = )
  let compare_fpclass = compare

  type t = Not [@@deriving eq, ord]

  let pp_signed ft b = Fmt.string ft (if b then "s" else "u")
  let pp ft = function Not -> Fmt.string ft "!"
end

module Binop = struct
  type t =
    (* Bool *)
    | And
    | Or
    (* Comparison *)
    | Eq
    | Leq
    | Lt
    (* Arith *)
    | Plus
    | Minus
    | Times
    | Div
    | Rem
    | Mod (* Modulo, not remainder *)
  [@@deriving eq, show { with_path = false }, ord]

  let pp ft = function
    | And -> Fmt.string ft "&&"
    | Or -> Fmt.string ft "||"
    | Eq -> Fmt.string ft "=="
    | Leq -> Fmt.string ft "<="
    | Lt -> Fmt.string ft "<"
    | Plus -> Fmt.string ft "+"
    | Minus -> Fmt.string ft "-"
    | Times -> Fmt.string ft "*"
    | Div -> Fmt.string ft "/"
    | Rem -> Fmt.string ft "rem"
    | Mod -> Fmt.string ft "mod"
end

let pp_hash_consed pp_node ft t = pp_node ft t.node
let equal_hash_consed _ t1 t2 = Int.equal t1.tag t2.tag
let compare_hash_consed _ t1 t2 = Int.compare t1.tag t2.tag

type t_kind =
  | Var of Var.t
  | Bool of bool
  | Int of Z.t [@printer Fmt.of_to_string Z.to_string]
  | Unop of Unop.t * t
  | Binop of Binop.t * t * t
  | Nop of Nop.t * t list
  | Ite of t * t * t

and t_node = { kind : t_kind; ty : ty }
and t = t_node hash_consed [@@deriving show { with_path = false }, eq, ord]

let unique_tag t = t.tag
let hash t = t.tag
let kind t = t.node.kind
let is_bool_ty = [%matches? TBool]

let rec iter_vars (sv : t) (f : Var.t * ty -> unit) : unit =
  match sv.node.kind with
  | Var v -> f (v, sv.node.ty)
  | Bool _ | Int _ -> ()
  | Binop (_, l, r) ->
      iter_vars l f;
      iter_vars r f
  | Unop (_, sv) -> iter_vars sv f
  | Nop (_, l) -> List.iter (fun sv -> iter_vars sv f) l
  | Ite (c, t, e) ->
      iter_vars c f;
      iter_vars t f;
      iter_vars e f

let pp_full ft t = pp_t_node ft t.node

let rec pp ft t =
  let open Fmt in
  match t.node.kind with
  | Var v -> pf ft "V%a" Var.pp v
  | Bool b -> pf ft "%b" b
  | Int z when Z.(z > of_int 2048 || z < of_int (-2048)) ->
      pf ft "%s" (Z.format "%#x" z)
  | Int z -> pf ft "%a" Z.pp_print z
  | Ite (c, t, e) -> pf ft "(%a ? %a : %a)" pp c pp t pp e
  | Unop (Not, { node = { kind = Binop (Eq, v1, v2); _ }; _ }) ->
      pf ft "(%a != %a)" pp v1 pp v2
  | Unop (op, v) -> pf ft "%a(%a)" Unop.pp op pp v
  | Binop (op, v1, v2) -> pf ft "(%a %a %a)" pp v1 Binop.pp op pp v2
  | Nop (op, l) -> (
      let rec aux = function
        | acc, [] -> acc
        | Some l, { node = { kind = Var v; _ }; _ } :: rest ->
            aux (Some (Var.to_int v :: l), rest)
        | _, _ -> None
      in
      let range =
        aux (Some [], l)
        |> Option.bind (fun l ->
            let l = List.sort Int.compare l in
            let min = List.hd l in
            let max = List.hd @@ List.rev l in
            if max - min + 1 = List.length l then Some (min, max) else None)
      in
      match range with
      | Some (min, max) -> pf ft "%a(V|%d-%d|)" Nop.pp op min max
      | None -> pf ft "%a(%a)" Nop.pp op (list ~sep:comma pp) l)

let[@inline] equal a b = Int.equal a.tag b.tag
let[@inline] compare a b = Int.compare a.tag b.tag

module Hcons = Hc.Make (struct
  type t = t_node

  let equal = equal_t_node

  (* We could do a lot more efficient in terms of hashing probably, if this ever
     becomes a bottleneck. *)
  let hash { kind; ty } =
    let hty = Hashtbl.hash ty in
    match kind with
    | Var _ | Bool _ | Int _ -> Hashtbl.hash (kind, hty)
    | Unop (op, v) -> Hashtbl.hash (op, v.tag, hty)
    | Binop (op, l, r) -> Hashtbl.hash (op, l.tag, r.tag, hty)
    | Nop (op, l) -> Hashtbl.hash (op, List.map (fun sv -> sv.tag) l, hty)
    | Ite (c, t, e) -> Hashtbl.hash (c.tag, t.tag, e.tag, hty)
end)

module Hashtbl = Hashtbl.Make (struct
  type nonrec t = t

  let equal = equal
  let hash = hash
end)

let ( <| ) kind ty : t = Hcons.hashcons { kind; ty }
let mk_var v ty = Var v <| ty

(** {2 Booleans} *)

let v_true = Bool true <| TBool
let v_false = Bool false <| TBool

let to_bool t =
  if equal t v_true then Some true
  else if equal t v_false then Some false
  else None

let of_bool b =
  (* avoid re-alloc and re-hashconsing *)
  if b then v_true else v_false

let rec split_ands (sv : t) (f : t -> unit) : unit =
  match sv.node.kind with
  | Binop (And, s1, s2) ->
      split_ands s1 f;
      split_ands s2 f
  | _ -> f sv

(** {2 Integers} *)

let int_z z = Int z <| TInt
let int i = int_z (Z.of_int i)

let nonzero_z z =
  if Z.equal Z.zero z then raise (Invalid_argument "nonzero_z") else int_z z

let nonzero x = if x = 0 then raise (Invalid_argument "nonzero") else int x
let zero = int_z Z.zero
let one = int_z Z.one

(** {2 Simplification rules}

    The simplifying smart constructors are generated from the rules in
    [rules/*.bvr]; see [soteria/bvr]. *)

module Prims = struct
  let node = ( <| )
  let equal_ty = equal_ty
  let zcompare = Z.compare
  let zequal = Z.equal
  let v_true = v_true
  let v_false = v_false
  let int_z = int_z
  let zero = zero
  let one = one
  let var_equal = Var.equal
  let tdiv = Z.div
  let trem = Z.rem
  let divisible = Z.divisible
end

module R = struct
  module P = Prims

  [%%include_file "svalue_rules.gen.ml"]
end

let sure_neq = R.sure_neq
let mk_commut_binop = R.mk_commut_binop

(** {2 Boolean operations} *)

let and_ = R.and_
let or_ = R.or_
let conj l = List.fold_left and_ v_true l
let not = R.not_
let distinct = R.distinct
let distinct_seq s = distinct (List.of_seq s)
let ite = R.ite

(** {2 Integer operations} *)

let add = R.add
let sub = R.sub
let mul = R.mul
let div = R.div
let is_mod = R.is_mod
let rem = R.rem
let mod_ = R.mod_
let neg = R.neg

(* {2 Equality, comparison, int-bool conversions} *)

let lt = R.lt
let leq = R.leq
let geq v1 v2 = leq v2 v1
let gt v1 v2 = lt v2 v1
let sem_eq = R.sem_eq
let sem_eq_untyped = R.sem_eq_untyped

(** {2 General constructors} *)

let mk_unop : Unop.t -> t -> t = function Not -> not

let mk_binop : Binop.t -> t -> t -> t = function
  | And -> and_
  | Or -> or_
  | Eq -> sem_eq
  | Leq -> leq
  | Lt -> lt
  | Plus -> add
  | Minus -> sub
  | Times -> mul
  | Div -> div
  | Rem -> rem
  | Mod -> mod_

let mk_nop : Nop.t -> t list -> t = function Distinct -> distinct

(** {2 Infix operators} *)

module Infix = struct
  let int_z = int_z
  let int = int
  let ( ==@ ) = sem_eq
  let ( ==?@ ) = sem_eq_untyped
  let ( >@ ) = gt
  let ( >=@ ) = geq
  let ( <@ ) = lt
  let ( <=@ ) = leq
  let ( &&@ ) = and_
  let ( ||@ ) = or_
  let ( +@ ) = add
  let ( -@ ) = sub
  let ( ~- ) = neg
  let ( *@ ) = mul
  let ( /@ ) = div
  let ( %@ ) = mod_
end

module Syntax = struct
  module Sym_int_syntax = struct
    let mk_nonzero = nonzero
    let[@inline] zero () = zero
    let[@inline] one () = one
  end
end
