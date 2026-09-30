(** Abstract syntax of BVR, the rule language in which the Bv_values smart
    constructors are written. *)

type ty =
  | TInt  (** mathematical integers: [Z.t] in OCaml, [Int] in Lean *)
  | TBv  (** a bit-vector value, which knows its width *)
  | TBool
  | TUnit
  | TTerm  (** svalues *)
  | TKind  (** the kind of an svalue *)
  | TSty  (** the type of an svalue *)
  | TData of string
      (** the other types declared by the language: operators, enums, records
          and abstract types *)
  | TVar  (** a variable identifier *)
  | TTuple of ty list
  | TOption of ty
  | TList of ty

let rec pp_ty ft = function
  | TInt -> Fmt.string ft "int"
  | TBv -> Fmt.string ft "bv"
  | TBool -> Fmt.string ft "bool"
  | TUnit -> Fmt.string ft "unit"
  | TTerm -> Fmt.string ft "t"
  | TKind -> Fmt.string ft "kind"
  | TSty -> Fmt.string ft "ty"
  | TData s -> Fmt.string ft s
  | TVar -> Fmt.string ft "var"
  | TTuple l -> Fmt.(parens (list ~sep:(any " * ") pp_ty)) ft l
  | TOption t -> Fmt.pf ft "%a option" pp_ty t
  | TList t -> Fmt.pf ft "%a list" pp_ty t

(** An argument of a constructor. [Small] integers are OCaml [int]s (widths,
    indices), as opposed to [Z.t]s; in BVR both have type [int]. *)
type arg = Arg of ty | Small

let arg_ty = function Arg t -> t | Small -> TInt

type constr = {
  c_name : string;  (** the BVR (and OCaml and Lean) name *)
  c_res : ty;
  c_args : arg list;
}

(** A type declared by the language: [kind], [ty], operators, enums, records and
    abstract types. *)
type decl = {
  d_name : string;
  d_ocaml : string;  (** the OCaml type *)
  d_eq : bool;  (** whether [=] and [<>] are allowed at this type *)
  d_fields : (string * ty) list;  (** the fields of a record type, in order *)
}

(** An operator on terms, e.g. [+]: in expressions it calls its smart
    constructor [smart], with the leading arguments [pre]; in patterns it
    matches its [node], with any parameters; on bit-vector values it is the
    primitive [on_bv]. *)
type operator = {
  sym : string;
      (** as parsed: ["+"], ["&&"], ...; ["~-"], ["lognot"] and ["not"] for the
          prefix [-], [~] and [not] *)
  arity : int;
  node : string;
  smart : string;
  pre : Ppxlib.expression list;
  on_bv : string option;
}

(** The language that the rules are written in: its types, constructors and
    operators, as declared in its [.bvl] file. *)
type lang = {
  decls : decl list;
  constrs : constr list;
  commutative : string list;
      (** the binary operators whose operands commute, which patterns match in
          either order: in [[@cases]] functions, [[@comm]] may only swap theirs,
          and the swapped alternative is proved from the other by commutativity
      *)
  node_kinds : string list;
      (** the kind constructors whose first argument is an operator, which then
          stands for the node: [Add (c, l, r)] for [Binop (Add c, l, r)] *)
  lit_bool : string option;  (** the kind constructor of boolean literals *)
  lit_bv : string option;  (** the kind constructor of bit-vector literals *)
  operators : operator list;
}

let lang =
  ref
    {
      decls = [];
      constrs = [];
      commutative = [];
      node_kinds = [];
      lit_bool = None;
      lit_bv = None;
      operators = [];
    }

let find_constr name = List.find_opt (fun c -> c.c_name = name) !lang.constrs
let find_decl name = List.find_opt (fun d -> d.d_name = name) !lang.decls

(** The name of the declaration of a type of the language. *)
let decl_name = function
  | TKind -> Some "kind"
  | TSty -> Some "ty"
  | TData s -> Some s
  | _ -> None

let decl_of_ty t =
  match Option.bind (decl_name t) find_decl with
  | Some d -> d
  | None -> Fmt.failwith "type %a is not declared by the language" pp_ty t

let find_operator ~arity sym =
  List.find_opt (fun o -> o.sym = sym && o.arity = arity) !lang.operators

let is_commutative name = List.mem name !lang.commutative

type unop = Neg | Not | Lognot

type binop = Add | Sub | Mul | Lt | Le | Gt | Ge | Eq | Ne | And | Or
and bitop = Land | Lor | Lxor | Lsl | Asr

type binop' = Arith of binop | Bit of bitop

type pat = {
  p : pat_desc;
  pty : ty;
  ploc : Location.t;
  pid : int;
      (** unique to the pattern node, and shared by its copy in the swapped
          alternative of a [[@comm]] pattern *)
}

and pat_desc =
  | PAny
  | PVar of string
  | PAs of pat * string
  | POr of pat * pat
  | PComm of pat * pat  (** [p [@comm]]: [p], or [p] with operands swapped *)
  | PInt of Z.t
  | PBool of bool
  | PUnit
  | PTuple of pat list
  | PConstr of constr * pat list
      (** a constructor of kind type, matched against a term, matches its kind
      *)
  | PSome of pat
  | PNone
  | PNil
  | PCons of pat * pat
  | PRecord of (string * pat) list  (** partial [checked] records *)
  | PLit of string
      (** in [[@cases]] functions, [BitVec x]: a bit-vector literal, whose value
          is bound to [x] as a [bv] *)

type expr = { e : expr_desc; ety : ty; eloc : Location.t }

and expr_desc =
  | EVar of string
  | EInt of Z.t
  | EBool of bool
  | EUnit
  | EConstr of constr * expr list
  | ENode of expr * expr  (** [kind <| ty] *)
  | ECall of string * expr list  (** global function or primitive *)
  | ELocalCall of string * expr list
  | EUnop of unop * expr
  | EBinop of binop' * expr * expr
  | EIf of expr * expr * expr
  | ELet of pat * expr * expr
  | ELetFun of string * (string * ty) list * expr * expr
  | EMatch of expr list * case list
  | ETuple of expr list
  | ESome of expr
  | ENone
  | ENil
  | ECons of expr * expr
  | ERecord of (string * expr) list
  | EField of expr * string
  | EAssert of expr * expr

and case = {
  pat : pat;  (** of tuple type when there are several scrutinees *)
  guard : expr option;
  body : expr;
  rule : string option;
  cloc : Location.t;
  alt : (int * int * bool * string) list;
      (** the alternative of the source case: for each or-pattern (and [[@comm]]
          pattern, flagged) taken, its [pid], the side chosen, and a name for
          that side (see [Check.alternatives]) *)
}

type fn = {
  name : string;
  params : (string * ty) list;
  ret : ty;
  spec : expr option;
      (** for rule functions, the raw term the result must refine *)
  cases : bool;
      (** [[@cases]]: literals are bound as [bv]s, and the rules are proved per
          alternative *)
  body : expr;
  floc : Location.t;
}

type prim = { pname : string; pargs : ty list; pret : ty; oracle : bool }
type program = { prims : prim list; fns : fn list }
