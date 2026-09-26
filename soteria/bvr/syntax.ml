(** Abstract syntax of BVR, the rule language in which the Bv_values smart
    constructors are written. *)

type ty =
  | TInt  (** mathematical integers: [Z.t] in OCaml, [Int] in Lean *)
  | TBool
  | TUnit
  | TTerm  (** svalues *)
  | TKind  (** the kind of an svalue *)
  | TSty  (** the type of an svalue *)
  | TData of string
      (** operators, enums and records: [unop], [binop], [checked], ... *)
  | TFloat  (** a concrete float literal *)
  | TVar  (** a variable identifier *)
  | TTuple of ty list
  | TOption of ty
  | TList of ty

let rec pp_ty ft = function
  | TInt -> Fmt.string ft "int"
  | TBool -> Fmt.string ft "bool"
  | TUnit -> Fmt.string ft "unit"
  | TTerm -> Fmt.string ft "t"
  | TKind -> Fmt.string ft "kind"
  | TSty -> Fmt.string ft "ty"
  | TData s -> Fmt.string ft s
  | TFloat -> Fmt.string ft "float"
  | TVar -> Fmt.string ft "var"
  | TTuple l -> Fmt.(parens (list ~sep:(any " * ") pp_ty)) ft l
  | TOption t -> Fmt.pf ft "%a option" pp_ty t
  | TList t -> Fmt.pf ft "%a list" pp_ty t

(** An argument of a constructor. [Small] integers are OCaml [int]s (widths,
    indices), as opposed to [Z.t]s; in BVR both have type [int]. *)
type arg = Arg of ty | Small

let arg_ty = function Arg t -> t | Small -> TInt

type constr = {
  c_name : string;  (** the BVR (and OCaml) name *)
  c_res : ty;
  c_args : arg list;
  c_lean : string;  (** fully qualified Lean name *)
}

let data_types =
  [
    "unop";
    "binop";
    "triop";
    "nop";
    "checked";
    "rm";
    "fp";
    "fc";
    "ext";
    "ext_ty";
  ]

let constrs : constr list =
  let mk res lean_ns l =
    List.map
      (fun (c_name, c_lean, c_args) ->
        { c_name; c_res = res; c_args; c_lean = lean_ns ^ "." ^ c_lean })
      l
  in
  let t = Arg TTerm and b = Arg TBool and d s = Arg (TData s) in
  mk TKind "Kind"
    [
      ("Var", "var", [ Arg TVar ]);
      ("Bool", "bool", [ b ]);
      ("Float", "float", [ Arg TFloat ]);
      ("Ptr", "ptr", [ t; t ]);
      ("BitVec", "bitVec", [ Arg TInt ]);
      ("Seq", "seq", [ Arg (TList TTerm) ]);
      ("Unop", "unop", [ d "unop"; t ]);
      ("Binop", "binop", [ d "binop"; t; t ]);
      ("Triop", "triop", [ d "triop"; t; t; t ]);
      ("Nop", "nop", [ d "nop"; Arg (TList TTerm) ]);
      ("Exists", "exists_", [ Arg (TList (TTuple [ TVar; TSty ])); t ]);
      ("Extension", "extension", [ d "ext" ]);
    ]
  @ mk (TData "unop") "Unop"
      [
        ("Not", "not_", []);
        ("GetPtrLoc", "getPtrLoc", []);
        ("GetPtrOfs", "getPtrOfs", []);
        ("BvOfBool", "bvOfBool", [ Small ]);
        ("BvOfFloat", "bvOfFloat", [ d "rm"; b; Small ]);
        ("FloatOfBv", "floatOfBv", [ d "rm"; b; d "fp" ]);
        ("FloatOfBvRaw", "floatOfBvRaw", [ d "fp" ]);
        ("FloatOfFloat", "floatOfFloat", [ d "rm"; d "fp" ]);
        ("BvExtract", "bvExtract", [ Small; Small ]);
        ("BvExtend", "bvExtend", [ b; Small ]);
        ("BvNot", "bvNot", []);
        ("Neg", "neg", [ b ]);
        ("FAbs", "fAbs", []);
        ("FNeg", "fNeg", []);
        ("FSqrt", "fSqrt", []);
        ("FIs", "fIs", [ d "fc" ]);
        ("FIsNeg", "fIsNeg", []);
        ("FIsPos", "fIsPos", []);
        ("FRound", "fRound", [ d "rm" ]);
      ]
  @ mk (TData "binop") "Binop"
      [
        ("And", "and_", []);
        ("Or", "or_", []);
        ("Eq", "eq", []);
        ("FEq", "fEq", []);
        ("FLeq", "fLeq", []);
        ("FLt", "fLt", []);
        ("FAdd", "fAdd", []);
        ("FSub", "fSub", []);
        ("FMul", "fMul", []);
        ("FDiv", "fDiv", []);
        ("FRem", "fRem", []);
        ("FMin", "fMin", []);
        ("FMax", "fMax", []);
        ("Add", "add", [ d "checked" ]);
        ("Sub", "sub", [ d "checked" ]);
        ("Mul", "mul", [ d "checked" ]);
        ("Div", "div", [ b ]);
        ("Rem", "rem", [ b ]);
        ("Mod", "mod_", []);
        ("AddOvf", "addOvf", [ b ]);
        ("SubOvf", "subOvf", [ b ]);
        ("MulOvf", "mulOvf", [ b ]);
        ("Lt", "lt", [ b ]);
        ("Leq", "leq", [ b ]);
        ("BvConcat", "bvConcat", []);
        ("BitAnd", "bitAnd", []);
        ("BitOr", "bitOr", []);
        ("BitXor", "bitXor", []);
        ("Shl", "shl", []);
        ("LShr", "lShr", []);
        ("AShr", "aShr", []);
      ]
  @ mk (TData "triop") "Triop" [ ("Fma", "fma", []); ("Ite", "ite", []) ]
  @ mk (TData "nop") "Nop" [ ("Distinct", "distinct", []) ]
  @ mk TSty "Ty"
      [
        ("TBool", "bool", []);
        ("TFloat", "float", [ d "fp" ]);
        ("TLoc", "loc", [ Small ]);
        ("TPointer", "pointer", [ Small ]);
        ("TSeq", "seq", [ Arg TSty ]);
        ("TBitVector", "bitVector", [ Small ]);
        ("TExtension", "extension", [ d "ext_ty" ]);
      ]
  @ mk (TData "fp") "Prec"
      [
        ("F16", "f16", []);
        ("F32", "f32", []);
        ("F64", "f64", []);
        ("F128", "f128", []);
      ]
  @ mk (TData "rm") "RM"
      [
        ("NearestTiesToEven", "nearestTiesToEven", []);
        ("Truncate", "truncate", []);
        ("Ceil", "ceil", []);
        ("Floor", "floor", []);
        ("NearestTiesToAway", "nearestTiesToAway", []);
      ]
  @ mk (TData "fc") "FClass"
      [
        ("Normal", "normal", []);
        ("Subnormal", "subnormal", []);
        ("Zero", "zero", []);
        ("Infinite", "infinite", []);
        ("NaN", "nan", []);
      ]

let find_constr name = List.find_opt (fun c -> c.c_name = name) constrs

(** Fields of the [checked] record. *)
let checked_fields = [ "signed"; "unsigned" ]

type unop = Neg | Not | Lognot

type binop = Add | Sub | Mul | Lt | Le | Gt | Ge | Eq | Ne | And | Or
and bitop = Land | Lor | Lxor | Lsl | Asr

type binop' = Arith of binop | Bit of bitop

type pat = { p : pat_desc; pty : ty; ploc : Location.t }

and pat_desc =
  | PAny
  | PVar of string
  | PAs of pat * string
  | POr of pat * pat
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
}

type fn = {
  name : string;
  params : (string * ty) list;
  ret : ty;
  spec : expr option;
      (** for rule functions, the raw term the result must refine *)
  body : expr;
  floc : Location.t;
}

type prim = { pname : string; pargs : ty list; pret : ty; oracle : bool }
type program = { prims : prim list; fns : fn list }
