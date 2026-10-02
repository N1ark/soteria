(** The neutral AST [Tm] of the differential harness, and the types shared by
    both sides (sorts, node names, views).

    [Tm.t] is built once, then replayed through the public smart constructors of
    each simplifier (see {!Side}). Its operators are the {e public entry points}
    (e.g. [Add] with a [checked] flag, [Gt] which the old API defines as [Lt]
    with swapped operands), not raw nodes. *)

module FP = Soteria.Bv_values.Svalue.FloatPrecision
module RM = Soteria.Bv_values.Svalue.RoundingMode
module FC = Soteria.Bv_values.Svalue.FloatClass

type prec = FP.t = F16 | F32 | F64 | F128

type sort =
  | SBool
  | SBv of int
  | SLoc of int
  | SPtr of int
  | SFloat of prec
  | SSeq of sort

let rec pp_sort ft = function
  | SBool -> Fmt.string ft "bool"
  | SBv n -> Fmt.pf ft "bv%d" n
  | SLoc n -> Fmt.pf ft "loc%d" n
  | SPtr n -> Fmt.pf ft "ptr%d" n
  | SFloat p -> Fmt.pf ft "%a" FP.pp p
  | SSeq s -> Fmt.pf ft "seq(%a)" pp_sort s

let show_sort s = Fmt.str "%a" pp_sort s

(** [(signed, unsigned)]: in which signedness(es) the operation is known not to
    overflow. *)
type checked = bool * bool

(** The nodes of the term language, as seen through a {!view}: the union of the
    old [Unop/Binop/Triop/Nop] constructors, which are the new [Op1/Op2/Op3/OpN]
    ones. Parameters are compared exactly (structural equality). *)
type node =
  (* unary *)
  | N_not
  | N_ptr_loc
  | N_ptr_ofs
  | N_bv_of_bool of int
  | N_bv_of_float of RM.t * bool * int
  | N_float_of_bv of RM.t * bool * prec
  | N_float_of_bv_raw of prec
  | N_float_of_float of RM.t * prec
  | N_extract of int * int
  | N_extend of bool * int
  | N_bvnot
  | N_neg of bool
  | N_fabs
  | N_fneg
  | N_fsqrt
  | N_fis of FC.t
  | N_fisneg
  | N_fispos
  | N_fround of RM.t
  (* binary *)
  | N_and
  | N_or
  | N_eq
  | N_feq
  | N_fleq
  | N_flt
  | N_fadd
  | N_fsub
  | N_fmul
  | N_fdiv
  | N_frem
  | N_fmin
  | N_fmax
  | N_add of checked
  | N_sub of checked
  | N_mul of checked
  | N_div of bool
  | N_rem of bool
  | N_mod
  | N_addovf of bool
  | N_subovf of bool
  | N_mulovf of bool
  | N_lt of bool
  | N_leq of bool
  | N_concat
  | N_bitand
  | N_bitor
  | N_bitxor
  | N_shl
  | N_lshr
  | N_ashr
  (* ternary *)
  | N_fma
  | N_ite
  (* n-ary *)
  | N_distinct

(** The nodes whose smart constructors order their operands by tag
    ([mk_commut_binop] in the old rules). *)
let is_comm = function
  | N_and | N_or | N_eq | N_feq | N_add _ | N_mul _ | N_addovf _ | N_mulovf _
  | N_bitand | N_bitor | N_bitxor ->
      true
  | _ -> false

let pp_b ft b = Fmt.string ft (if b then "s" else "u")

let pp_ck ft (s, u) =
  Fmt.string ft
    (match (s, u) with
    | false, false -> ""
    | true, false -> "cks"
    | false, true -> "cku"
    | true, true -> "ck")

let pp_node ft = function
  | N_not -> Fmt.string ft "not"
  | N_ptr_loc -> Fmt.string ft "loc"
  | N_ptr_ofs -> Fmt.string ft "ofs"
  | N_bv_of_bool n -> Fmt.pf ft "b2bv[%d]" n
  | N_bv_of_float (rm, s, n) -> Fmt.pf ft "f2%abv[%a,%d]" pp_b s RM.pp rm n
  | N_float_of_bv (rm, s, p) ->
      Fmt.pf ft "%abv2f[%a,%a]" pp_b s RM.pp rm FP.pp p
  | N_float_of_bv_raw p -> Fmt.pf ft "bv2f[%a]" FP.pp p
  | N_float_of_float (rm, p) -> Fmt.pf ft "f2f[%a,%a]" RM.pp rm FP.pp p
  | N_extract (i, j) -> Fmt.pf ft "extract[%d-%d]" i j
  | N_extend (s, k) -> Fmt.pf ft "extend[%a%d]" pp_b s k
  | N_bvnot -> Fmt.string ft "bvnot"
  | N_neg c -> Fmt.pf ft "neg%s" (if c then "ck" else "")
  | N_fabs -> Fmt.string ft "fabs"
  | N_fneg -> Fmt.string ft "fneg"
  | N_fsqrt -> Fmt.string ft "fsqrt"
  | N_fis fc -> Fmt.pf ft "fis(%a)" FC.pp fc
  | N_fisneg -> Fmt.string ft "fisneg"
  | N_fispos -> Fmt.string ft "fispos"
  | N_fround rm -> Fmt.pf ft "fround(%a)" RM.pp rm
  | N_and -> Fmt.string ft "and"
  | N_or -> Fmt.string ft "or"
  | N_eq -> Fmt.string ft "eq"
  | N_feq -> Fmt.string ft "feq"
  | N_fleq -> Fmt.string ft "fleq"
  | N_flt -> Fmt.string ft "flt"
  | N_fadd -> Fmt.string ft "fadd"
  | N_fsub -> Fmt.string ft "fsub"
  | N_fmul -> Fmt.string ft "fmul"
  | N_fdiv -> Fmt.string ft "fdiv"
  | N_frem -> Fmt.string ft "frem"
  | N_fmin -> Fmt.string ft "fmin"
  | N_fmax -> Fmt.string ft "fmax"
  | N_add c -> Fmt.pf ft "add%a" pp_ck c
  | N_sub c -> Fmt.pf ft "sub%a" pp_ck c
  | N_mul c -> Fmt.pf ft "mul%a" pp_ck c
  | N_div s -> Fmt.pf ft "div%a" pp_b s
  | N_rem s -> Fmt.pf ft "rem%a" pp_b s
  | N_mod -> Fmt.string ft "mod"
  | N_addovf s -> Fmt.pf ft "add%a_ovf" pp_b s
  | N_subovf s -> Fmt.pf ft "sub%a_ovf" pp_b s
  | N_mulovf s -> Fmt.pf ft "mul%a_ovf" pp_b s
  | N_lt s -> Fmt.pf ft "lt%a" pp_b s
  | N_leq s -> Fmt.pf ft "leq%a" pp_b s
  | N_concat -> Fmt.string ft "concat"
  | N_bitand -> Fmt.string ft "bitand"
  | N_bitor -> Fmt.string ft "bitor"
  | N_bitxor -> Fmt.string ft "bitxor"
  | N_shl -> Fmt.string ft "shl"
  | N_lshr -> Fmt.string ft "lshr"
  | N_ashr -> Fmt.string ft "ashr"
  | N_fma -> Fmt.string ft "fma"
  | N_ite -> Fmt.string ft "ite"
  | N_distinct -> Fmt.string ft "distinct"

(** The name of a node's constructor, parameters dropped (coverage keys). *)
let node_name n =
  let s = Fmt.str "%a" pp_node n in
  match String.index_opt s '[' with
  | Some i -> String.sub s 0 i
  | None -> (
      match String.index_opt s '(' with Some i -> String.sub s 0 i | None -> s)

(** One-level structural view of a term of either side. [Ptr] and [Seq] are
    dedicated constructors in the old kinds; in the new language they are
    ordinary nodes, which the adapters of the new side map to these. *)
type 'a view =
  | VVar of int * sort
  | VBool of bool
  | VBv of int * Z.t
  | VLoc of int * Z.t
  | VFloat of prec * Z.t  (** the IEEE bits *)
  | VPtr of 'a * 'a
  | VSeq of 'a list
  | VNode of node * 'a list
  | VExists of (int * sort) list * 'a

(** Public entry points (see the module comment). Argument counts in comments;
    all argument terms are plain [Tm.t]. *)
type op =
  (* bool *)
  | And (* 2 *)
  | Or
  | Not (* 1 *)
  | Ite (* 3 *)
  | SemEq (* 2 *)
  | SemEqUntyped
  | Distinct (* n *)
  | AndLazy (* 2: the rhs is only built when the lhs is not false *)
  | OrLazy
  | Conj (* n: [fold and_ v_true] *)
  | Exists1 of sort (* 2: [not_in; body], the body uses [Bound] *)
  (* bitvec *)
  | BvAdd of checked
  | BvSub of checked
  | BvMul of checked
  | BvDiv of bool
  | BvRem of bool
  | BvMod
  | BvNeg of bool
  | BvAddOvf of bool
  | BvSubOvf of bool
  | BvMulOvf of bool
  | BvNegOvf
  | BvLt of bool
  | BvLeq of bool
  | BvGt of bool
  | BvGeq of bool
  | BvConcat
  | BvExtend of bool * int
  | BvExtract of int * int
  | BvAnd
  | BvOr
  | BvXor
  | BvShl
  | BvLShr
  | BvAShr
  | BvNot
  | BvOfBool of int
  | BvToBool
  | BvNotBool
  | BvOfFloat of RM.t * bool * int
  | BvToFloat of RM.t * bool * prec
  | BvToFloatRaw
  (* float *)
  | FEq
  | FLt
  | FLeq
  | FGt
  | FGeq
  | FAdd
  | FSub
  | FMul
  | FDiv
  | FRem
  | FFmod
  | FFmodOfRem (* 3 *)
  | FFma (* 3 *)
  | FMin
  | FMax
  | FMinimum
  | FMaximum
  | FAbs
  | FNeg
  | FSqrt
  | FIsFloatClass of FC.t
  | FCast of RM.t * prec
  | FRound of RM.t
  | FIsNegative
  | FIsPositive
  (* pointers *)
  | PtrMk
  | PtrLoc
  | PtrOfs
  | PtrAddOfs
  | PtrNull of int (* 0 *)
  | PtrIsNullLoc
  | PtrIsNull
  | PtrIsAtNullLoc
  (* sequences *)
  | SeqMk of sort (* n; the sort is the sequence sort *)

type t =
  | Var of int * sort
  | Bool of bool
  | Bv of int * Z.t
  | Loc of int * Z.t
  | Float of prec * Z.t  (** the IEEE bits *)
  | Bound of int * sort  (** the [i]th enclosing [Exists1] binder *)
  | Op of op * t list

let op_name = function
  | And -> "and"
  | Or -> "or"
  | Not -> "not"
  | Ite -> "ite"
  | SemEq -> "sem_eq"
  | SemEqUntyped -> "sem_eq_untyped"
  | Distinct -> "distinct"
  | AndLazy -> "and_lazy"
  | OrLazy -> "or_lazy"
  | Conj -> "conj"
  | Exists1 _ -> "exists_1"
  | BvAdd _ -> "bv_add"
  | BvSub _ -> "bv_sub"
  | BvMul _ -> "bv_mul"
  | BvDiv _ -> "bv_div"
  | BvRem _ -> "bv_rem"
  | BvMod -> "bv_mod"
  | BvNeg _ -> "bv_neg"
  | BvAddOvf _ -> "bv_add_overflows"
  | BvSubOvf _ -> "bv_sub_overflows"
  | BvMulOvf _ -> "bv_mul_overflows"
  | BvNegOvf -> "bv_neg_overflows"
  | BvLt _ -> "bv_lt"
  | BvLeq _ -> "bv_leq"
  | BvGt _ -> "bv_gt"
  | BvGeq _ -> "bv_geq"
  | BvConcat -> "bv_concat"
  | BvExtend _ -> "bv_extend"
  | BvExtract _ -> "bv_extract"
  | BvAnd -> "bv_and"
  | BvOr -> "bv_or"
  | BvXor -> "bv_xor"
  | BvShl -> "bv_shl"
  | BvLShr -> "bv_lshr"
  | BvAShr -> "bv_ashr"
  | BvNot -> "bv_not"
  | BvOfBool _ -> "bv_of_bool"
  | BvToBool -> "bv_to_bool"
  | BvNotBool -> "bv_not_bool"
  | BvOfFloat _ -> "bv_of_float"
  | BvToFloat _ -> "bv_to_float"
  | BvToFloatRaw -> "bv_to_float_raw"
  | FEq -> "float_eq"
  | FLt -> "float_lt"
  | FLeq -> "float_leq"
  | FGt -> "float_gt"
  | FGeq -> "float_geq"
  | FAdd -> "float_add"
  | FSub -> "float_sub"
  | FMul -> "float_mul"
  | FDiv -> "float_div"
  | FRem -> "float_rem"
  | FFmod -> "float_fmod"
  | FFmodOfRem -> "float_fmod_of_rem"
  | FFma -> "float_fma"
  | FMin -> "float_min"
  | FMax -> "float_max"
  | FMinimum -> "float_minimum"
  | FMaximum -> "float_maximum"
  | FAbs -> "float_abs"
  | FNeg -> "float_neg"
  | FSqrt -> "float_sqrt"
  | FIsFloatClass _ -> "float_is_floatclass"
  | FCast _ -> "float_cast"
  | FRound _ -> "float_round"
  | FIsNegative -> "float_is_negative"
  | FIsPositive -> "float_is_positive"
  | PtrMk -> "ptr_mk"
  | PtrLoc -> "ptr_loc"
  | PtrOfs -> "ptr_ofs"
  | PtrAddOfs -> "ptr_add_ofs"
  | PtrNull _ -> "ptr_null"
  | PtrIsNullLoc -> "ptr_is_null_loc"
  | PtrIsNull -> "ptr_is_null"
  | PtrIsAtNullLoc -> "ptr_is_at_null_loc"
  | SeqMk _ -> "seq_mk"

(** The operator with its parameters, for printing reproductions. *)
let pp_op ft o =
  let b = pp_b and ck = pp_ck in
  let base = op_name o in
  match o with
  | Exists1 s -> Fmt.pf ft "%s[%a]" base pp_sort s
  | BvAdd c | BvSub c | BvMul c -> Fmt.pf ft "%s[%a]" base ck c
  | BvDiv s
  | BvRem s
  | BvAddOvf s
  | BvSubOvf s
  | BvMulOvf s
  | BvLt s
  | BvLeq s
  | BvGt s
  | BvGeq s ->
      Fmt.pf ft "%s[%a]" base b s
  | BvNeg c -> Fmt.pf ft "%s[%b]" base c
  | BvExtend (s, k) -> Fmt.pf ft "%s[%a,%d]" base b s k
  | BvExtract (i, j) -> Fmt.pf ft "%s[%d,%d]" base i j
  | BvOfBool n -> Fmt.pf ft "%s[%d]" base n
  | BvOfFloat (rm, s, n) -> Fmt.pf ft "%s[%a,%a,%d]" base RM.pp rm b s n
  | BvToFloat (rm, s, p) -> Fmt.pf ft "%s[%a,%a,%a]" base RM.pp rm b s FP.pp p
  | FIsFloatClass fc -> Fmt.pf ft "%s[%a]" base FC.pp fc
  | FCast (rm, p) -> Fmt.pf ft "%s[%a,%a]" base RM.pp rm FP.pp p
  | FRound rm -> Fmt.pf ft "%s[%a]" base RM.pp rm
  | PtrNull n -> Fmt.pf ft "%s[%d]" base n
  | SeqMk s -> Fmt.pf ft "%s[%a]" base pp_sort s
  | _ -> Fmt.string ft base

let rec pp ft = function
  | Var (i, s) -> Fmt.pf ft "v%d:%a" i pp_sort s
  | Bool b -> Fmt.bool ft b
  | Bv (n, z) -> Fmt.pf ft "0x%s:bv%d" (Z.format "%x" z) n
  | Loc (n, z) -> Fmt.pf ft "loc0x%s:loc%d" (Z.format "%x" z) n
  | Float (p, z) -> Fmt.pf ft "f0x%s:%a" (Z.format "%x" z) FP.pp p
  | Bound (i, s) -> Fmt.pf ft "bound%d:%a" i pp_sort s
  | Op (o, []) -> Fmt.pf ft "(%a)" pp_op o
  | Op (o, l) ->
      Fmt.pf ft "(@[<hv>%a@ %a@])" pp_op o (Fmt.list ~sep:Fmt.sp pp) l

let show t = Fmt.str "%a" pp t

let rec size = function
  | Op (_, l) -> List.fold_left (fun a t -> a + size t) 1 l
  | _ -> 1

(** Result sort of an operator, given the sorts of its arguments. *)
let result_sort op (args : sort list) : sort =
  let a0 () = List.hd args in
  match op with
  | And | Or | Not | SemEq | SemEqUntyped | Distinct | AndLazy | OrLazy | Conj
  | Exists1 _ | BvAddOvf _ | BvSubOvf _ | BvMulOvf _ | BvNegOvf | BvLt _
  | BvLeq _ | BvGt _ | BvGeq _ | BvToBool | FEq | FLt | FLeq | FGt | FGeq
  | FIsFloatClass _ | FIsNegative | FIsPositive | PtrIsNullLoc | PtrIsNull
  | PtrIsAtNullLoc ->
      SBool
  | Ite -> List.nth args 1
  | BvAdd _ | BvSub _ | BvMul _ | BvDiv _ | BvRem _ | BvMod | BvNeg _ | BvAnd
  | BvOr | BvXor | BvShl | BvLShr | BvAShr | BvNot | BvNotBool | FAdd | FSub
  | FMul | FDiv | FRem | FFmod | FFma | FMin | FMax | FMinimum | FMaximum | FAbs
  | FNeg | FSqrt | FRound _ | PtrAddOfs ->
      a0 ()
  | FFmodOfRem -> List.nth args 1
  | BvConcat -> (
      match args with [ SBv n; SBv m ] -> SBv (n + m) | _ -> assert false)
  | BvExtend (_, k) -> (
      match args with [ SBv n ] -> SBv (n + k) | _ -> assert false)
  | BvExtract (i, j) ->
      ignore i;
      ignore j;
      SBv (j - i + 1)
  | BvOfBool n -> SBv n
  | BvOfFloat (_, _, n) -> SBv n
  | BvToFloat (_, _, p) -> SFloat p
  | BvToFloatRaw -> (
      match args with
      | [ SBv 16 ] -> SFloat F16
      | [ SBv 32 ] -> SFloat F32
      | [ SBv 64 ] -> SFloat F64
      | [ SBv 128 ] -> SFloat F128
      | _ -> assert false)
  | FCast (_, p) -> SFloat p
  | PtrMk -> ( match args with [ SLoc n; _ ] -> SPtr n | _ -> assert false)
  | PtrLoc -> ( match args with [ SPtr n ] -> SLoc n | _ -> assert false)
  | PtrOfs -> ( match args with [ SPtr n ] -> SBv n | _ -> assert false)
  | PtrNull n -> SPtr n
  | SeqMk s -> s

let rec sort_of (t : t) : sort =
  match t with
  | Var (_, s) | Bound (_, s) -> s
  | Bool _ -> SBool
  | Bv (n, _) -> SBv n
  | Loc (n, _) -> SLoc n
  | Float (p, _) -> SFloat p
  | Op (op, args) -> result_sort op (List.map sort_of args)

(** [ptr_size] etc. *)
let bits_of_prec = FP.size
