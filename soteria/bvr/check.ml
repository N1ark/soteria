(** Front-end: converts the OCaml parse tree of a BVR file into typed BVR
    ({!Syntax}), rejecting anything outside of the language. *)

open Ppxlib
open Syntax

exception Error of Location.t * string

let error loc fmt = Fmt.kstr (fun s -> raise (Error (loc, s))) fmt

let pp_loc ft (loc : Location.t) =
  let p = loc.loc_start in
  Fmt.pf ft "%s:%d:%d" p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol)

(* ---------------------------------------------------------------- *)
(* Types *)

let rec ty_of_core (ct : core_type) : Syntax.ty =
  match ct.ptyp_desc with
  | Ptyp_constr ({ txt = Lident "int"; _ }, []) -> TInt
  | Ptyp_constr ({ txt = Lident "bool"; _ }, []) -> TBool
  | Ptyp_constr ({ txt = Lident "unit"; _ }, []) -> TUnit
  | Ptyp_constr ({ txt = Lident "t"; _ }, []) -> TTerm
  | Ptyp_constr ({ txt = Lident "kind"; _ }, []) -> TKind
  | Ptyp_constr ({ txt = Lident "ty"; _ }, []) -> TSty
  | Ptyp_constr ({ txt = Lident "float"; _ }, []) -> TFloat
  | Ptyp_constr ({ txt = Lident "var"; _ }, []) -> TVar
  | Ptyp_constr ({ txt = Lident s; _ }, []) when List.mem s data_types ->
      TData s
  | Ptyp_constr ({ txt = Lident "list"; _ }, [ t ]) -> TList (ty_of_core t)
  | Ptyp_constr ({ txt = Lident "option"; _ }, [ t ]) -> TOption (ty_of_core t)
  | Ptyp_tuple l -> TTuple (List.map ty_of_core l)
  | _ -> error ct.ptyp_loc "unsupported type"

(** Types of the arguments and result of an arrow type. *)
let rec arrow_of_core (ct : core_type) =
  match ct.ptyp_desc with
  | Ptyp_arrow (Nolabel, a, r) ->
      let args, ret = arrow_of_core r in
      (ty_of_core a :: args, ret)
  | _ -> ([], ty_of_core ct)

let rec ty_equal a b =
  match (a, b) with
  | TTuple l1, TTuple l2 ->
      List.length l1 = List.length l2 && List.for_all2 ty_equal l1 l2
  | TOption a, TOption b | TList a, TList b -> ty_equal a b
  | _ -> a = b

let expect loc ~expected ty =
  if not (ty_equal expected ty) then
    error loc "type mismatch: expected %a, got %a" pp_ty expected pp_ty ty

(* ---------------------------------------------------------------- *)
(* Environments *)

type sig_ = { args : Syntax.ty list; ret : Syntax.ty }

type env = {
  vars : (string * Syntax.ty) list;
  locals : (string * sig_) list;
  globals : (string * sig_) list;  (** functions and primitives *)
}

let find_global env loc name =
  match List.assoc_opt name env.globals with
  | Some s -> s
  | None -> error loc "unknown function %s" name

(* ---------------------------------------------------------------- *)
(* Patterns *)

let rule_name_of_attrs (attrs : attributes) =
  List.find_map
    (fun (a : attribute) ->
      if a.attr_name.txt = "r" then
        match a.attr_payload with
        | PStr
            [
              { pstr_desc = Pstr_eval ({ pexp_desc = Pexp_ident id; _ }, _); _ };
            ] ->
            Some (Longident.name id.txt)
        | _ -> error a.attr_loc "expected [@r name]"
      else None)
    attrs

let constr_args ?(any = fun _ -> false) loc (c : constr) (arg : 'a option)
    (split : 'a -> 'a list option) =
  let n = List.length c.c_args in
  let args =
    match arg with
    | None -> []
    | Some a when n > 1 && any a -> List.init n (fun _ -> a)
    | Some a when n > 1 -> (
        match split a with
        | Some l -> l
        | None -> error loc "constructor %s expects %d arguments" c.c_name n)
    | Some a -> [ a ]
  in
  if List.length args <> n then
    error loc "constructor %s expects %d arguments" c.c_name n;
  args

let split_ppat (p : pattern) =
  match p.ppat_desc with Ppat_tuple l -> Some l | _ -> None

let split_pexp (e : expression) =
  match e.pexp_desc with Pexp_tuple l -> Some l | _ -> None

(** Converts a pattern at the expected type, returning it and its binders. *)
let rec pat (expected : Syntax.ty) (p : pattern) : Syntax.pat =
  let loc = p.ppat_loc in
  let mk d = { p = d; pty = expected; ploc = loc } in
  match p.ppat_desc with
  | Ppat_any -> mk PAny
  | Ppat_var { txt; _ } -> mk (PVar txt)
  | Ppat_alias (p, { txt; _ }) -> mk (PAs (pat expected p, txt))
  | Ppat_or (p1, p2) ->
      let p1 = pat expected p1 and p2 = pat expected p2 in
      let b1 = binders p1 and b2 = binders p2 in
      let sort = List.sort compare in
      if sort (List.map fst b1) <> sort (List.map fst b2) then
        error loc "or-pattern alternatives bind different variables";
      List.iter
        (fun (x, (t, small)) ->
          let t', small' = List.assoc x b2 in
          expect loc ~expected:t t';
          if small <> small' then
            error loc "variable %s bound at different integer kinds" x)
        b1;
      mk (POr (p1, p2))
  | Ppat_constant (Pconst_integer (s, None)) ->
      expect loc ~expected TInt;
      mk (PInt (Z.of_string s))
  | Ppat_tuple l -> (
      match expected with
      | TTuple tys when List.length tys = List.length l ->
          mk (PTuple (List.map2 pat tys l))
      | _ -> error loc "unexpected tuple pattern at type %a" pp_ty expected)
  | Ppat_construct ({ txt = Lident (("true" | "false") as b); _ }, None) ->
      expect loc ~expected TBool;
      mk (PBool (b = "true"))
  | Ppat_construct ({ txt = Lident "()"; _ }, None) ->
      expect loc ~expected TUnit;
      mk PUnit
  | Ppat_construct ({ txt = Lident "None"; _ }, None) -> (
      match expected with
      | TOption _ -> mk PNone
      | _ -> error loc "None at type %a" pp_ty expected)
  | Ppat_construct ({ txt = Lident "Some"; _ }, Some (_, p)) -> (
      match expected with
      | TOption t -> mk (PSome (pat t p))
      | _ -> error loc "Some at type %a" pp_ty expected)
  | Ppat_construct ({ txt = Lident "[]"; _ }, None) -> (
      match expected with
      | TList _ -> mk PNil
      | _ -> error loc "[] at type %a" pp_ty expected)
  | Ppat_construct
      ( { txt = Lident "::"; _ },
        Some (_, { ppat_desc = Ppat_tuple [ h; tl ]; _ }) ) -> (
      match expected with
      | TList t -> mk (PCons (pat t h, pat expected tl))
      | _ -> error loc ":: at type %a" pp_ty expected)
  | Ppat_construct ({ txt = Lident name; _ }, arg) -> (
      match find_constr name with
      | None -> error loc "unknown constructor %s" name
      | Some c ->
          (* kind constructors can be matched against terms *)
          let ok =
            ty_equal c.c_res expected || (c.c_res = TKind && expected = TTerm)
          in
          if not ok then
            error loc "constructor %s has type %a, expected %a" name pp_ty
              c.c_res pp_ty expected;
          let is_any (p : pattern) = p.ppat_desc = Ppat_any in
          let args =
            constr_args ~any:is_any loc c (Option.map snd arg) split_ppat
          in
          let args = List.map2 (fun a p -> pat (arg_ty a) p) c.c_args args in
          List.iter2
            (fun a (p : Syntax.pat) ->
              match (a, p.p) with
              | Small, (PAny | PVar _ | PInt _) -> ()
              | Small, _ ->
                  error p.ploc
                    "only variables, wildcards and literals can match \
                     machine-integer fields"
              | Arg TInt, PInt _ ->
                  error p.ploc "cannot match an arbitrary-precision literal"
              | _ -> ())
            c.c_args args;
          mk (PConstr (c, args)))
  | Ppat_record (fields, _) ->
      if expected <> TData "checked" then
        error loc "record patterns are only supported for checked";
      let fields =
        List.map
          (fun (({ txt; _ } : longident loc), p) ->
            let f = Longident.name txt in
            if not (List.mem f checked_fields) then
              error loc "unknown field %s" f;
            (f, pat TBool p))
          fields
      in
      mk (PRecord fields)
  | Ppat_constraint (p, ct) ->
      expect loc ~expected (ty_of_core ct);
      pat expected p
  | _ -> error loc "unsupported pattern"

(** Variables bound by a pattern, with their type and whether they are bound to
    a machine-integer field. *)
and binders (p : Syntax.pat) : (string * (Syntax.ty * bool)) list =
  match p.p with
  | PAny | PInt _ | PBool _ | PUnit | PNone | PNil -> []
  | PVar x -> [ (x, (p.pty, false)) ]
  | PAs (p', x) -> (x, (p.pty, false)) :: binders p'
  | POr (p1, _) -> binders p1
  | PTuple l -> List.concat_map binders l
  | PSome p -> binders p
  | PCons (a, b) -> binders a @ binders b
  | PRecord l -> List.concat_map (fun (_, p) -> binders p) l
  | PConstr (c, args) ->
      List.concat
        (List.map2
           (fun a p ->
             match (a, p.p) with
             | Small, PVar x -> [ (x, (TInt, true)) ]
             | _ -> binders p)
           c.c_args args)

let no_shadow env loc x =
  if List.mem_assoc x env.globals then
    error loc "%s shadows a global function" x

let add_binders env p =
  let bs = binders p in
  List.iter (fun (x, _) -> no_shadow env p.ploc x) bs;
  { env with vars = List.map (fun (x, (t, _)) -> (x, t)) bs @ env.vars }

(* ---------------------------------------------------------------- *)
(* Expressions *)

let int_ops = [ ("+", Add); ("-", Sub); ("*", Mul) ]
let cmp_ops = [ ("<", Lt); ("<=", Le); (">", Gt); (">=", Ge) ]

let bit_ops =
  [ ("land", Land); ("lor", Lor); ("lxor", Lxor); ("lsl", Lsl); ("asr", Asr) ]

(** Types on which [=] and [<>] are allowed: structural equality coincides in
    OCaml and Lean. *)
let rec eq_ty = function
  | TInt | TBool | TUnit | TSty | TData _ -> true
  | TTuple l -> List.for_all eq_ty l
  | TOption t -> eq_ty t
  | TTerm | TKind | TFloat | TVar | TList _ -> false

let rec expr env ?expected (e : expression) : Syntax.expr =
  let loc = e.pexp_loc in
  let mk ety d =
    Option.iter (fun expected -> expect loc ~expected ety) expected;
    { e = d; ety; eloc = loc }
  in
  match e.pexp_desc with
  | Pexp_ident { txt = Lident x; _ } -> (
      match List.assoc_opt x env.vars with
      | Some t -> mk t (EVar x)
      | None -> (
          match List.assoc_opt x env.globals with
          | Some { args = []; ret } -> mk ret (ECall (x, []))
          | _ -> error loc "unbound variable %s" x))
  | Pexp_constant (Pconst_integer (s, None)) -> mk TInt (EInt (Z.of_string s))
  | Pexp_construct ({ txt = Lident (("true" | "false") as b); _ }, None) ->
      mk TBool (EBool (b = "true"))
  | Pexp_construct ({ txt = Lident "()"; _ }, None) -> mk TUnit EUnit
  | Pexp_construct ({ txt = Lident "None"; _ }, None) -> (
      match expected with
      | Some (TOption _ as t) -> mk t ENone
      | _ -> error loc "cannot infer the type of None")
  | Pexp_construct ({ txt = Lident "Some"; _ }, Some a) ->
      let inner =
        match expected with Some (TOption t) -> Some t | _ -> None
      in
      let a = expr env ?expected:inner a in
      mk (TOption a.ety) (ESome a)
  | Pexp_construct ({ txt = Lident "[]"; _ }, None) -> (
      match expected with
      | Some (TList _ as t) -> mk t ENil
      | _ -> error loc "cannot infer the type of []")
  | Pexp_construct
      ({ txt = Lident "::"; _ }, Some { pexp_desc = Pexp_tuple [ h; tl ]; _ })
    ->
      let inner = match expected with Some (TList t) -> Some t | _ -> None in
      let h = expr env ?expected:inner h in
      let tl = expr env ~expected:(TList h.ety) tl in
      mk tl.ety (ECons (h, tl))
  | Pexp_construct ({ txt = Lident name; _ }, arg) -> (
      match find_constr name with
      | None -> error loc "unknown constructor %s" name
      | Some c ->
          let args = constr_args loc c arg split_pexp in
          let args =
            List.map2 (fun a e -> expr env ~expected:(arg_ty a) e) c.c_args args
          in
          mk c.c_res (EConstr (c, args)))
  | Pexp_apply ({ pexp_desc = Pexp_ident { txt = Lident op; _ }; _ }, args) -> (
      let args =
        List.map
          (function
            | Nolabel, a -> a
            | _, (a : expression) ->
                error a.pexp_loc "labelled arguments are not supported")
          args
      in
      match (op, args) with
      | "<|", [ k; t ] ->
          let k = expr env ~expected:TKind k in
          let t = expr env ~expected:TSty t in
          mk TTerm (ENode (k, t))
      | ("+" | "-" | "*"), [ a; b ] ->
          let a = expr env ~expected:TInt a and b = expr env ~expected:TInt b in
          mk TInt (EBinop (Arith (List.assoc op int_ops), a, b))
      | ("<" | "<=" | ">" | ">="), [ a; b ] ->
          let a = expr env ~expected:TInt a and b = expr env ~expected:TInt b in
          mk TBool (EBinop (Arith (List.assoc op cmp_ops), a, b))
      | ("=" | "<>"), [ a; b ] ->
          let a = expr env a in
          let b = expr env ~expected:a.ety b in
          if not (eq_ty a.ety) then
            error loc "structural equality is not allowed at type %a" pp_ty
              a.ety;
          mk TBool (EBinop (Arith (if op = "=" then Eq else Ne), a, b))
      | ("&&" | "||"), [ a; b ] ->
          let a = expr env ~expected:TBool a
          and b = expr env ~expected:TBool b in
          mk TBool (EBinop (Arith (if op = "&&" then And else Or), a, b))
      | ("land" | "lor" | "lxor" | "lsl" | "asr"), [ a; b ] ->
          let a = expr env ~expected:TInt a and b = expr env ~expected:TInt b in
          mk TInt (EBinop (Bit (List.assoc op bit_ops), a, b))
      | "not", [ a ] -> mk TBool (EUnop (Not, expr env ~expected:TBool a))
      | ("~-" | "-"), [ a ] -> mk TInt (EUnop (Neg, expr env ~expected:TInt a))
      | "lognot", [ a ] -> mk TInt (EUnop (Lognot, expr env ~expected:TInt a))
      | f, args -> (
          let check_args (s : sig_) =
            if List.length s.args <> List.length args then
              error loc "%s expects %d arguments, got %d" f (List.length s.args)
                (List.length args);
            List.map2 (fun t a -> expr env ~expected:t a) s.args args
          in
          match List.assoc_opt f env.locals with
          | Some s -> mk s.ret (ELocalCall (f, check_args s))
          | None ->
              let s = find_global env loc f in
              mk s.ret (ECall (f, check_args s))))
  | Pexp_ifthenelse (c, a, Some b) ->
      let c = expr env ~expected:TBool c in
      let a = expr env ?expected a in
      let b = expr env ~expected:a.ety b in
      mk a.ety (EIf (c, a, b))
  | Pexp_let (Nonrecursive, [ vb ], body) -> (
      match vb.pvb_expr.pexp_desc with
      | Pexp_function (params, ret, Pfunction_body fbody) ->
          let name =
            match vb.pvb_pat.ppat_desc with
            | Ppat_var { txt; _ } -> txt
            | _ -> error vb.pvb_loc "expected a function name"
          in
          let params = List.map (param_of loc) params in
          List.iter (no_shadow env loc) (name :: List.map fst params);
          let ret = Option.map ret_of ret in
          let fenv = { env with vars = params @ env.vars } in
          let fbody = expr fenv ?expected:ret fbody in
          let s = { args = List.map snd params; ret = fbody.ety } in
          let body =
            expr { env with locals = (name, s) :: env.locals } ?expected body
          in
          mk body.ety (ELetFun (name, params, fbody, body))
      | _ ->
          let annot =
            match vb.pvb_constraint with
            | Some (Pvc_constraint { typ; locally_abstract_univars = [] }) ->
                Some (ty_of_core typ)
            | None -> None
            | _ -> error vb.pvb_loc "unsupported binding constraint"
          in
          let rhs = expr env ?expected:annot vb.pvb_expr in
          let p = pat rhs.ety vb.pvb_pat in
          let body = expr (add_binders env p) ?expected body in
          mk body.ety (ELet (p, rhs, body)))
  | Pexp_match (scrut, cases) ->
      let scruts =
        match scrut.pexp_desc with
        | Pexp_tuple l -> List.map (expr env) l
        | _ -> [ expr env scrut ]
      in
      let cases = List.map (case env ?expected scruts) cases in
      let ety =
        match cases with
        | [] -> error loc "empty match"
        | c :: rest ->
            List.iter
              (fun c' -> expect c'.cloc ~expected:c.body.ety c'.body.ety)
              rest;
            c.body.ety
      in
      mk ety (EMatch (scruts, cases))
  | Pexp_tuple l ->
      let tys = match expected with Some (TTuple t) -> Some t | _ -> None in
      let l =
        match tys with
        | Some tys when List.length tys = List.length l ->
            List.map2 (fun t e -> expr env ~expected:t e) tys l
        | _ -> List.map (expr env) l
      in
      mk (TTuple (List.map (fun e -> e.ety) l)) (ETuple l)
  | Pexp_record (fields, None) ->
      let fields =
        List.map
          (fun (({ txt; _ } : longident loc), e) ->
            (Longident.name txt, expr env ~expected:TBool e))
          fields
      in
      if List.sort compare (List.map fst fields) <> checked_fields then
        error loc
          "a checked record needs exactly the fields signed and unsigned";
      mk (TData "checked") (ERecord fields)
  | Pexp_field (e, { txt = Lident f; _ }) ->
      if not (List.mem f checked_fields) then error loc "unknown field %s" f;
      let e = expr env ~expected:(TData "checked") e in
      mk TBool (EField (e, f))
  | Pexp_sequence ({ pexp_desc = Pexp_assert c; _ }, body) ->
      let c = expr env ~expected:TBool c in
      let body = expr env ?expected body in
      mk body.ety (EAssert (c, body))
  | Pexp_constraint (e, ct) ->
      let t = ty_of_core ct in
      Option.iter (fun expected -> expect loc ~expected t) expected;
      expr env ~expected:t e
  | _ -> error loc "unsupported expression"

and case env ?expected scruts (c : Ppxlib.case) : Syntax.case =
  let loc = c.pc_lhs.ppat_loc in
  (* the rule name is written after the pattern; when the pattern is a tuple
     without parentheses, it is attached to its last component *)
  let rule, lhs =
    match rule_name_of_attrs c.pc_lhs.ppat_attributes with
    | Some r -> (Some r, { c.pc_lhs with ppat_attributes = [] })
    | None -> (
        match c.pc_lhs.ppat_desc with
        | Ppat_tuple l -> (
            let rev = List.rev l in
            let last = List.hd rev in
            match rule_name_of_attrs last.ppat_attributes with
            | Some r ->
                let last = { last with ppat_attributes = [] } in
                ( Some r,
                  {
                    c.pc_lhs with
                    ppat_desc = Ppat_tuple (List.rev (last :: List.tl rev));
                  } )
            | None -> (None, c.pc_lhs))
        | _ -> (None, c.pc_lhs))
  in
  let sty =
    match scruts with
    | [ s ] -> s.ety
    | _ -> TTuple (List.map (fun s -> s.ety) scruts)
  in
  let pat = pat sty lhs in
  let env = add_binders env pat in
  let guard = Option.map (expr env ~expected:TBool) c.pc_guard in
  let body = expr env ?expected c.pc_rhs in
  { pat; guard; body; rule; cloc = loc }

and param_of loc (p : function_param) =
  match p.pparam_desc with
  | Pparam_val
      ( Nolabel,
        None,
        {
          ppat_desc =
            Ppat_constraint ({ ppat_desc = Ppat_var { txt; _ }; _ }, ct);
          _;
        } ) ->
      (txt, ty_of_core ct)
  | _ -> error loc "parameters must be of the form (x : ty)"

and ret_of = function
  | Pconstraint ct -> ty_of_core ct
  | Pcoerce _ -> failwith "unsupported coercion"

(* ---------------------------------------------------------------- *)
(* Top-level *)

let spec_of_attrs (attrs : attributes) =
  List.find_map
    (fun (a : attribute) ->
      if a.attr_name.txt = "spec" then
        match a.attr_payload with
        | PStr [ { pstr_desc = Pstr_eval (e, _); _ } ] -> Some e
        | _ -> error a.attr_loc "expected [@spec expr]"
      else None)
    attrs

type raw_fn = {
  rname : string;
  rparams : (string * Syntax.ty) list;
  rret : Syntax.ty;
  rspec : expression option;
  rbody : expression;
  rloc : Location.t;
}

let raw_fn (vb : value_binding) =
  let loc = vb.pvb_loc in
  let rname =
    match vb.pvb_pat.ppat_desc with
    | Ppat_var { txt; _ } -> txt
    | _ -> error loc "expected a function name"
  in
  let rspec = spec_of_attrs vb.pvb_attributes in
  match vb.pvb_expr.pexp_desc with
  | Pexp_function (params, Some ret, Pfunction_body rbody) ->
      {
        rname;
        rparams = List.map (param_of loc) params;
        rret = ret_of ret;
        rspec;
        rbody;
        rloc = loc;
      }
  | Pexp_function _ -> error loc "%s: the return type must be annotated" rname
  | _ -> (
      match vb.pvb_constraint with
      | Some (Pvc_constraint { typ; locally_abstract_univars = [] }) ->
          {
            rname;
            rparams = [];
            rret = ty_of_core typ;
            rspec;
            rbody = vb.pvb_expr;
            rloc = loc;
          }
      | _ -> error loc "%s: constants must be annotated with their type" rname)

let program (str : structure) : program =
  let prims, raws =
    List.fold_left
      (fun (prims, raws) (si : structure_item) ->
        match si.pstr_desc with
        | Pstr_primitive vd ->
            let pargs, pret = arrow_of_core vd.pval_type in
            ({ pname = vd.pval_name.txt; pargs; pret } :: prims, raws)
        | Pstr_value (_, [ vb ]) -> (prims, raw_fn vb :: raws)
        | Pstr_value _ -> error si.pstr_loc "one function per let"
        | _ -> error si.pstr_loc "unsupported top-level item")
      ([], []) str
  in
  let prims = List.rev prims and raws = List.rev raws in
  let globals =
    List.map (fun p -> (p.pname, { args = p.pargs; ret = p.pret })) prims
    @ List.map
        (fun r -> (r.rname, { args = List.map snd r.rparams; ret = r.rret }))
        raws
  in
  let names = List.map fst globals in
  List.iter
    (fun n ->
      if List.length (List.filter (( = ) n) names) > 1 then
        error Location.none "%s is defined twice" n)
    names;
  let env0 = { vars = []; locals = []; globals } in
  let fns =
    List.map
      (fun r ->
        List.iter (fun (x, _) -> no_shadow env0 r.rloc x) r.rparams;
        let env = { env0 with vars = r.rparams } in
        let body = expr env ~expected:r.rret r.rbody in
        let spec =
          Option.map
            (fun s ->
              if r.rret <> TTerm then
                error r.rloc "%s: only term-returning functions have a spec"
                  r.rname;
              expr env ~expected:TTerm s)
            r.rspec
        in
        {
          name = r.rname;
          params = r.rparams;
          ret = r.rret;
          spec;
          body;
          floc = r.rloc;
        })
      raws
  in
  { prims; fns }

let parse_file file : structure =
  let ic = open_in_bin file in
  let lexbuf = Lexing.from_channel ic in
  Lexing.set_filename lexbuf file;
  let str = Parse.implementation lexbuf in
  close_in ic;
  str
