(** Lean backend.

    Functions with a [[@spec]] are rule functions. Each of their rules becomes a
    Lean function [f.r.name : Ops -> args -> Option Term] (the rule's patterns
    and guard, returning its right-hand side), in which the calls to rule
    functions go through the record [O : Ops]. [f.step O] tries the rules in
    order and falls back to the spec; [opsN orc n] ties the knot with [n] steps
    of fuel (fuel 0 being the raw specs).

    Helpers that call rule functions or oracles take [O] as a parameter; the
    other helpers are plain Lean functions.

    Three files are generated: [Model.lean] (the above), [Statements.lean]
    (soundness of [Ops], and one statement per rule) and [Soundness.lean]
    (soundness of [opsN], from the proofs [f.r.name.proof] of the rule
    statements, written by hand). *)

open Syntax

let pf = Format.fprintf

let list ?(sep = ", ") pp ft l =
  Format.pp_print_list ~pp_sep:(fun ft () -> pf ft "%s" sep) pp ft l

let keywords =
  [
    "by";
    "at";
    "fun";
    "from";
    "have";
    "show";
    "let";
    "if";
    "then";
    "else";
    "do";
    "match";
    "with";
    "in";
    "end";
    "open";
    "theorem";
    "def";
    "where";
    "deriving";
    "instance";
    "structure";
    "class";
    "example";
    "calc";
    "mut";
    "return";
    "for";
    "unless";
    "import";
    "section";
    "namespace";
    "variable";
    "universe";
    "private";
    "protected";
    "partial";
    "noncomputable";
    "mutual";
    "inductive";
    "extends";
    "abbrev";
    "macro";
    "syntax";
    "notation";
    "local";
    "attribute";
    "Type";
    "Prop";
    "Sort";
    "at";
    "obtain";
    "using";
    "fin";
  ]

let id x = if List.mem x keywords then "«" ^ x ^ "»" else x

(* ---------------------------------------------------------------- *)
(* Classification *)

type kind = Rule | OHelper | Pure
type ctx = { prims : prim list; kinds : (string * kind) list; fns : fn list }

let fn_kind ctx f = List.assoc f ctx.kinds
let is_oracle ctx f = List.exists (fun p -> p.pname = f && p.oracle) ctx.prims
let is_prim ctx f = List.exists (fun p -> p.pname = f) ctx.prims

let classify (p : program) =
  let is_oracle f = List.exists (fun q -> q.pname = f && q.oracle) p.prims in
  let kinds =
    ref
      (List.map
         (fun f -> (f.name, if Option.is_some f.spec then Rule else Pure))
         p.fns)
  in
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter
      (fun f ->
        if List.assoc f.name !kinds = Pure then
          let needs_o =
            List.exists
              (fun g ->
                is_oracle g
                ||
                match List.assoc_opt g !kinds with
                | Some (Rule | OHelper) -> true
                | _ -> false)
              (Gen_ocaml.calls [] f.body)
          in
          if needs_o then (
            kinds := (f.name, OHelper) :: List.remove_assoc f.name !kinds;
            changed := true))
      p.fns
  done;
  { prims = p.prims; kinds = !kinds; fns = p.fns }

(* ---------------------------------------------------------------- *)
(* Types *)

let rec lean_ty ft = function
  | TInt -> pf ft "Int"
  | TBv -> pf ft "BvVal"
  | TBool -> pf ft "Bool"
  | TUnit -> pf ft "Unit"
  | TTerm -> pf ft "Term"
  | TKind -> pf ft "Kind"
  | TSty -> pf ft "Ty"
  | TFloat -> pf ft "FloatLit"
  | TVar -> pf ft "Int"
  | TData "unop" -> pf ft "Unop"
  | TData "binop" -> pf ft "Binop"
  | TData "triop" -> pf ft "Triop"
  | TData "nop" -> pf ft "Nop"
  | TData "checked" -> pf ft "Checked"
  | TData "rm" -> pf ft "RM"
  | TData "fp" -> pf ft "Prec"
  | TData "fc" -> pf ft "FClass"
  | TData "ext" -> pf ft "Ext"
  | TData "ext_ty" -> pf ft "ExtTy"
  | TData s -> failwith ("lean_ty: " ^ s)
  | TTuple l -> pf ft "(%a)" (list ~sep:" × " lean_ty) l
  | TOption t -> pf ft "(Option %a)" lean_ty t
  | TList t -> pf ft "(List %a)" lean_ty t

(* ---------------------------------------------------------------- *)
(* Patterns *)

let rec pat ft (p : pat) =
  match p.p with
  | PAny -> pf ft "_"
  | PVar x -> pf ft "%s" (id x)
  | PLit x -> pf ft "%s@(Term.mk (Kind.bitVec _) _)" (id x)
  | PAs (q, x) -> pf ft "%s@%a" (id x) pat q
  | POr _ -> failwith "gen_lean: or-pattern after desugaring"
  | PInt z -> pf ft "(%s : Int)" (Z.to_string z)
  | PBool b -> pf ft "%b" b
  | PUnit -> pf ft "()"
  | PTuple l -> pf ft "(%a)" (list pat) l
  | PSome q -> pf ft "(some %a)" pat q
  | PNone -> pf ft "none"
  | PNil -> pf ft "[]"
  | PCons (h, t) -> pf ft "(%a :: %a)" pat h pat t
  | PRecord fs ->
      let field f =
        match List.assoc_opt f fs with
        | Some p -> Fmt.str "%a" pat p
        | None -> "_"
      in
      pf ft "⟨%s, %s⟩" (field "signed") (field "unsigned")
  | PConstr (c, args) ->
      let inner ft () =
        match args with
        | [] -> pf ft "%s" c.c_lean
        | _ -> pf ft "(%s %a)" c.c_lean (list ~sep:" " pat) args
      in
      if p.pty = TTerm then pf ft "(Term.mk %a _)" inner () else inner ft ()

(* ---------------------------------------------------------------- *)
(* Expressions *)

let rec expr ctx ft (e : expr) =
  let expr = expr ctx in
  match e.e with
  | EVar x -> pf ft "%s" (id x)
  | EInt z -> pf ft "(%s : Int)" (Z.to_string z)
  | EBool b -> pf ft "%b" b
  | EUnit -> pf ft "()"
  | EConstr (c, []) -> pf ft "%s" c.c_lean
  | EConstr (c, args) -> pf ft "(%s %a)" c.c_lean (list ~sep:" " expr) args
  | ENode (k, t) -> pf ft "(Term.mk %a %a)" expr k expr t
  | ECall (f, args) ->
      let f =
        if is_oracle ctx f then "O.orc." ^ f
        else if is_prim ctx f then f
        else
          match fn_kind ctx f with
          | Rule -> "O." ^ f
          | OHelper -> f ^ " O"
          | Pure -> f
      in
      if args = [] then pf ft "%s" f
      else pf ft "(%s %a)" f (list ~sep:" " expr) args
  | ELocalCall (f, args) -> pf ft "(%s %a)" (id f) (list ~sep:" " expr) args
  | EUnop (Neg, a) -> pf ft "(- %a)" expr a
  | EUnop (Not, a) -> pf ft "(! %a)" expr a
  | EUnop (Lognot, a) -> pf ft "(zlognot %a)" expr a
  | EBinop (Arith op, a, b) -> (
      let infix s = pf ft "(%a %s %a)" expr a s expr b in
      let dec s = pf ft "(decide (%a %s %a))" expr a s expr b in
      match op with
      | Add -> infix "+"
      | Sub -> infix "-"
      | Mul -> infix "*"
      | Lt -> dec "<"
      | Le -> dec "≤"
      | Gt -> dec ">"
      | Ge -> dec "≥"
      | Eq -> dec "="
      | Ne -> dec "≠"
      | And -> infix "&&"
      | Or -> infix "||")
  | EBinop (Bit op, a, b) ->
      let f =
        match op with
        | Land -> "zland"
        | Lor -> "zlor"
        | Lxor -> "zlxor"
        | Lsl -> "zshiftl"
        | Asr -> "zasr"
      in
      pf ft "(%s %a %a)" f expr a expr b
  | EIf (c, a, b) ->
      pf ft "@[<hv>(if %a@ then %a@ else %a)@]" expr c expr a expr b
  | ELet ({ p = PVar x; _ }, rhs, body) ->
      pf ft "@[<v>(let %s := %a;@ %a)@]" (id x) expr rhs expr body
  | ELet (p, rhs, body) ->
      pf ft "@[<v>(match %a with@ | %a =>@;<1 2>%a)@]" expr rhs pat p expr body
  | ELetFun (f, params, fbody, body) ->
      pf ft "@[<v>(let %s := fun %a =>@;<1 2>%a;@ %a)@]" (id f)
        (list ~sep:" " (fun ft (x, t) -> pf ft "(%s : %a)" (id x) lean_ty t))
        params expr fbody expr body
  | EMatch (scruts, cases) -> match_ ctx ft (scruts, cases)
  | ETuple l -> pf ft "(%a)" (list expr) l
  | ESome e -> pf ft "(some %a)" expr e
  | ENone -> pf ft "none"
  | ENil -> pf ft "[]"
  | ECons (h, t) -> pf ft "(%a :: %a)" expr h expr t
  | ERecord fs ->
      pf ft "({ signed := %a, unsigned := %a } : Checked)" expr
        (List.assoc "signed" fs) expr (List.assoc "unsigned" fs)
  | EField (e, f) -> pf ft "%a.%s" expr e f
  | EAssert (_, body) -> expr ft body

(** Rebinds the variables of [PLit] patterns to their values. *)
and lit_lets ft (p : pat) =
  List.iter
    (fun x -> pf ft "let %s := bv_of_lit %s;@ " (id x) (id x))
    (Check.lit_binders p)

(** Prints [k] after the [lit_lets] of [p], if any. *)
and with_lits p k ft () =
  if Check.lit_binders p = [] then k ft ()
  else pf ft "@[<hv>(%a%a)@]" lit_lets p k ()

(** A case's result: [some body], under its guard. *)
and guarded ctx (c : case) ft () =
  with_lits c.pat
    (fun ft () ->
      match c.guard with
      | None -> pf ft "some (%a)" (expr ctx) c.body
      | Some g ->
          pf ft "@[<hv>(if %a@ then some (%a)@ else none)@]" (expr ctx) g
            (expr ctx) c.body)
    ft ()

(** Whether a pattern matches every value of its type. *)
and irrefutable (p : pat) =
  match p.p with
  | PAny | PVar _ | PUnit -> true
  | PAs (q, _) -> irrefutable q
  | PTuple l -> List.for_all irrefutable l
  | PRecord fs -> List.for_all (fun (_, q) -> irrefutable q) fs
  | _ -> false

(** How a match on [scruts] is printed: on several discriminants when possible
    (so that Lean sees the recursion on each of them), else on a tuple. *)
and discriminants ctx (scruts, (cases : case list)) =
  let multi =
    List.length scruts > 1
    && List.for_all
         (fun (c : case) ->
           match c.pat.p with PTuple _ | PAny -> true | _ -> false)
         cases
  in
  let d ft () =
    if multi || List.length scruts = 1 then list (expr ctx) ft scruts
    else pf ft "(%a)" (list (expr ctx)) scruts
  in
  let p ft (q : pat) =
    match q.p with
    | PTuple l when multi -> list pat ft l
    | PAny when multi -> list (fun ft _ -> pf ft "_") ft scruts
    | _ -> pat ft q
  in
  let wild ft () =
    if multi then list (fun ft _ -> pf ft "_") ft scruts else pf ft "_"
  in
  (d, p, wild)

(** A match with guards: each case is a Lean match of its own, returning [none]
    when its pattern or guard fails, and the first case that applies gives the
    result. A last case that always applies is the default. *)
and match_ ctx ft (scruts, cases) =
  let d, p, wild = discriminants ctx (scruts, cases) in
  let alt ft (c : case) =
    let rhs = guarded ctx c in
    if irrefutable c.pat then
      pf ft "@[<hv 2>(match %a with@ | %a =>@ %a)@]" d () p c.pat rhs ()
    else
      pf ft "@[<hv 2>(match %a with@ | %a =>@ %a@ | %a => none)@]" d () p c.pat
        rhs () wild ()
  in
  let alts, default =
    match List.rev cases with
    | ({ guard = None; _ } as c) :: rest when irrefutable c.pat ->
        ( List.rev rest,
          fun ft () ->
            pf ft "@[<hv 2>(match %a with@ | %a =>@ %a)@]" d () p c.pat
              (with_lits c.pat (fun ft () -> expr ctx ft c.body))
              () )
    | _ -> (cases, fun ft () -> pf ft "Inhabited.default")
  in
  match alts with
  | [] -> default ft ()
  | _ ->
      pf ft "@[<hv 2>((firstSome [%a]).getD@ %a)@]"
        (Format.pp_print_list ~pp_sep:(fun ft () -> pf ft ",@ ") alt)
        alts default ()

(* ---------------------------------------------------------------- *)
(* Rules *)

(** A rule function's body: a prefix of [let]s and [assert]s, then a match whose
    consecutive cases with the same name form the rules. *)
let rec split_body (e : expr) : (expr -> expr) * expr list * case list list =
  match e.e with
  | ELet (p, rhs, body) ->
      let pre, s, r = split_body body in
      ((fun x -> { e with e = ELet (p, rhs, pre x) }), s, r)
  | EAssert (_, body) -> split_body body
  | EMatch (scruts, cases) ->
      let groups =
        List.fold_left
          (fun acc (c : case) ->
            match acc with
            | (g :: _ as grp) :: rest when g.rule = c.rule ->
                (grp @ [ c ]) :: rest
            | _ -> [ c ] :: acc)
          [] cases
        |> List.rev
      in
      ((fun x -> x), scruts, groups)
  | _ ->
      ( (fun x -> x),
        [],
        [
          [
            {
              pat = { p = PAny; pty = TUnit; ploc = e.eloc };
              guard = None;
              body = e;
              rule = Some "main";
              cloc = e.eloc;
            };
          ];
        ] )

let rule_name (f : fn) (grp : case list) =
  match (List.hd grp).rule with
  | Some r -> r
  | None ->
      raise
        (Check.Error ((List.hd grp).cloc, Fmt.str "%s: unnamed rule" f.name))

let params ft (f : fn) =
  list ~sep:" "
    (fun ft (x, t) -> pf ft "(%s : %a)" (id x) lean_ty t)
    ft f.params

let args ft (f : fn) =
  list ~sep:" " (fun ft (x, _) -> pf ft "%s" (id x)) ft f.params

let arrow ft (f : fn) =
  List.iter (fun (_, t) -> pf ft "%a → " lean_ty t) f.params;
  lean_ty ft f.ret

(** The Lean function for one rule. *)
let rule_def ctx ft (f : fn) (pre, scruts, grp) =
  let name = rule_name f grp in
  let d, p, wild = discriminants ctx (scruts, grp) in
  let alt ft (c : case) =
    let rhs = guarded ctx c in
    if scruts = [] then rhs ft ()
    else if irrefutable c.pat then
      pf ft "@[<hv 2>(match %a with@ | %a =>@ %a)@]" d () p c.pat rhs ()
    else
      pf ft "@[<hv 2>(match %a with@ | %a =>@ %a@ | %a => none)@]" d () p c.pat
        rhs () wild ()
  in
  let rec lets ft (e : expr) =
    match e.e with
    | ELet ({ p = PVar x; _ }, rhs, b) ->
        pf ft "let %s := %a;@ %a" (id x) (expr ctx) rhs lets b
    | ELet _ -> failwith "gen_lean: destructuring let before a rule match"
    | _ -> Format.pp_print_list ~pp_sep:(fun ft () -> pf ft "@ <|> ") alt ft grp
  in
  pf ft "@[<v 2>def %s.r_%s (O : Ops) %a : Option Term :=@ %a@]@ @ " f.name
    (id name) params f lets
    (pre { (List.hd grp).body with e = EUnit })

let rules (f : fn) =
  let pre, scruts, groups = split_body f.body in
  List.map (fun g -> (pre, scruts, g)) groups

(* ---------------------------------------------------------------- *)
(* Files *)

let header ~sources ft imports =
  pf ft "@[<v>-- Generated by bvr from %a. Do not edit.@ "
    (list Format.pp_print_string)
    sources;
  List.iter (fun i -> pf ft "import %s@ " i) imports;
  pf ft
    "@ set_option linter.unusedVariables false@ set_option maxHeartbeats \
     1000000@ @ noncomputable section@ @ namespace Bvr@ @ open Classical@ @ "

(** The parameter a recursive helper recurses on: the first variable its body
    matches on. *)
let rec decreasing (f : fn) (e : expr) =
  match e.e with
  | ELet (_, _, b) | EAssert (_, b) | ELetFun (_, _, _, b) -> decreasing f b
  | EMatch (scruts, _) ->
      List.find_map
        (fun (s : expr) ->
          match s.e with
          | EVar x when List.mem_assoc x f.params -> Some x
          | _ -> None)
        scruts
  | _ -> None

let fn_def ctx ft (f : fn) ~o ~kw ~recursive =
  pf ft "@[<v 2>%s %s%s %a : %a :=@ %a@]@ " kw (id f.name)
    (if o then " (O : Ops)" else "")
    params f lean_ty f.ret (expr ctx) f.body;
  (if recursive then
     match decreasing f f.body with
     | Some x ->
         pf ft
           "termination_by sizeOf %s@ decreasing_by all_goals (simp_wf; \
            omega)@ "
           (id x)
     | None -> ());
  pf ft "@ "

let defs ctx ft kind ~o =
  List.iter
    (fun group ->
      let group = List.filter (fun f -> fn_kind ctx f.name = kind) group in
      match group with
      | [] -> ()
      | [ f ] when not (Gen_ocaml.is_recursive [ f ]) ->
          fn_def ctx ft f ~o ~kw:"def" ~recursive:false
      | _ ->
          pf ft "mutual@ @ ";
          List.iter (fn_def ctx ft ~o ~kw:"def" ~recursive:true) group;
          pf ft "end@ @ ")
    (Gen_ocaml.sccs ctx.fns)

let rule_fns ctx = List.filter (fun f -> fn_kind ctx f.name = Rule) ctx.fns

let model ~sources ft (p : program) =
  let ctx = classify p in
  header ~sources ft [ "Bvr.Prims" ];
  (* oracles *)
  pf ft
    "@[<v 2>/-- The primitives that the model is parameterised by. -/@ \
     structure Oracle where";
  List.iter
    (fun (q : prim) ->
      if q.oracle then (
        pf ft "@ %s : " q.pname;
        List.iter (fun t -> pf ft "%a → " lean_ty t) q.pargs;
        lean_ty ft q.pret))
    p.prims;
  pf ft "@]@ @ ";
  defs ctx ft Pure ~o:false;
  (* Ops *)
  pf ft
    "@[<v 2>/-- The rule functions, as used by the rules. -/@ structure Ops \
     where@ orc : Oracle";
  List.iter (fun f -> pf ft "@ %s : %a" f.name arrow f) (rule_fns ctx);
  pf ft "@]@ @ ";
  defs ctx ft OHelper ~o:true;
  (* specs *)
  List.iter
    (fun f ->
      pf ft "@[<v 2>def %s.spec %a : Term :=@ %a@]@ @ " f.name params f
        (expr ctx) (Option.get f.spec))
    (rule_fns ctx);
  (* rules and steps *)
  List.iter
    (fun f ->
      let rs = rules f in
      List.iter (rule_def ctx ft f) rs;
      pf ft
        "@[<v 2>def %s.step (O : Ops) %a : Term :=@ (firstSome [%a]).getD \
         (%s.spec %a)@]@ @ "
        f.name params f
        (list (fun ft r ->
             pf ft "%s.r_%s O %a" f.name
               (id
                  (rule_name f
                     (let _, _, g = r in
                      g)))
               args f))
        rs f.name args f)
    (rule_fns ctx);
  let fields ft mk =
    List.iter (fun f -> pf ft ",\n    %s := %a" f.name mk f) (rule_fns ctx)
  in
  pf ft "@[<v 2>def opsRaw (orc : Oracle) : Ops :=@ { orc := orc%a }@]@ @ "
    fields (fun ft f -> pf ft "fun %a => %s.spec %a" args f f.name args f);
  pf ft "@[<v 2>def opsStep (O : Ops) : Ops :=@ { orc := O.orc%a }@]@ @ " fields
    (fun ft f -> pf ft "%s.step O" f.name);
  pf ft
    "@[<v 2>def opsN (orc : Oracle) : Nat → Ops@ | 0 => opsRaw orc@ | n + 1 => \
     opsStep (opsN orc n)@]@ @ ";
  pf ft "end Bvr@]@."

let statements ~sources ft (p : program) =
  let ctx = classify p in
  header ~sources ft [ "Bvr.Semantics" ];
  pf ft
    "@[<v 2>/-- Every rule function refines its spec. -/@ structure Ops.Sound \
     (FS : FloatSem) (O : Ops) : Prop where@ orc : O.orc.Compat FS";
  List.iter
    (fun f ->
      pf ft "@ %s : ∀ %a, Refines FS (%s.spec %a) (O.%s %a)" f.name params f
        f.name args f f.name args f)
    (rule_fns ctx);
  pf ft "@]@ @ ";
  List.iter
    (fun f ->
      List.iter
        (fun r ->
          let _, _, g = r in
          let n = id (rule_name f g) in
          pf ft
            "@[<v 2>def %s.r_%s.Stmt : Prop :=@ ∀ (FS : FloatSem) (O : Ops), \
             O.Sound FS →@ ∀ %a (res : Term), %s.r_%s O %a = some res →@ \
             Refines FS (%s.spec %a) res@]@ @ "
            f.name n params f f.name n args f f.name args f)
        (rules f))
    (rule_fns ctx);
  pf ft "end Bvr@]@."

let soundness ~sources ~proofs ft (p : program) =
  let ctx = classify p in
  header ~sources ft ("Bvr.Statements" :: proofs);
  List.iter
    (fun f ->
      pf ft
        "@[<v 2>theorem %s.step_sound (FS : FloatSem) (O : Ops) (hO : O.Sound \
         FS) %a :@ Refines FS (%s.spec %a) (%s.step O %a) := by@ unfold \
         %s.step@ "
        f.name params f f.name args f f.name args f f.name;
      List.iter
        (fun r ->
          let _, _, g = r in
          let n = id (rule_name f g) in
          pf ft
            "refine Refines.firstSome_cons (fun res h => %s.r_%s.proof FS O hO \
             %a res h) ?_@ "
            f.name n args f)
        (rules f);
      pf ft "exact Refines.firstSome_nil@]@ @ ")
    (rule_fns ctx);
  pf ft
    "@[<v 2>/-- Every rule function refines its spec, for any amount of fuel. \
     -/@ theorem opsN_sound (FS : FloatSem) (orc : Oracle) (h : orc.Compat FS) \
     :@ ∀ n, (opsN orc n).Sound FS@ | 0 =>\n\
    \    { orc := h";
  List.iter
    (fun f -> pf ft ",\n      %s := fun %a => Refines.refl" f.name args f)
    (rule_fns ctx);
  pf ft
    " }\n\
    \  | n + 1 =>\n\
    \    have hO := opsN_sound FS orc h n\n\
    \    { orc := hO.orc";
  List.iter
    (fun f -> pf ft ",\n      %s := %s.step_sound FS _ hO" f.name f.name)
    (rule_fns ctx);
  pf ft " }@]@ @ end Bvr@]@."
