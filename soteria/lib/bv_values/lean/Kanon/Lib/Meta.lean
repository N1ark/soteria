import Lean
import Kanon.Lib.Den

/-!
# Meta-level tactics

- `kanon_cases` splits on the values of the atoms of the goal and hypotheses:
  the applications of `den`, `denB`, `evalBV` and `evalB` that are left once the
  structure of the terms is unfolded.
- `kanon_split` destructs the conjunctions and existentials of the hypotheses.
- `kanon_destruct_tys` destructs the term variables whose type is constrained.
-/

namespace Kanon.Lib

open Lean Meta Elab Tactic

private def isAtom (e : Expr) : Bool :=
  !e.hasLooseBVars && (e.isAppOfArity ``Kanon.Lib.den 4 || e.isAppOfArity ``Kanon.Lib.evalBV 4 ||
    e.isAppOfArity ``Kanon.Lib.evalB 3 || e.isAppOfArity ``Kanon.Lib.denB 3)

/-- Generalizes and case splits every atom. -/
partial def caseAtoms (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let hyps := (← getLCtx).foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail then acc else acc.push d
  let mut cand : Option Expr := ty.find? isAtom
  for d in hyps do
    if cand.isNone then
      cand := (← instantiateMVars d.type).find? isAtom
  match cand with
  | none => return [g]
  | some a =>
    let (_, fvs, g) ← g.generalizeHyp #[{ expr := a, xName? := `a }] (hyps.map (·.fvarId))
    let subgoals ← g.cases fvs[0]!
    subgoals.toList.foldlM (init := []) fun acc sg => return acc ++ (← caseAtoms sg.mvarId)

elab "kanon_cases" : tactic => liftMetaTactic caseAtoms

/-- Destructs the conjunctions and existentials of the hypotheses. -/
partial def splitHyps (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars d.type)
    if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 then
      let subgoals ← g.cases d.fvarId
      return ← subgoals.toList.foldlM (init := []) fun acc sg =>
        return acc ++ (← splitHyps sg.mvarId)
  return [g]

elab "kanon_split" : tactic => liftMetaTactic splitHyps

/-- Destructs the term variables whose type a hypothesis constrains
(`v.ty = e`), so that their type is a variable that can be substituted. -/
partial def destructTys (g : MVarId) : MetaM MVarId := g.withContext do
  let tyVar (e : Expr) : Option FVarId :=
    if e.isAppOfArity ``Kanon.Term.ty 1 && e.appArg!.isFVar then some e.appArg!.fvarId! else none
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let some (_, a, b) := ty.eq? then
      if let some v := tyVar a <|> tyVar b then
        match (← g.cases v).toList with
        | [sg] => return ← destructTys sg.mvarId
        | _ => return g
  return g

elab "kanon_destruct_tys" : tactic => liftMetaTactic fun g => return [← destructTys g]

open Lean Meta Elab Tactic in
/-- Replaces the integer variables `w` with a hypothesis `0 < w` (the widths of
bit-vector types) by natural numbers. -/
partial def natWidths (g : MVarId) : MetaM MVarId := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOfArity ``LT.lt 4 && (ty.getArg! 3).isFVar do continue
    unless ← isDefEq (ty.getArg! 0) (mkConst ``Int) do continue
    unless ← isDefEq (ty.getArg! 2) (toExpr (0 : Int)) do continue
    let pf ← mkAppM ``Int.eq_ofNat_of_zero_le #[← mkAppM ``Int.le_of_lt #[d.toExpr]]
    let (h, g) ← (← g.assert `hw (← inferType pf) pf).intro1P
    let [sg] := (← g.cases h).toList | return g
    let heq := sg.fields[1]!.fvarId!
    let some sg' ← observing? (subst sg.mvarId heq) | return sg.mvarId
    return ← natWidths sg'
  return g

open Lean Meta Elab Tactic in
elab "kanon_nat_widths" : tactic => liftMetaTactic fun g => return [← natWidths g]

end Kanon.Lib
