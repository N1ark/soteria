import Lean
import Bvr.Lib.BV

/-!
# Meta-level tactics

- `bvr_cases` splits on the values of the atoms of the goal and hypotheses:
  the applications of `den`, `evalBV` and `evalB` that are left once the
  structure of the terms is unfolded.
- `bvr_split` destructs the conjunctions and existentials of the hypotheses.
- `bvr_destruct_tys` destructs the term variables whose type is constrained.
-/

namespace Bvr.Lib

open Lean Meta Elab Tactic

private def isAtom (e : Expr) : Bool :=
  e.isAppOfArity ``Bvr.Lib.den 4 || e.isAppOfArity ``Bvr.Lib.evalBV 4 ||
    e.isAppOfArity ``Bvr.Lib.evalB 3

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

elab "bvr_cases" : tactic => liftMetaTactic caseAtoms

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

elab "bvr_split" : tactic => liftMetaTactic splitHyps

/-- Destructs the term variables whose type a hypothesis constrains
(`v.ty = e`), so that their type is a variable that can be substituted. -/
partial def destructTys (g : MVarId) : MetaM MVarId := g.withContext do
  let tyVar (e : Expr) : Option FVarId :=
    if e.isAppOfArity ``Bvr.Term.ty 1 && e.appArg!.isFVar then some e.appArg!.fvarId! else none
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let some (_, a, b) := ty.eq? then
      if let some v := tyVar a <|> tyVar b then
        match (← g.cases v).toList with
        | [sg] => return ← destructTys sg.mvarId
        | _ => return g
  return g

elab "bvr_destruct_tys" : tactic => liftMetaTactic fun g => return [← destructTys g]

end Bvr.Lib
