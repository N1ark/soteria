import Lean
import Kanon.Lib.Den

/-!
# Meta-level tactics

- `kanon_cases` (Kanon's) splits on the values of the atoms of the goal and
  hypotheses: the applications of `den`, `denB`, `evalBV` and `evalB` that are
  left once the structure of the terms is unfolded (`den_cases`, …).
- `kanon_destruct_tys` destructs the term variables whose type is constrained.
- `kanon_nat_widths` makes the widths of bit-vector types natural numbers.
-/

namespace Kanon.Lib

open Lean Meta Elab Tactic

@[kanon_atom_cases] theorem den_cases {FS ρ n t} :
    den FS ρ n t = none ∨ ∃ x, den FS ρ n t = some x := Option.eq_none_or_eq_some _
@[kanon_atom_cases] theorem denB_cases {FS ρ t} :
    denB FS ρ t = none ∨ ∃ b, denB FS ρ t = some b := Option.eq_none_or_eq_some _
@[kanon_atom_cases] theorem evalBV_cases {FS ρ n t} :
    evalBV FS ρ n t = none ∨ ∃ x, evalBV FS ρ n t = some x := Option.eq_none_or_eq_some _
@[kanon_atom_cases] theorem evalB_cases {FS ρ t} :
    evalB FS ρ t = none ∨ ∃ b, evalB FS ρ t = some b := Option.eq_none_or_eq_some _

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

open Lean Meta Elab Tactic in
/-- `Kanon.Proof.liftGoal`, which leaves the goals that are not refinements (the
`Nonzero v'` of the lifting lemmas of the rule functions with an operand at a subsort)
instead of failing on them. -/
partial def liftGoalSide : TacticM (List MVarId) := do
  let g ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← g.getType))
  unless ty.isAppOfArity ``Kanon.Sem.Refines 3 do return [g]
  match ← Kanon.Proof.liftLemma? (ty.getArg! 2) with
  | some l =>
    evalTactic (← `(tactic| apply $(mkCIdent l) (by assumption)))
    let mut out := []
    for g' in ← getGoals do
      unless ← g'.isAssigned do
        setGoals [g']
        out := out ++ (← liftGoalSide)
    return out
  | none =>
    evalTactic (← `(tactic| exact Kanon.Sem.Refines.refl))
    return []

open Lean Meta Elab Tactic in
/-- `kanon_lift_body` (Kanon's), with the goals of the subsorts left after the others. They
only hold of well-typed terms, so when there are any, the lifting is done under the
hypothesis `kw` that the spec is well-typed. -/
elab "kanon_lift_body_side" : tactic => do
  let s ← saveState
  evalTactic (← `(tactic| apply Kanon.Sem.Refines.of_lift))
  let hl :: rest ← getGoals | throwError "kanon_lift_body_side: no goal"
  setGoals [hl]
  let out ← liftGoalSide
  if out.isEmpty then setGoals rest
  else
    s.restore
    evalTactic (← `(tactic| refine Kanon.Sem.Refines.of_WT (fun $(mkIdent `kw) => ?_)))
    evalTactic (← `(tactic| apply Kanon.Sem.Refines.of_lift))
    let hl :: rest ← getGoals | throwError "kanon_lift_body_side: no goal"
    setGoals [hl]
    let out ← liftGoalSide
    setGoals (rest ++ out)

end Kanon.Lib
