import Lean
import Tiny.Lemmas

/-!
# Meta-level tactics

- `kanon_split` destructs the conjunctions and existentials of the hypotheses.
- `kanon_cases` splits on the values of the atoms of the goal and hypotheses:
  the evaluations `ev ρ x` of the terms `x` that are not nodes (the variables
  of the rule), and the values `ρ i` of the variables of the language. An atom
  of a known type (a hypothesis `x.ty = .TInt` or `x.ty = .TBool`, with
  `x.WT`) is poison or a value of that type; the others are poison or any
  value.
-/

namespace Tiny.Lib

open Lean Meta Elab Tactic

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

private def isEvAtom (e : Expr) : Bool :=
  !e.hasLooseBVars && e.isAppOfArity ``Tiny.ev 2 && !e.appArg!.isAppOf ``Tiny.Term.mk

private partial def subterms (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc := acc.push e
  match e with
  | .app f a => subterms a (subterms f acc)
  | .mdata _ b => subterms b acc
  | _ => acc

/-- The first atom of the goal or of the hypotheses. -/
def findAtom (g : MVarId) : MetaM (Option Expr) := g.withContext do
  let mut exprs := #[← instantiateMVars (← g.getType)]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then exprs := exprs.push (← instantiateMVars d.type)
  for e in exprs do
    if let some a := e.find? isEvAtom then return some a
  -- the values of the variables of the language, `ρ i`
  for e in exprs do
    for s in subterms e #[] do
      if !s.hasLooseBVars && s.isApp && s.appFn!.isFVar then
        if (← inferType s.appFn!).isConstOf ``Tiny.Env then return some s
  return none

/-- The hypothesis of the context of type `t`, if any. -/
def findHyp (t : Expr) : MetaM (Option Expr) := do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if ← isDefEq (← instantiateMVars d.type) t then return some d.toExpr
  return none

/-- Generalizes the first atom of the goal, with a hypothesis `kanon_hc` on its
possible values, destructed by `rcases` with the returned pattern. -/
def generalizeAtom (g : MVarId) : MetaM (Option (MVarId × Nat)) := g.withContext do
  let some a ← findAtom g | return none
  let (pf, pat) ← do
    if a.isAppOfArity ``Tiny.ev 2 then
      let ρ := a.appFn!.appArg!
      let x := a.appArg!
      let wt ← mkAppM ``Tiny.Term.WT #[x]
      let tyx ← mkAppM ``Tiny.Term.ty #[x]
      let hw ← findHyp wt
      let hi ← findHyp (← mkEq tyx (mkConst ``Tiny.Ty.TInt))
      let hb ← findHyp (← mkEq tyx (mkConst ``Tiny.Ty.TBool))
      match hw, hi, hb with
      | some hw, some hi, _ =>
        pure (← mkAppOptM ``Tiny.ev_int #[ρ, x, hw, hi], 0)
      | some hw, _, some hb =>
        pure (← mkAppOptM ``Tiny.ev_bool #[ρ, x, hw, hb], 1)
      | _, _, _ => pure (← mkAppOptM ``Tiny.ev_opt #[ρ, x], 2)
    else
      pure (← mkAppM ``Tiny.val_cases #[a], 3)
  let (_, g) ← (← g.assert `kanon_hc (← inferType pf) pf).intro1P
  g.withContext do
    let hyps := (← getLCtx).foldl (init := #[]) fun acc d =>
      if d.isImplementationDetail then acc else acc.push d.fvarId
    let (_, _, g) ← g.generalizeHyp #[{ expr := a, xName? := `a }] hyps
    return some (g, pat)

/-- Splits the goal on the value of its first atom. -/
def caseAtom (g : MVarId) : TacticM (Option (List MVarId)) := do
  let some (g, pat) ← generalizeAtom g | return none
  setGoals [g]
  let h := mkIdent `kanon_hc
  let r := mkIdent `rfl
  g.withContext do
    match pat with
    | 1 => evalTactic (← `(tactic| rcases $h:ident with $r:ident | $r:ident | $r:ident))
    | 3 => evalTactic (← `(tactic| rcases $h:ident with $r:ident | ⟨_, $r:ident⟩ | ⟨_, $r:ident⟩))
    | _ => evalTactic (← `(tactic| rcases $h:ident with $r:ident | ⟨_, $r:ident⟩))
  return some (← getGoals)

/-- Splits the goals on the values of all their atoms. -/
partial def caseAtoms (g : MVarId) : TacticM (List MVarId) := do
  match ← caseAtom g with
  | none => return [g]
  | some gs => gs.foldlM (init := []) fun acc g => return acc ++ (← caseAtoms g)

elab "kanon_cases" : tactic => do
  let gs ← getGoals
  let mut out := []
  for g in gs do
    out := out ++ (← caseAtoms g)
  setGoals out

end Tiny.Lib
