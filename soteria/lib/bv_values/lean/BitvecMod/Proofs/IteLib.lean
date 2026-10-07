import BitvecMod.Lift

/-!
# The arms that distribute an operation over conditionals

`bv_ite_arm` proves the arms `op (Ite b l r) … ⊑ Bool.ite b (op l …) (op r …)` (and with both
operands conditionals on the same guard) without arithmetic: the typing by the typing rules of
the nodes, the value by a case split on the value of the guard, the evaluations of the two sides
being then the same up to the types that give their widths (`ite_align`), and up to the checks
of overflow that the right-hand side drops (`ite_ckOp_unchecked`).
-/

noncomputable section

namespace BitvecMod

open Classical Kanon

/-- A checked operation that has a value has the same value unchecked. -/
theorem ite_ckOp_unchecked {D : Kanon.Dom} [Values D] {n : Nat} {c : CoreMod.Checked}
    {so uo : BitVec n → BitVec n → Bool} {f : BitVec n → BitVec n → BitVec n}
    {x y : Option (BitVec n)} {v : D.Val} (h : ofBV n (ckOp c so uo f x y) = some v) :
    ofBV n (ckOp ⟨false, false⟩ so uo f x y) = some v := by
  cases x <;> cases y <;> simp only [ckOp, ofBV, Option.map_none, reduceCtorEq] at h ⊢
  split at h
  · simp only [Option.map_none, reduceCtorEq] at h
  · simpa only [Bool.false_and, Bool.or_false, Bool.false_eq_true, ↓reduceIte] using h

open Lean Meta Elab Tactic in
/-- A proof of `a = b` by a chain of the equations of the context at the type of `a`, either way
round, if there is one. -/
def iteTyPath (a b : Expr) : MetaM (Option Expr) := do
  let α ← instantiateMVars (← inferType a)
  let mut edges : Array (Expr × Expr × Expr) := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let some (β, l, r) := (← instantiateMVars d.type).eq? | continue
    unless β == α do continue
    edges := edges.push (l, r, d.toExpr)
    edges := edges.push (r, l, ← mkEqSymm d.toExpr)
  let mut seen : Array Expr := #[a]
  let mut todo : Array (Expr × Expr) := #[(a, ← mkEqRefl a)]
  while !todo.isEmpty do
    let (x, px) := todo[0]!
    todo := todo.eraseIdx! 0
    if x == b then return some px
    for (l, r, p) in edges do
      if l == x && !seen.contains r then
        seen := seen.push r
        todo := todo.push (r, ← mkEqTrans px p)
  return none

/-- The types whose widths `e` mentions (`Values.width τ`, closed ones). -/
partial def iteWidthArgs (e : Lean.Expr) (acc : Array Lean.Expr) : Array Lean.Expr :=
  if e.hasLooseBVars then acc
  else if e.isAppOfArity ``BitvecMod.Values.width 3 then
    (if acc.contains e.appArg! then acc else acc.push e.appArg!)
  else match e with
    | .app f a => iteWidthArgs a (iteWidthArgs f acc)
    | .mdata _ b => iteWidthArgs b acc
    | _ => acc

open Lean Meta Elab Tactic in
/-- Rewrites the types whose widths the hypothesis `h` mentions into those of the goal that the
equations of the context make equal to them (all the occurrences at once, so that the terms
whose types depend on these widths follow). -/
elab "ite_align " h:ident : tactic => withMainContext do
  let goalTys := iteWidthArgs (← instantiateMVars (← getMainTarget)) #[]
  let some d := (← getLCtx).findFromUserName? h.getId | throwError "ite_align: no {h}"
  for t in iteWidthArgs (← instantiateMVars d.type) #[] do
    if goalTys.contains t then continue
    for u in goalTys do
      let some p ← iteTyPath t u | continue
      withMainContext do
        let some d := (← getLCtx).findFromUserName? h.getId | throwError "ite_align: no {h}"
        let g ← getMainGoal
        let r ← g.rewrite (← instantiateMVars d.type) p
        let res ← g.replaceLocalDecl d.fvarId r.eNew r.eqProof
        replaceMainGoal (res.mvarId :: r.mvarIds)
      break
  withMainContext do
  let some d := (← getLCtx).findFromUserName? h.getId | throwError "ite_align: no {h}"
  let hTys := iteWidthArgs (← instantiateMVars d.type) #[]
  for t in iteWidthArgs (← instantiateMVars (← getMainTarget)) #[] do
    if hTys.contains t then continue
    for u in hTys do
      let some p ← iteTyPath t u | continue
      withMainContext do
        let g ← getMainGoal
        let r ← g.rewrite (← instantiateMVars (← getMainTarget)) p
        let g' ← g.replaceTargetEq r.eNew r.eqProof
        replaceMainGoal (g' :: r.mvarIds)
      break

/-- An arm that distributes an operation over the branches of conditionals on the same guard. -/
macro "bv_ite_arm" : tactic => `(tactic| (
  kanon_rule_lift
  all_goals (
    refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
    all_goals simp only [WT_mk, KanonBool.WT_mk, Node.wt, KanonBool.Node.wt, Node.All,
      KanonBool.Node.All, ty_mk, KanonBool.ty_mk] at w ⊢
    all_goals (try kanon_split)
    all_goals (try subst_vars)
    all_goals (try kanon_split)
    all_goals (try subst_vars)
    · simp_all
    · simp only [ev_mk, KanonBool.ev_mk, Node.map, KanonBool.Node.map, Node.eval,
        KanonBool.Node.eval, KanonBool.pite, ty_mk, KanonBool.ty_mk] at e ⊢
      split
      · rename_i h; simp only [h, ↓reduceIte] at e
        (try subst_vars)
        ite_align e
        first | exact e | exact ite_ckOp_unchecked e | (simp only [asBV_bv] at e ⊢; first | exact e | exact ite_ckOp_unchecked e) | simp_all
      · rename_i h; simp only [h, ↓reduceIte] at e ⊢; split
        · rename_i h'; simp only [h', ↓reduceIte] at e
          (try subst_vars)
          ite_align e
          first | exact e | exact ite_ckOp_unchecked e | (simp only [asBV_bv] at e ⊢; first | exact e | exact ite_ckOp_unchecked e) | simp_all
        · rename_i h'; simp_all)))

end BitvecMod
