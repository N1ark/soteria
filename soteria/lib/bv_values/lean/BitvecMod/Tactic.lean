import BitvecMod.Statements

/-!
# The rule tactic of the bitvec module

`kanon_auto`, with the widths of the sorts of bit-vectors made explicit:

- `bv_tys` identifies the sorts that the hypotheses give the same terms
  (`S.ty x = sort (TBitVector n)` twice gives the same `n`);
- `bv_widths` replaces each width `Values.width τ` of a sort `τ` of bit-vectors
  or locations of width `n` (by `rfl` or a hypothesis `τ = sort s`) by
  `n.toNat` (`width_eq`, in an environment of the context), each size
  `size_of_ty τ` by `n`, and each `(↑k : Int).toNat` by `k`, generalizing them
  first, as they are the widths of the types of other terms (which `simp`
  cannot rewrite);
- `bv_auto` is `kanon_rule` with these steps before the closing ones.
-/

noncomputable section

namespace BitvecMod

open Classical Kanon


section
variable {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [Lang S]

theorem size_of_eq {τ : S.Ty} {s : Srt} {n : Int} (hτ : τ = sort s)
    (hs : s = .TBitVector n ∨ s = .TLoc n) : size_of_ty τ = n := by
  subst hτ; rcases hs with rfl | rfl <;> simp

end

open Lean Meta Elab Tactic in
/-- For `X`, a sort of bit-vectors or locations `s` of width `n`: `s`, `n`, and whether it is
one of bit-vectors. -/
def srtWidth? (X : Expr) : MetaM (Option (Expr × Expr × Bool)) := do
  let X ← whnfR (← instantiateMVars X)
  let .app f s := X | return none
  let isInj := match f with
    | .proj ``Kanon.Embed 0 _ => true
    | _ => f.isAppOfArity ``Kanon.Embed.inj 3
  unless isInj do return none
  let s ← whnfR s
  if s.isAppOfArity ``BitvecMod.Srt.TBitVector 1 then return some (s, s.getArg! 0, true)
  if s.isAppOfArity ``BitvecMod.Srt.TLoc 1 then return some (s, s.getArg! 0, false)
  return none

open Lean Meta Elab Tactic in
/-- For `X`, a sort of bit-vectors or locations by `rfl` or by a hypothesis
`X = sort s`: the proof of `X = sort s`, the proof of
`s = .TBitVector n ∨ s = .TLoc n`, and the width `n`. -/
def srtOf? (X : Expr) : TacticM (Option (Expr × Expr × Expr)) := withMainContext do
  let mut found := none
  if let some r ← srtWidth? X then
    found := some (← mkEqRefl X, r)
  else
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let some (_, l, r) := (← instantiateMVars d.type).eq? | continue
      if l == X then
        if let some w ← srtWidth? r then found := some (d.toExpr, w); break
      if r == X then
        if let some w ← srtWidth? l then found := some (← mkEqSymm d.toExpr, w); break
  let some (hτ, s, n, b) := found | return none
  let e1 ← mkEq s (mkApp (mkConst ``BitvecMod.Srt.TBitVector) n)
  let e2 ← mkEq s (mkApp (mkConst ``BitvecMod.Srt.TLoc) n)
  let hs ← if b then mkAppOptM ``Or.inl #[e1, e2, ← mkEqRefl s]
    else mkAppOptM ``Or.inr #[e1, e2, ← mkEqRefl s]
  return some (hτ, hs, n)

open Lean Meta Elab Tactic in
/-- A proof of `W = W'`, for `W` a width `Values.width X` (`W'` is `n.toNat`, in an
environment of the context), a size `size_of_ty X` (`n`) of a sort `X` of
bit-vectors or locations of width `n`, `(↑k : Int).toNat` (`k`), `(↑a + ↑b : Int).toNat` (`a + b`), or the `toNat` of a literal. -/
def depProof? (W : Expr) : TacticM (Option Expr) := withMainContext do
  try
    if W.isAppOfArity ``Int.toNat 1 && W.appArg!.isAppOfArity ``Nat.cast 3 then
      return some (← mkAppM ``Int.toNat_natCast #[W.appArg!.appArg!])
    if W.isAppOfArity ``Int.toNat 1 && W.appArg!.isAppOfArity ``HAdd.hAdd 6 then
      -- a sum of natural numbers
      let a := W.appArg!.getArg! 4
      let b := W.appArg!.getArg! 5
      if a.isAppOfArity ``Nat.cast 3 && b.isAppOfArity ``Nat.cast 3 then
        let W' ← mkAppM ``HAdd.hAdd #[a.appArg!, b.appArg!]
        let mv ← mkFreshExprMVar (← mkEq W W')
        let gs ← Tactic.run mv.mvarId! (evalTactic (← `(tactic| omega)))
        unless gs.isEmpty do return none
        return some (← instantiateMVars mv)
    if W.isAppOfArity ``Int.toNat 1 then
      -- a literal width
      let some k := (← instantiateMVars W.appArg!).int? | return none
      unless 0 ≤ k do return none
      let W' := mkNatLit k.toNat
      return some (← mkExpectedTypeHint (← mkEqRefl W') (← mkEq W W'))
    if W.isAppOfArity ``BitvecMod.size_of_ty 5 then
      let some (hτ, hs, _) ← srtOf? W.appArg! | return none
      return some (← mkAppM ``BitvecMod.size_of_eq #[hτ, hs])
    unless W.isAppOfArity ``BitvecMod.Values.width 3 do return none
    let envTy := mkApp (mkConst ``Kanon.Dom.Env) (W.getArg! 0)
    let mut ρ? := none
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      if ← isDefEq d.type envTy then ρ? := some d.toExpr; break
    let some ρ := ρ? | return none
    let some (hτ, hs, n) ← srtOf? (W.getArg! 2) | return none
    let zero ← mkAppOptM ``OfNat.ofNat #[mkConst ``Int, mkRawNatLit 0, none]
    let hn ← mkFreshExprMVar (← mkAppM ``LT.lt #[zero, n])
    let gs ← Tactic.run hn.mvarId! (evalTactic (← `(tactic| omega)))
    unless gs.isEmpty do return none
    return some (← mkAppM ``BitvecMod.width_eq #[ρ, hτ, hs, hn])
  catch _ => return none

open Lean Meta Elab Tactic in
/-- Replaces a term `W` (see `depProof?`) by its value, everywhere: it is
generalized, then substituted, as `simp` cannot rewrite the widths of the types of
other terms. -/
def bvWidthStep : TacticM Bool := withMainContext do
  let g ← getMainGoal
  let mut exprs := #[← instantiateMVars (← g.getType)]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then exprs := exprs.push (← instantiateMVars d.type)
  let mut seen : Std.HashSet Expr := {}
  for e in exprs do
    for W in Kanon.Proof.closedSubterms e #[] do
      unless (W.isAppOfArity ``BitvecMod.Values.width 3 ||
          W.isAppOfArity ``BitvecMod.size_of_ty 5 || W.isAppOfArity ``Int.toNat 1) &&
        !seen.contains W do continue
      seen := seen.insert W
      let s ← saveState
      let some pf ← depProof? W | s.restore; continue
      try
        -- `W' = W`, which becomes `W' = kanon_m`, so that `subst` eliminates `kanon_m`
        let pf ← mkEqSymm pf
        let (_, g) ← (← g.assert `kanon_hw (← inferType pf) pf).intro1P
        let g ← g.withContext do
          let hyps := (← getLCtx).foldl (init := #[]) fun acc d =>
            if d.isImplementationDetail then acc else acc.push d.fvarId
          let (_, _, g) ← g.generalizeHyp #[{ expr := W, xName? := `kanon_m, hName? := `kanon_hm }] hyps
          pure g
        replaceMainGoal [g]
        evalTactic (← `(tactic| (subst $(mkIdent `kanon_hw); clear $(mkIdent `kanon_hm))))
        return true
      catch _ => s.restore
  return false

open Lean Meta Elab Tactic in
partial def bvWidths : TacticM Unit := do
  if ← bvWidthStep then bvWidths

open Lean Meta Elab Tactic in
elab "bv_widths" : tactic => do
  let gs ← getGoals
  let mut out := []
  for g in gs do
    setGoals [g]
    bvWidths
    out := out ++ (← getGoals)
  setGoals out

section
variable {D : Kanon.Dom} [KanonBool.Values D] [Values D]
@[simp, kanon_val] theorem asBV_ofBV (n : Nat) (r : Option (BitVec n)) :
    asBV n (ofBV (D := D) n r) = r := by
  cases r <;> simp [ofBV]
end

open Lean Meta Elab Tactic in
/-- The hypotheses `S.ty x = e` (or `e = S.ty x`) on a term variable `x`. -/
def tyHyps (g : MVarId) : MetaM (Array FVarId) := g.withContext do
  let isTyVar (e : Expr) : Bool :=
    e.isAppOfArity ``Kanon.Sem.ty 2 && e.appArg!.isFVar
  let mut out := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let some (_, a, b) := ty.eq? then
      if (isTyVar a && !b.containsFVar a.appArg!.fvarId!) ||
          (isTyVar b && !a.containsFVar b.appArg!.fvarId!) then
        out := out.push d.fvarId
  return out

open Lean Meta Elab Tactic in
/-- Rewrites, in the other hypotheses and the goal, the sorts of the term
variables that a hypothesis gives (`S.ty x = e`); the hypothesis is kept. -/
elab "bv_rw_tys" : tactic => do
  for h in ← tyHyps (← getMainGoal) do
    withMainContext do
    let some d := (← getLCtx).find? h | return
    let some (_, a, _) := (← instantiateMVars d.type).eq? | return
    let hs ← Term.exprToSyntax d.toExpr
    let stx ← if a.isAppOfArity ``Kanon.Sem.ty 2 then `(tactic| simp only [$hs:term])
      else `(tactic| simp only [← $hs:term])
    let { ctx, simprocs, dischargeWrapper, .. } ← mkSimpContext stx (eraseLocal := false)
    let others := (← (← getMainGoal).getNondepPropHyps).filter (· != h)
    try
      dischargeWrapper.with fun dis? => do
        let (r, _) ← simpGoal (← getMainGoal) ctx simprocs dis? true others
        replaceMainGoal (match r with | none => [] | some (_, g) => [g])
    catch _ => pure ()

/-- The sorts that the hypotheses give the same terms, identified. -/
macro "bv_tys" : tactic => `(tactic| (
  (try bv_rw_tys)
  (try simp only [Kanon.Embed.inj_eq_iff, Srt.TBitVector.injEq, Srt.TLoc.injEq, reduceCtorEq] at *)
  (try subst_vars)))

set_option hygiene false in
macro "bv_sem" : tactic => `(tactic| (
  kanon_sem_core
  all_goals (try bv_tys)
  all_goals (try bv_widths)
  all_goals (try simp only [kanon_val, Option.some.injEq, reduceCtorEq, false_and, and_false,
    ite_true, ite_false, Bool.not_true, Bool.not_false, Option.ite_none_left_eq_some,
    Option.ite_none_right_eq_some, Sigma.mk.injEq] at e ⊢)
  all_goals (try subst e)
  all_goals (try (kanon_split; subst_vars))
  all_goals (try simp only [heq_eq_eq] at *)
  all_goals (try subst_vars)
  all_goals first
    | kanon_close
    | ((repeat' split at e) <;> (repeat' split) <;> kanon_close)
    | skip))

macro "bv_auto" : tactic => `(tactic| (
  (try intro _)
  intros
  kanon_rule_lift
  all_goals kanon_on_refines (
    refine Kanon.Sem.Refines.intro ?_ ?_
    · kanon_wt
    bv_sem)))

end BitvecMod
