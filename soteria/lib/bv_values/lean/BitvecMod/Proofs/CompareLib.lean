import BitvecMod.Proofs.Common

/-!
# The lemmas and tactics of the comparisons and of the bool rules on bit-vectors

`cmp_rule` proves an arm as `kanon_rule` does, with the widths of the operands
unified (`bv_rw_tys`) and the values of typed bit-vectors read at the width of
their sort (`cmp_exists_vbv`).
-/

noncomputable section

namespace BitvecMod

open Classical Kanon

set_option linter.unusedSectionVars false

section
variable {D : Kanon.Dom} [KanonBool.Values D] [Values D]

theorem cmp_ofBV_ite (n : Nat) (c : Prop) [Decidable c] (r : Option (BitVec n)) :
    ofBV (D := D) n (if c then none else r) = if c then none else ofBV n r := by
  split <;> rfl

theorem cmp_asBV_ite (n : Nat) (c : Prop) [Decidable c] (r : Option D.Val) :
    asBV n (if c then none else r) = if c then none else asBV n r := by
  split <;> rfl

theorem cmp_asB_ite (c : Prop) [Decidable c] (r : Option D.Val) :
    asB (if c then none else r) = if c then none else asB r := by
  split <;> rfl

theorem cmp_ofB_ite (c : Prop) [Decidable c] (r : Option Bool) :
    ofB (D := D) (if c then none else r) = if c then none else ofB r := by
  split <;> rfl

theorem cmp_withW_ite (c : Prop) [Decidable c] (r : Option D.Val) (k : Nat → Option D.Val) :
    withW (if c then none else r) k = if c then none else withW r k := by
  split <;> rfl

theorem cmp_binB_ite_l {α : Type} {f : α → α → Bool} (c : Prop) [Decidable c] (a b : Option α) :
    binB f (if c then none else a) b = if c then none else binB f a b := by
  split <;> rfl

theorem cmp_binB_ite_r {α : Type} {f : α → α → Bool} (c : Prop) [Decidable c] (a b : Option α) :
    binB f a (if c then none else b) = if c then none else binB f a b := by
  split <;> simp

theorem cmp_binOp_ite_l {n : Nat} {f : BitVec n → BitVec n → BitVec n} (c : Prop) [Decidable c]
    (a b : Option (BitVec n)) : binOp f (if c then none else a) b = if c then none else binOp f a b := by
  split <;> rfl

theorem cmp_binOp_ite_r {n : Nat} {f : BitVec n → BitVec n → BitVec n} (c : Prop) [Decidable c]
    (a b : Option (BitVec n)) : binOp f a (if c then none else b) = if c then none else binOp f a b := by
  split <;> simp

theorem cmp_map_ite {α β : Type} (f : α → β) (c : Prop) [Decidable c] (a : Option α) :
    (if c then none else a).map f = if c then none else a.map f := by
  split <;> rfl

theorem cmp_slt_zero {n : Nat} (x : BitVec n) : x.slt (BitVec.ofInt n 0) = x.msb := by
  rw [show BitVec.ofInt n 0 = 0#n by apply BitVec.eq_of_toNat_eq; simp]
  exact BitVec.slt_zero_eq_msb

theorem cmp_toInt_lt_zero {n : Nat} (x : BitVec n) :
    (x.toInt < (BitVec.ofInt n 0).toInt) = (x.msb = true) := by
  rw [← cmp_slt_zero, BitVec.slt]; simp

theorem cmp_pite_none {V : Type} (vb : Bool → V) (a b : Option V) :
    KanonBool.pite vb none a b = none := by
  simp [KanonBool.pite]

theorem cmp_ofInt_two_pow_pred {n : Nat} (hn : 0 < n) :
    BitVec.ofInt n (2 ^ (n - 1)) = BitVec.intMin n := by
  have e : (2 : Int) ^ (n - 1) = ((2 ^ (n - 1) : Nat) : Int) := by push_cast; rfl
  rw [e, BitVec.ofInt_natCast, ← BitVec.toNat_inj, BitVec.toNat_intMin_of_pos hn,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.two_pow_pred_lt_two_pow hn)]

theorem cmp_append_inj {w w' : Nat} {a c : BitVec w} {b d : BitVec w'} :
    a ++ b = c ++ d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have h1 := congrArg (fun x => x.extractLsb' w' w) h
    have h2 := congrArg (fun x => x.extractLsb' 0 w') h
    simp only [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem cmp_true_eq (p : Prop) [Decidable p] : (true = decide p) = p := by
  by_cases h : p <;> simp [h]
theorem cmp_false_eq (p : Prop) [Decidable p] : (false = decide p) = ¬p := by
  by_cases h : p <;> simp [h]

theorem cmp_exists_heq {m : Nat} {y : BitVec m} {P : (n : Nat) → BitVec n → Prop} :
    (∃ n x, (m = n ∧ HEq y x) ∧ P n x) ↔ P m y := by
  constructor
  · rintro ⟨n, x, ⟨rfl, h⟩, hp⟩; cases h; exact hp
  · intro h; exact ⟨m, y, ⟨rfl, HEq.rfl⟩, h⟩

theorem cmp_exists_vbv {m : Nat} {y : BitVec m} {P : (n : Nat) → BitVec n → Prop} :
    (∃ n x, (Values.vbv.inj ⟨m, y⟩ : D.Val) = bv n x ∧ P n x) ↔ P m y := by
  simp only [bv, Embed.inj_eq_iff]; exact exists_sigma_eq

end

section
variable {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [Lang S]

theorem cmp_width_bv [Typed S] (ρ : S.Env) {k : Int} (hk : 0 < k) :
    Values.width (D := S.toDom) (sort (.TBitVector k)) = k.toNat :=
  width_sort ρ (.inl rfl) hk

theorem cmp_width_loc [Typed S] (ρ : S.Env) {k : Int} (hk : 0 < k) :
    Values.width (D := S.toDom) (sort (.TLoc k)) = k.toNat :=
  width_sort ρ (.inr rfl) hk

end

namespace Lib

open Lean Meta Elab Tactic

/-- Replaces the integer variables `w` with a hypothesis `0 < w` (the widths of
bit-vector sorts) by natural numbers. -/
partial def natWidths (g : MVarId) : MetaM MVarId := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let isLt := ty.isAppOfArity ``LT.lt 4
    let isLe := ty.isAppOfArity ``LE.le 4
    unless (isLt || isLe) && (ty.getArg! 3).isFVar do continue
    unless ← isDefEq (ty.getArg! 0) (mkConst ``Int) do continue
    unless ← isDefEq (ty.getArg! 2) (toExpr (0 : Int)) do continue
    if isLe then
      -- only the integers whose `toNat` occurs (the widths of extensions)
      let w := ty.getArg! 3
      let mut used := false
      let mut exprs : Array Expr := #[← instantiateMVars (← g.getType)]
      for d' in (← getLCtx) do
        if !d'.isImplementationDetail then exprs := exprs.push (← instantiateMVars d'.type)
      for e in exprs do
        if (e.find? fun s => s.isAppOfArity ``Int.toNat 1 && s.appArg! == w).isSome then used := true
      unless used do continue
    let pf ← if isLe then mkAppM ``Int.eq_ofNat_of_zero_le #[d.toExpr]
      else mkAppM ``Int.eq_ofNat_of_zero_le #[← mkAppM ``Int.le_of_lt #[d.toExpr]]
    let (h, g) ← (← g.assert `hw (← inferType pf) pf).intro1P
    let [sg] := (← g.cases h).toList | return g
    let heq := sg.fields[1]!.fvarId!
    let some sg' ← observing? (subst sg.mvarId heq) | return sg.mvarId
    return ← natWidths sg'
  return g

elab "cmp_nat_widths" : tactic => liftMetaTactic fun g => return [← natWidths g]

/-- Splits the goal on the boolean variables of the context. -/
partial def boolVars (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if (← instantiateMVars d.type).isConstOf ``Bool && d.isLet == false then
      let gs ← g.cases d.fvarId
      return ← gs.toList.foldlM (init := []) fun acc sg => return acc ++ (← boolVars sg.mvarId)
  return [g]

elab "cmp_bool_vars" : tactic => liftMetaTactic boolVars

/-- The environment of the context. -/
def findEnv (S : Expr) : TacticM (Option Expr) := withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``Kanon.Dom.Env 1 then return some d.toExpr
  return none

/-- Substitutes the equations of dependent pairs `⟨a, b⟩ = ⟨n, x⟩` of the
hypotheses, whose right side are variables. -/
partial def sigmaCases (g : MVarId) : MetaM MVarId := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l, r) := ty.eq? | continue
    unless l.isAppOfArity ``Sigma.mk 4 && r.isAppOfArity ``Sigma.mk 4 do continue
    unless (r.getArg! 2).isFVar && (r.getArg! 3).isFVar ||
      (l.getArg! 2).isFVar && (l.getArg! 3).isFVar do continue
    let some gs ← observing? (g.cases d.fvarId) | continue
    let #[sg] := gs | continue
    return ← sigmaCases sg.mvarId
  return g

/-- Splits the conjunctions, disjunctions and existentials of the hypotheses. -/
partial def splitAll (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars d.type)
    if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 || ty.isAppOfArity ``Or 2 then
      let subgoals ← g.cases d.fvarId
      return ← subgoals.toList.foldlM (init := []) fun acc sg =>
        return acc ++ (← splitAll sg.mvarId)
  return [g]

elab "cmp_split_all" : tactic => liftMetaTactic splitAll

/-- Normalizes the widths `(↑n).toNat` of the types of the bit-vector variables to `n`. -/
def normBvTypes (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOfArity ``BitVec 1 do continue
    let k := ty.appArg!
    unless k.isAppOfArity ``Int.toNat 1 do continue
    let c := k.appArg!
    unless c.isAppOfArity ``Nat.cast 3 do continue
    g ← g.replaceLocalDeclDefEq d.fvarId (mkApp (mkConst ``BitVec) c.appArg!)
  return g

elab "cmp_norm_bv_types" : tactic => liftMetaTactic fun g => return [← normBvTypes g]

/-- The terms `v` whose `Bitvec.msb_of v` occurs in the goal or the hypotheses. -/
def msbTerms (g : MVarId) : MetaM (Array Expr) := g.withContext do
  let mut exprs : Array Expr := #[← instantiateMVars (← g.getType)]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then exprs := exprs.push (← instantiateMVars d.type)
  let out ← IO.mkRef (#[] : Array Expr)
  for e in exprs do
    e.forEach' fun sub => do
      if sub.isAppOfArity ``BitvecMod.Bitvec.msb_of 5 && !sub.hasLooseBVars then
        let v := sub.appArg!
        unless (← out.get).contains v do out.modify (·.push v)
      return true
  out.get

/-- Adds, for the terms `v` whose `msb_of` occurs, the bound of their values
(`msb_bound`), in the environment `ρ` of the context. -/
elab "cmp_msb_facts" : tactic => withMainContext do
  for v in ← msbTerms (← getMainGoal) do
    let vs ← Term.exprToSyntax v
    try
      evalTactic (← `(tactic| have := $(mkIdent `BitvecMod.msb_fact) $(mkIdent `ρ) (v := $vs) (by assumption) (by assumption)))
    catch _ => pure ()

/-- Replaces the widths `(↑a + ↑b).toNat` by `a + b` everywhere (also in the types of
other terms, which `simp` cannot rewrite), by generalizing them. -/
def genSumStep : TacticM Bool := withMainContext do
  let g ← getMainGoal
  let mut exprs := #[← instantiateMVars (← g.getType)]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then exprs := exprs.push (← instantiateMVars d.type)
  for e in exprs do
    for W in Kanon.Proof.closedSubterms e #[] do
      unless W.isAppOfArity ``Int.toNat 1 do continue
      let a := W.appArg!
      let pf? : Option (TacticM Expr) :=
        if let some k := a.int? then
          if 0 ≤ k then some (do
            mkExpectedTypeHint (← mkEqRefl W) (← mkEq W (mkNatLit k.toNat)))
          else none
        else if a.isAppOfArity ``HAdd.hAdd 6 && (a.getArg! 4).isAppOfArity ``Nat.cast 3 &&
            (a.getArg! 5).isAppOfArity ``Nat.cast 3 then
          some (mkAppM ``toNat_natCast_add #[(a.getArg! 4).appArg!, (a.getArg! 5).appArg!])
        else none
      -- a width `a` that a hypothesis gives as `↑k`
      let pf? ← if pf?.isSome then pure pf? else do
        let mut r : Option (TacticM Expr) := none
        for d in (← getLCtx) do
          if d.isImplementationDetail then continue
          let some (_, l, rr) := (← instantiateMVars d.type).eq? | continue
          let k? := if rr == a && l.isAppOfArity ``Nat.cast 3 then some l.appArg!
            else if l == a && rr.isAppOfArity ``Nat.cast 3 then some rr.appArg! else none
          let some k := k? | continue
          r := some (do
            let mv ← mkFreshExprMVar (← mkEq W k)
            let gs ← Tactic.run mv.mvarId! (evalTactic (← `(tactic| omega)))
            unless gs.isEmpty do throwError "omega"
            instantiateMVars mv)
          break
        pure r
      let some mkPf := pf? | continue
      let s ← saveState
      try
        let pf ← mkPf
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

partial def genSums : TacticM Unit := do
  if ← genSumStep then genSums

elab "cmp_gen_sums" : tactic => genSums

/-- Clears the equations of integers (or naturals) between non-variables that `omega`
proves: `simp_all` could loop on them (`↑w = ↑w - 1 + 1`), and `omega` has their
premises. -/
elab "cmp_clear_arith_eqs" : tactic => withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let some (ty, l, r) := (← instantiateMVars d.type).eq? | continue
    unless ty.isConstOf ``Int || ty.isConstOf ``Nat do continue
    if l.isFVar || r.isFVar then continue
    let s ← saveState
    try
      let g ← getMainGoal
      let g' ← g.clear d.fvarId
      let mv ← g'.withContext (mkFreshExprMVar d.type)
      let gs ← Tactic.run mv.mvarId! (evalTactic (← `(tactic| omega)))
      unless gs.isEmpty do s.restore; continue
      replaceMainGoal [g']
    catch _ => s.restore

/-- Clears the duplicated propositions of the context, and the trivial ones (`True`,
`¬False`): `simp_all` and `omega` work on every hypothesis. -/
elab "cmp_dedupe" : tactic => withMainContext do
  let mut seen : Std.HashSet Expr := {}
  let mut drop := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    unless (← Meta.isProp t) do continue
    if t.isConstOf ``True || t == mkNot (mkConst ``False) || seen.contains t then
      drop := drop.push d.fvarId
    else seen := seen.insert t
  liftMetaTactic1 fun g => g.tryClearMany drop

/-- The condition of an `if` of the goal, outside binders. -/
def iteCond? (e : Expr) : Option Expr :=
  (e.find? fun s => s.isAppOfArity ``ite 5 && !(s.getArg! 1).hasLooseBVars).map (·.getArg! 1)

/-- Splits the `if`s of the goal by cases on their conditions (whatever their
`Decidable` instances). -/
partial def splitIfs : TacticM Unit := withMainContext do
  let some c := iteCond? (← instantiateMVars (← getMainTarget)) | return
  let cs ← Term.exprToSyntax c
  let h := mkIdent `cmp_hc
  evalTactic (← `(tactic| by_cases $h : $cs))
  let gs ← getGoals
  let mut out := []
  for g in gs do
    setGoals [g]
    evalTactic (← `(tactic| first | rw [if_pos $h] | rw [if_neg $h]))
    evalTactic (← `(tactic| (try rw [if_pos $h]) <;> (try rw [if_neg $h])))
    splitIfs
    out := out ++ (← getGoals)
  setGoals out

elab "cmp_split_ifs" : tactic => do
  let gs ← getGoals
  let mut out := []
  for g in gs do
    setGoals [g]
    try splitIfs catch _ => pure ()
    out := out ++ (← getGoals)
  setGoals out

/-- For the guards `O.bool_sure_neq a b = true`, adds that `a` and `b` have no value in
common in the environment `ρ` (the postcondition of the oracle). -/
elab "cmp_sure_neq_facts" : tactic => withMainContext do
  let mut hO? := none
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if (← instantiateMVars d.type).isAppOf ``BitvecMod.Ops.Sound then hO? := some d.toExpr
  let some hO := hO? | return
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let some (_, l, r) := (← instantiateMVars d.type).eq? | continue
    unless r.isConstOf ``Bool.true && l.isAppOf ``KanonBool.Ops.bool_sure_neq do continue
    let a := l.getArg! (l.getAppNumArgs - 2)
    let b := l.getArg! (l.getAppNumArgs - 1)
    let (hs, as, bs, ds) := (← Term.exprToSyntax hO, ← Term.exprToSyntax a,
      ← Term.exprToSyntax b, ← Term.exprToSyntax d.toExpr)
    try
      evalTactic (← `(tactic| have := ($hs).bool_sure_neq $as $bs $ds (by assumption)
        (by simp only [kanon_wt, true_and, and_true] at *; (try simp_all)
            all_goals first | done | omega | exact Int.pow_pos (by decide))
        (by simp_all) $(mkIdent `ρ)))
    catch _ => pure ()

elab "cmp_sigma_cases" : tactic => liftMetaTactic fun g => return [← sigmaCases g]

end Lib

/-- The typing facts of the hypotheses, split, with the sorts of the terms
substituted. -/
macro "cmp_facts" : tactic => `(tactic| (
  kanon_lits
  kanon_wt_simp
  (try kanon_split)
  (try subst_vars)
  kanon_wt_simp
  (try bv_rw_tys)
  (try simp only [sort_inj_iff, KanonBool.sort_inj_iff, Srt.TBitVector.injEq, Srt.TLoc.injEq,
    sort_Bitvec_ne_Bool, true_and, and_true] at *)
  (try subst_vars)
  (try bv_tys)
  (try simp only [BitvecMod.sort_eq_ty, KanonBool.sort_eq_ty] at *)
  (try cmp_nat_widths)
  (try simp only [Int.toNat_natCast, Int.natCast_pos, Int.natCast_inj, reduceCtorEq, or_false,
    false_or, forall_eq', forall_eq, Srt.TBitVector.injEq, Srt.TLoc.injEq] at *)
  (try kanon_split)))

set_option hygiene false in
/-- Proves that a literal divisor is not zero (the subsort `Nonzero`), from the typing of
the left side (`kw`). -/
macro "cmp_nonzero" : tactic => `(tactic| (
  apply BitvecMod.nonzero_lit
  · simp only [kanon_wt, true_and, and_true] at kw ⊢
    (try kanon_split)
    (try subst_vars)
    (try simp_all)
    all_goals first | done | omega | (exact Int.pow_pos (by decide)) | skip
  · first | assumption | omega | (simp_all; done)))

set_option hygiene false in
/-- The widths of the sorts of bit-vectors (`ρ` in the context). -/
macro "cmp_widths" : tactic => `(tactic| (
  all_goals (try simp only [BitvecMod.Bitvec.size, BitvecMod.size_of_ty_TBitVector,
    BitvecMod.size_of_ty_TLoc] at *)
  all_goals (try cmp_nat_widths)
  all_goals (try bv_widths)
  all_goals (try cmp_gen_sums)))

set_option hygiene false in
/-- The values of the operations, the typed bit-vectors at the widths of their
sorts. -/
macro "cmp_vals" : tactic => `(tactic| (
  all_goals (try simp only [BitvecMod.Srt.val, KanonBool.Srt.val, BitvecMod.asBV_bv,
    BitvecMod.asBV_eq_some, BitvecMod.asB_vbool, BitvecMod.asB_eq_some, BitvecMod.withW_bv,
    BitvecMod.ofBV_some, BitvecMod.ofB_some, BitvecMod.ckOp_some, BitvecMod.binOp_some,
    BitvecMod.negOp_some, BitvecMod.binB_some, BitvecMod.asBV_ofBV, BitvecMod.asBV_none,
    BitvecMod.asB_none, BitvecMod.withW_none, BitvecMod.ofBV_none, BitvecMod.ofB_none,
    BitvecMod.ckOp_none_l, BitvecMod.ckOp_none_r, BitvecMod.binOp_none_l, BitvecMod.binOp_none_r,
    BitvecMod.negOp_none, BitvecMod.binB_none_l, BitvecMod.binB_none_r, KanonBool.pand_eq_some,
    KanonBool.por_eq_some, KanonBool.pnot_eq_some, KanonBool.peq_eq_some, KanonBool.pite_eq_some,
    BitvecMod.cmp_pite_none,
    Kanon.Embed.inj_eq_iff, Kanon.Embed.proj_inj, Option.bind_eq_bind, Option.bind_some,
    Option.bind_none, Option.map_some, Option.map_none, BitvecMod.cmp_ofBV_ite,
    BitvecMod.cmp_asBV_ite, BitvecMod.cmp_asB_ite, BitvecMod.cmp_ofB_ite, BitvecMod.cmp_withW_ite,
    BitvecMod.cmp_binB_ite_l, BitvecMod.cmp_binB_ite_r, BitvecMod.cmp_binOp_ite_l,
    BitvecMod.cmp_binOp_ite_r, BitvecMod.cmp_map_ite, Option.some.injEq, reduceCtorEq, false_and, and_false,
    ite_true, ite_false, Bool.not_true, Bool.not_false, Option.ite_none_left_eq_some,
    Option.ite_none_right_eq_some] at e ⊢)
  cmp_widths))

set_option hygiene false in
/-- The value half of a refinement, split on the values of its atoms, the
typed bit-vectors at the widths of their sorts; its hypothesis is `e`. -/
macro "cmp_sem_core" : tactic => `(tactic| (
  intro ρ v w w' e
  cmp_facts
  (try simp only [kanon_ev] at e ⊢)
  cmp_widths
  (try cmp_msb_facts)
  (try cmp_sure_neq_facts)
  (try simp only [kanon_ev] at *)
  kanon_cases
  all_goals (try simp only [BitvecMod.Srt.val, KanonBool.Srt.val, BitvecMod.asBV_bv,
    BitvecMod.asBV_eq_some, BitvecMod.asB_vbool, BitvecMod.asB_eq_some, BitvecMod.withW_bv,
    BitvecMod.ofBV_some, BitvecMod.ofB_some, BitvecMod.ckOp_some, BitvecMod.binOp_some,
    BitvecMod.negOp_some, BitvecMod.binB_some, BitvecMod.asBV_ofBV, BitvecMod.asBV_none,
    BitvecMod.asB_none, BitvecMod.withW_none, BitvecMod.ofBV_none, BitvecMod.ofB_none,
    BitvecMod.ckOp_none_l, BitvecMod.ckOp_none_r, BitvecMod.binOp_none_l, BitvecMod.binOp_none_r,
    BitvecMod.negOp_none, BitvecMod.binB_none_l, BitvecMod.binB_none_r, KanonBool.pand_eq_some,
    KanonBool.por_eq_some, KanonBool.pnot_eq_some, KanonBool.peq_eq_some, KanonBool.pite_eq_some,
    BitvecMod.cmp_pite_none,
    Kanon.Embed.inj_eq_iff, Kanon.Embed.proj_inj, Option.bind_eq_bind, Option.bind_some,
    Option.bind_none, Option.map_some, Option.map_none] at *)
  all_goals (try (kanon_split; subst_vars))
  cmp_vals
  all_goals (try (kanon_split; subst_vars))
  cmp_vals
  all_goals (try subst e)
  all_goals (try (kanon_split; subst_vars))))

end BitvecMod

/-! ## Reasoning on the integer values of the bit-vectors (option B's `bv_cmp_omega`) -/

namespace BitvecMod.Cmp

open Classical Kanon Prim

/-- The sign bit of `signed_to_unsigned_cmp`. -/
theorem cmp_sign_bit {n : Nat} (hn : 0 < n) :
    BitVec.ofInt n (2 ^ ((n : Int) - 1).toNat) = BitVec.intMin n := by
  have e : (2 : Int) ^ ((n : Int) - 1).toNat = ((2 ^ (n - 1) : Nat) : Int) := by
    push_cast; congr 1; omega
  rw [e, BitVec.ofInt_natCast, ← BitVec.toNat_inj, BitVec.toNat_intMin_of_pos hn,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.two_pow_pred_lt_two_pow hn)]

theorem cmp_binB_ite_l {α : Type} {f : α → α → Bool} {c : Prop} [Decidable c]
    (a a' b : Option α) :
    binB f (if c then a else a') b = if c then binB f a b else binB f a' b := by
  split <;> rfl

theorem cmp_binB_ite_r {α : Type} {f : α → α → Bool} {c : Prop} [Decidable c]
    (a b b' : Option α) :
    binB f a (if c then b else b') = if c then binB f a b else binB f a b' := by
  split <;> rfl

theorem cmp_eq_intMin_iff {n : Nat} (hn : 0 < n) (x : BitVec n) :
    x = BitVec.intMin n ↔ x.toInt = -2 ^ (n - 1) := by
  rw [← BitVec.toInt_inj, BitVec.toInt_intMin_of_pos hn]

/-! ## Facts for `omega` -/

/-- A quotient by `d` is at most `n` when `n * d` overflows. -/
theorem cmp_smtUDiv_ule_of_umulOverflow {w : Nat} {x n d : BitVec w} (h : n.umulOverflow d = true) :
    (x.smtUDiv d).ule n = true := by
  simp only [BitVec.umulOverflow, decide_eq_true_eq] at h
  have hd : d.toNat ≠ 0 := by intro e; rw [e] at h; have := Nat.two_pow_pos w; omega
  have := x.isLt
  simp only [BitVec.ule, decide_eq_true_eq, smtUDiv_toNat hd]
  have : x.toNat < (n.toNat + 1) * d.toNat := by rw [Nat.add_mul]; omega
  have := (Nat.div_lt_iff_lt_mul (by omega)).2 this
  omega

/-! ## Facts for `omega` -/

theorem cmp_toInt_neg_cases {w : Nat} (x : BitVec w) :
    (-x).toInt = -x.toInt ∨ ((-x).toInt = x.toInt ∧ x.toInt = -2 ^ (w - 1)) := by
  rw [BitVec.toInt_neg_eq_ite]
  split
  · next h => subst h; rcases Nat.eq_zero_or_pos w with rfl | hw <;>
      simp [BitVec.toInt_zero_length, BitVec.toInt_intMin_of_pos, *]
  · exact .inl rfl

theorem cmp_toNat_neg_cases {w : Nat} (x : BitVec w) :
    (x.toNat = 0 ∧ (-x).toNat = 0) ∨
      (0 < x.toNat ∧ ((-x).toNat : Int) = 2 ^ w - x.toNat) := by
  rw [BitVec.toNat_neg]
  have := x.isLt
  by_cases h : x.toNat = 0
  · left; simp [h]
  · right; rw [Nat.mod_eq_of_lt (by omega), Int.ofNat_sub (by omega)]; push_cast; omega

theorem cmp_toNat_add_cases {w : Nat} (x y : BitVec w) :
    ((x + y).toNat : Int) = x.toNat + y.toNat ∨
      ((x + y).toNat : Int) = x.toNat + y.toNat - 2 ^ w := by
  have := x.isLt; have := y.isLt
  have e : ((2 ^ w : Nat) : Int) = 2 ^ w := by push_cast; rfl
  rw [BitVec.toNat_add]
  by_cases h : x.toNat + y.toNat < 2 ^ w
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem cmp_toNat_sub_cases {w : Nat} (x y : BitVec w) :
    ((x - y).toNat : Int) = x.toNat - y.toNat ∨
      ((x - y).toNat : Int) = x.toNat - y.toNat + 2 ^ w := by
  have := x.isLt; have := y.isLt
  have e : ((2 ^ w : Nat) : Int) = 2 ^ w := by push_cast; rfl
  rw [BitVec.toNat_sub]
  by_cases h : y.toNat ≤ x.toNat
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem cmp_toNat_bounds {w : Nat} (x : BitVec w) : (x.toNat : Int) < 2 ^ w := by
  have := x.isLt; exact_mod_cast this

theorem cmp_toInt_toNat_cases {w : Nat} (x : BitVec w) :
    (2 * (x.toNat : Int) < 2 ^ w ∧ x.toInt = x.toNat) ∨
      (2 ^ w ≤ 2 * (x.toNat : Int) ∧ x.toInt = x.toNat - 2 ^ w) := by
  have e : ((2 ^ w : Nat) : Int) = 2 ^ w := by push_cast; rfl
  rw [BitVec.toInt_eq_toNat_cond, e]; split <;> omega

/-- The powers of two of a width, for `omega`. -/
theorem cmp_two_pow_facts (w : Nat) :
    ((2 ^ w : Nat) : Int) = (2 : Int) ^ w ∧ ((2 ^ (w - 1) : Nat) : Int) = (2 : Int) ^ (w - 1) ∧
      ((2 : Int) ^ w = 2 * 2 ^ (w - 1) ∨ w = 0) ∧ (0 : Int) < 2 ^ (w - 1) := by
  refine ⟨by push_cast; rfl, by push_cast; rfl, ?_, Int.pow_pos (by decide)⟩
  rcases Nat.eq_zero_or_pos w with h | h
  · exact .inr h
  · exact .inl (by rw [← Int.pow_succ', Nat.sub_add_cancel h])

/-- Cancelling a positive factor, for `omega`. -/
theorem cmp_mul_cmp_facts (p q r : Int) :
    0 < p → (p * q < p * r ↔ q < r) ∧ (p * q ≤ p * r ↔ q ≤ r) := fun h =>
  ⟨Int.mul_lt_mul_left h, Int.mul_le_mul_left h⟩

theorem cmp_nat_mul_cmp_facts (p q r : Nat) :
    0 < p → (p * q < p * r ↔ q < r) ∧ (p * q ≤ p * r ↔ q ≤ r) := fun h =>
  ⟨Nat.mul_lt_mul_left h, Nat.mul_le_mul_left_iff h⟩

/-- `cmp_tdiv_facts`, for natural numbers. -/
theorem cmp_div_facts (C2 C1 X : Nat) : C1 ≠ 0 →
    C2 = C2 / C1 * C1 + C2 % C1 ∧ C2 % C1 < C1 ∧
    (X + 1 ≤ C2 / C1 → X * C1 + C1 ≤ C2 / C1 * C1) ∧
    (C2 / C1 + 1 ≤ X → C2 / C1 * C1 + C1 ≤ X * C1) ∧
    (X = C2 / C1 → X * C1 = C2 / C1 * C1) := by
  intro h
  have e := Nat.div_add_mod C2 C1
  refine ⟨by rw [Nat.mul_comm]; omega, Nat.mod_lt _ (by omega), fun hx => ?_, fun hx => ?_,
    fun hx => by rw [hx]⟩
  · have := Nat.mul_le_mul_right C1 hx; rw [Nat.add_mul, Nat.one_mul] at this; exact this
  · have := Nat.mul_le_mul_right C1 hx; rw [Nat.add_mul, Nat.one_mul] at this; exact this

/-- The truncated quotient `D` of `C2` by `C1` (and its remainder), and how the
products `X * C1` compare to `D * C1`, for `omega`. -/
theorem cmp_tdiv_facts (C2 C1 X : Int) : C1 ≠ 0 →
    C2 = C2.tdiv C1 * C1 + C2.tmod C1 ∧ (0 ≤ C2 → 0 ≤ C2.tmod C1) ∧
    (C2 ≤ 0 → C2.tmod C1 ≤ 0) ∧
    (0 < C1 → -C1 < C2.tmod C1 ∧ C2.tmod C1 < C1) ∧
    (C1 < 0 → C1 < C2.tmod C1 ∧ C2.tmod C1 < -C1) ∧
    (X ≤ C2.tdiv C1 - 1 → (0 < C1 → X * C1 ≤ C2.tdiv C1 * C1 - C1) ∧
      (C1 < 0 → C2.tdiv C1 * C1 - C1 ≤ X * C1)) ∧
    (C2.tdiv C1 + 1 ≤ X → (0 < C1 → C2.tdiv C1 * C1 + C1 ≤ X * C1) ∧
      (C1 < 0 → X * C1 ≤ C2.tdiv C1 * C1 + C1)) ∧
    (X = C2.tdiv C1 → X * C1 = C2.tdiv C1 * C1) := by
  intro h
  have e := Int.tmod_add_tdiv_mul C2 C1
  refine ⟨by omega, fun h => Int.tmod_nonneg _ h, fun h => ?_, fun h => ?_, fun h => ?_,
    fun hx => ⟨fun hc => ?_, fun hc => ?_⟩, fun hx => ⟨fun hc => ?_, fun hc => ?_⟩,
    fun hx => by rw [hx]⟩
  · have := Int.tmod_nonneg C1 (show 0 ≤ -C2 by omega)
    rw [Int.neg_tmod] at this; omega
  · exact ⟨Int.lt_tmod_of_pos _ h, Int.tmod_lt_of_pos _ h⟩
  · have h1 := Int.lt_tmod_of_pos C2 (show 0 < -C1 by omega)
    have h2 := Int.tmod_lt_of_pos C2 (show 0 < -C1 by omega)
    rw [Int.tmod_neg] at h1 h2; omega
  · have := Int.mul_le_mul_of_nonneg_right hx (Int.le_of_lt hc)
    rw [Int.sub_mul, Int.one_mul] at this; exact this
  · have := Int.mul_le_mul_of_nonpos_right hx (Int.le_of_lt hc)
    rw [Int.sub_mul, Int.one_mul] at this; exact this
  · have := Int.mul_le_mul_of_nonneg_right hx (Int.le_of_lt hc)
    rw [Int.add_mul, Int.one_mul] at this; exact this
  · have := Int.mul_le_mul_of_nonpos_right hx (Int.le_of_lt hc)
    rw [Int.add_mul, Int.one_mul] at this; exact this

theorem cmp_toInt_smtSDiv_facts {w : Nat} (a b : BitVec w) : b.toInt ≠ 0 →
    ¬(a.toInt = -2 ^ (w - 1) ∧ b.toInt = -1) → (a.smtSDiv b).toInt = a.toInt.tdiv b.toInt := by
  intro hb hov
  have hb0 : b ≠ 0#w := by rintro rfl; simp at hb
  have hw : 0 < w := by
    rcases Nat.eq_zero_or_pos w with rfl | h
    · simp [BitVec.toInt_zero_length] at hb
    · exact h
  have hb' : -b ≠ 0#w := fun h => hb0 (BitVec.neg_eq_zero_iff.1 h)
  have e : a.smtSDiv b = a.sdiv b := by
    rw [BitVec.smtSDiv_eq, BitVec.sdiv]
    rcases a.msb <;> rcases b.msb <;> simp [BitVec.smtUDiv_eq, hb0, hb']
  rw [e]
  apply BitVec.toInt_sdiv_of_ne_or_ne
  by_cases ha : a = BitVec.intMin w
  · right; rintro rfl
    apply hov
    refine ⟨by rw [ha, BitVec.toInt_intMin_of_pos hw], ?_⟩
    simp [BitVec.neg_one_eq_allOnes, BitVec.toInt_allOnes, hw]
  · exact .inl ha

theorem cmp_toNat_smtUDiv_facts {w : Nat} (a b : BitVec w) : b.toNat ≠ 0 →
    (a.smtUDiv b).toNat = a.toNat / b.toNat := smtUDiv_toNat

/-! ## Adding the facts -/

open Lean Meta in
/-- The subterms `x` of the goal and hypotheses (bit-vectors of any width) such
that `f x` is a subterm, where `p` recognizes `f x` and returns `x`. -/
def cmp_collectArgs (g : MVarId) (p : Expr → Option Expr) : MetaM (Array Expr) := g.withContext do
  let mut exprs : Array Expr := #[← instantiateMVars (← g.getType)]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then exprs := exprs.push (← instantiateMVars d.type)
  let atoms ← IO.mkRef (#[] : Array Expr)
  for e in exprs do
    e.forEach' fun sub => do
      if let some x := p sub then
        unless x.hasLooseBVars || (← atoms.get).contains x do atoms.modify (·.push x)
      return true
  atoms.get

open Lean Meta in
/-- Adds `lem x` for each of the `xs`. -/
def cmp_addFacts (g : MVarId) (lems : List Name) (xs : Array Expr) : MetaM MVarId := do
  let mut g := g
  for x in xs do
    for lem in lems do
      let pf ← g.withContext (mkAppM lem #[x])
      let (_, g') ← (← g.assert `hbd (← g.withContext (inferType pf)) pf).intro1P
      g := g'
  return g

open Lean Meta in
/-- `cmp_collectArgs`, for binary functions. -/
def cmp_collectArgs2 (g : MVarId) (p : Expr → Option (Expr × Expr)) :
    MetaM (Array (Expr × Expr)) := g.withContext do
  let mut exprs : Array Expr := #[← instantiateMVars (← g.getType)]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then exprs := exprs.push (← instantiateMVars d.type)
  let atoms ← IO.mkRef (#[] : Array (Expr × Expr))
  for e in exprs do
    e.forEach' fun sub => do
      if let some (x, y) := p sub then
        unless x.hasLooseBVars || y.hasLooseBVars || (← atoms.get).contains (x, y) do
          atoms.modify (·.push (x, y))
      return true
  atoms.get

open Lean Meta in
/-- Adds `lem x y` for each of the `xys`. -/
def cmp_addFacts2 (g : MVarId) (lem : Name) (xys : Array (Expr × Expr)) : MetaM MVarId := do
  let mut g := g
  for (x, y) in xys do
    let pf ← g.withContext (mkAppM lem #[x, y])
    let (_, g') ← (← g.assert `hbd (← g.withContext (inferType pf)) pf).intro1P
    g := g'
  return g

theorem cmp_toNat_ofInt_fact {n : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ n) :
    ((BitVec.ofInt n z).toNat : Int) = z := by
  rw [toNat_ofInt_of_lt h0 h1]; omega

theorem cmp_toInt_ofInt_fact {n : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ n) :
    ((BitVec.ofInt n z).toInt = z ∧ 2 * z < 2 ^ n) ∨
      ((BitVec.ofInt n z).toInt = z - 2 ^ n ∧ 2 ^ n ≤ 2 * z) := by
  have e : ((BitVec.ofInt n z).toNat : Int) = z := cmp_toNat_ofInt_fact h0 h1
  have hp : ((2 ^ n : Nat) : Int) = 2 ^ n := by push_cast; rfl
  rw [BitVec.toInt_eq_toNat_cond]
  split
  · rename_i h
    have h' : 2 * ((BitVec.ofInt n z).toNat : Int) < ((2 ^ n : Nat) : Int) := by exact_mod_cast h
    left; refine ⟨e, ?_⟩; omega
  · rename_i h
    have h' : ((2 ^ n : Nat) : Int) ≤ 2 * ((BitVec.ofInt n z).toNat : Int) := by
      exact_mod_cast Nat.le_of_not_lt h
    right; refine ⟨?_, ?_⟩
    · omega
    · omega

theorem cmp_bmod_ofInt_fact {n : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ n) :
    (z.bmod (2 ^ n) = z ∧ 2 * z < 2 ^ n) ∨
      (z.bmod (2 ^ n) = z - 2 ^ n ∧ 2 ^ n ≤ 2 * z) := by
  have := cmp_toInt_ofInt_fact h0 h1
  rwa [BitVec.toInt_ofInt] at this

open Lean Meta Elab Tactic in
/-- A hypothesis of type `t`, or else a proof of it by `omega` (the range facts
of the literals, which `simp` may have rewritten). -/
def cmpFindFact (t : Expr) : TacticM (Option Expr) := do
  if let some h ← Kanon.Proof.findHyp t then return some h
  let mv ← mkFreshExprMVar t
  try
    let gs ← Tactic.run mv.mvarId! (evalTactic (← `(tactic| omega)))
    if gs.isEmpty then return some (← instantiateMVars mv) else return none
  catch _ => return none

open Lean Meta Elab Tactic in
/-- Adds the values (`toNat`, `toInt`) of the literals `BitVec.ofInt n z` of the goal and
hypotheses, from their range. -/
elab "cmpo_lit_facts" : tactic => withMainContext do
  let g ← getMainGoal
  let atoms ← cmp_collectArgs g fun e =>
    if (e.isAppOfArity ``BitVec.toNat 2 || e.isAppOfArity ``BitVec.toInt 2) &&
        e.appArg!.isAppOfArity ``BitVec.ofInt 2 then some e.appArg! else none
  let bmods ← cmp_collectArgs g fun e =>
    if e.isAppOfArity ``Int.bmod 2 then some e else none
  for a in bmods do
    let c ← mkConstWithFreshMVarLevels ``cmp_bmod_ofInt_fact
    let (mvs, _, _) ← forallMetaTelescopeReducing (← inferType c)
    unless (← isDefEq mvs[1]! (a.getArg! 0)) do continue
    let mut ok := true
    for mv in mvs[2:] do
      match ← cmpFindFact (← instantiateMVars (← inferType mv)) with
      | some h => unless ← isDefEq mv h do ok := false
      | none => ok := false
    if ok then
      let pf ← instantiateMVars (mkAppN c mvs)
      let (_, g') ← (← (← getMainGoal).assert `hlf (← inferType pf) pf).intro1P
      replaceMainGoal [g']
  for a in atoms do
    for lem in [``cmp_toNat_ofInt_fact, ``cmp_toInt_ofInt_fact] do
      let c ← mkConstWithFreshMVarLevels lem
      let (mvs, _, _) ← forallMetaTelescopeReducing (← inferType c)
      unless (← isDefEq mvs[0]! a.appFn!.appArg!) && (← isDefEq mvs[1]! a.appArg!) do continue
      let mut ok := true
      for mv in mvs[2:] do
        match ← cmpFindFact (← instantiateMVars (← inferType mv)) with
        | some h => unless ← isDefEq mv h do ok := false
        | none => ok := false
      if ok then
        let pf ← instantiateMVars (mkAppN c mvs)
        let (_, g') ← (← (← getMainGoal).assert `hlf (← inferType pf) pf).intro1P
        replaceMainGoal [g']

open Lean Meta Elab Tactic in
/-- Adds the facts on the values of the bit-vectors of the goal and hypotheses
that `omega` needs: their bounds, those of their negations, and the relation
between their signed and unsigned values (when both occur). -/
elab "cmpo_cmp_bounds" : tactic => liftMetaTactic fun g => do
  let arg (f : Name) (e : Expr) : Option Expr :=
    if e.isAppOfArity f 2 then some e.appArg! else none
  let neg (f : Name) (e : Expr) : Option Expr :=
    (arg f e).bind fun x => if x.isAppOfArity ``Neg.neg 3 then some x.appArg! else none
  let g ← cmp_addFacts g [``cmp_toInt_neg_cases] (← cmp_collectArgs g (neg ``BitVec.toInt))
  let g ← cmp_addFacts g [``cmp_toNat_neg_cases] (← cmp_collectArgs g (neg ``BitVec.toNat))
  let bin (op : Name) (e : Expr) : Option (Expr × Expr) :=
    (arg ``BitVec.toInt e <|> arg ``BitVec.toNat e).bind fun x =>
      if x.isAppOfArity op 6 then some (x.getArg! 4, x.getArg! 5) else none
  -- the sums and differences whose value is already given (by an overflow fact)
  let known ← g.withContext do
    (← getLCtx).foldlM (init := #[]) fun acc d => do
      let some (_, lhs, _) := (← instantiateMVars d.type).eq? | return acc
      return match arg ``BitVec.toInt lhs <|> arg ``BitVec.toNat lhs with
        | some x => acc.push x
        | none => acc
  let unknown (op : Name) (xys : Array (Expr × Expr)) : MetaM (Array (Expr × Expr)) :=
    g.withContext <| xys.filterM fun (x, y) => do
      let e ← mkAppM op #[x, y]
      return !(← known.anyM (isDefEq e ·))
  let g ← cmp_addFacts2 g ``cmp_toNat_add_cases
    (← unknown ``HAdd.hAdd (← cmp_collectArgs2 g (bin ``HAdd.hAdd)))
  let g ← cmp_addFacts2 g ``cmp_toNat_sub_cases
    (← unknown ``HSub.hSub (← cmp_collectArgs2 g (bin ``HSub.hSub)))
  let dedup (xs : Array Expr) : MetaM (Array Expr) := g.withContext do
    xs.foldlM (init := #[]) fun acc x => do
      if ← acc.anyM (isDefEq x ·) then return acc else return acc.push x
  let is ← dedup (← cmp_collectArgs g (arg ``BitVec.toInt))
  let ns ← dedup (← cmp_collectArgs g (arg ``BitVec.toNat))
  let g ← cmp_addFacts g [``toInt_bounds] is
  let g ← cmp_addFacts g [``cmp_toNat_bounds] ns
  return [← cmp_addFacts g [``cmp_toInt_toNat_cases] (is.filter ns.contains)]

open Lean Meta Elab Tactic in
/-- Adds the facts on the powers of two of the widths of the bit-vectors of the
context. -/
elab "cmpo_pow_facts" : tactic => liftMetaTactic fun g => g.withContext do
  let mut ws : Array Expr := #[]
  for d in (← getLCtx) do
    let ty ← whnfR (← instantiateMVars d.type)
    if ty.isAppOfArity ``BitVec 1 && !ws.contains ty.appArg! then ws := ws.push ty.appArg!
  return [← cmp_addFacts g [``cmp_two_pow_facts] ws]

open Lean Meta in
/-- Generalizes the values (`toInt`, `toNat`) of the bit-vectors of the goal
and hypotheses, and the powers of two, so that `omega` treats them as atoms. -/
partial def cmp_genValues (g : MVarId) : MetaM MVarId := g.withContext do
  let isVal (e : Expr) : Bool := !e.hasLooseBVars &&
    (e.isAppOfArity ``BitVec.toInt 2 || e.isAppOfArity ``BitVec.toNat 2 ||
      (e.isAppOfArity ``HPow.hPow 6 && (e.getArg! 5).nat?.isNone))
  let mut cand : Option Expr := (← instantiateMVars (← g.getType)).find? isVal
  for d in (← getLCtx) do
    if cand.isNone && !d.isImplementationDetail then
      cand := (← instantiateMVars d.type).find? isVal
  let some v := cand | return g
  -- the occurrences are found up to instances, so all the facts are generalized
  let hyps ← (← getLCtx).foldlM (init := #[]) fun acc d => do
    if d.isImplementationDetail then return acc
    if ← isProp d.type then return acc.push d.fvarId
    return acc
  let (_, _, g) ← g.generalizeHyp #[{ expr := v, xName? := `v }] hyps
  cmp_genValues g

open Lean Meta Elab Tactic in
elab "cmpo_gen_values" : tactic => liftMetaTactic fun g => return [← cmp_genValues g]

open Lean Meta in
/-- The products `p * q` of integers (or natural numbers) of the goal and
hypotheses. -/
def cmp_collectProducts (g : MVarId) (int : Bool) : MetaM (Array (Expr × Expr)) :=
  cmp_collectArgs2 g fun e =>
    if e.isAppOfArity ``HMul.hMul 6 && (e.getArg! 0).isConstOf (if int then ``Int else ``Nat) &&
        (e.getArg! 4).int?.isNone && (e.getArg! 5).int?.isNone &&
        (e.getArg! 4).nat?.isNone && (e.getArg! 5).nat?.isNone then
      some (e.getArg! 4, e.getArg! 5)
    else none

open Lean Meta Elab Tactic in
/-- Adds the facts on the products and quotients of the goal and hypotheses
that `omega` needs: cancelling a common factor of two products, and the
quotients by a divisor that also multiplies. -/
elab "cmpo_mul_facts" : tactic => liftMetaTactic fun g => do
  let mut g := g
  -- cancelling a factor common to two products (in any position: with the
  -- commutativity of the products whose factors are swapped)
  for (int, lem, comm) in [(true, ``cmp_mul_cmp_facts, ``Int.mul_comm),
      (false, ``cmp_nat_mul_cmp_facts, ``Nat.mul_comm)] do
    let ps ← cmp_collectProducts g int
    for i in [0:ps.size] do
      for j in [i+1:ps.size] do
        let (a, b) := ps[i]!
        let (c, d) := ps[j]!
        let cands : List (Bool × Expr × Expr × Expr × List (Expr × Expr)) :=
          [(a == c, a, b, d, []), (b == d, b, a, c, [(a, b), (c, d)]),
           (a == d, a, b, c, [(c, d)]), (b == c, b, a, d, [(a, b)])]
        for (common, p, q, r, swaps) in cands do
          unless common && q != r do continue
          for (x, y) in swaps do
            let pf ← g.withContext (mkAppM comm #[x, y])
            let (_, g') ← (← g.assert `hcomm (← g.withContext (inferType pf)) pf).intro1P
            g := g'
          let pf ← g.withContext (mkAppM lem #[p, q, r])
          let (_, g') ← (← g.assert `hmul (← g.withContext (inferType pf)) pf).intro1P
          g := g'
  let divs (f : Name) := cmp_collectArgs2 g fun e =>
    if e.isAppOfArity f 3 then some (e.getArg! 1, e.getArg! 2) else none
  let sdivs ← divs ``BitVec.smtSDiv
  let udivs ← divs ``BitVec.smtUDiv
  g ← cmp_addFacts2 g ``cmp_toInt_smtSDiv_facts sdivs
  g ← cmp_addFacts2 g ``cmp_toNat_smtUDiv_facts udivs
  for (int, ds, val, lem, comm) in [(true, sdivs, ``BitVec.toInt, ``cmp_tdiv_facts, ``Int.mul_comm),
      (false, udivs, ``BitVec.toNat, ``cmp_div_facts, ``Nat.mul_comm)] do
    let ps ← cmp_collectProducts g int
    for (a, b) in ds do
      let (c2, c1) ← g.withContext do return (← mkAppM val #[a], ← mkAppM val #[b])
      let mut done : Array Expr := #[]
      for (x, q) in ps do
        -- the product `x * c1`, or `c1 * x` with its commutativity
        let (x, swapped) ←
          if ← g.withContext (isDefEq q c1) then pure (x, false)
          else if ← g.withContext (isDefEq x c1) then pure (q, true)
          else continue
        if done.contains x then continue
        done := done.push x
        if swapped then
          let pf ← g.withContext (mkAppM comm #[c1, x])
          let (_, g') ← (← g.assert `hcomm (← g.withContext (inferType pf)) pf).intro1P
          g := g'
        let pf ← g.withContext (mkAppM lem #[c2, c1, x])
        let (_, g') ← (← g.assert `hdiv (← g.withContext (inferType pf)) pf).intro1P
        g := g'
  return [g]

open Lean Meta Elab Tactic in
/-- Clears the facts that only hold under an unknown checked flag
(`c.signed = true → _`), which `omega` cannot use. -/
elab "cmpo_clear_flags" : tactic => liftMetaTactic fun g => g.withContext do
  let mut g := g
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let .forallE _ dom _ _ := ty then
      if let some (_, lhs, _) := dom.eq? then
        if lhs.isAppOfArity ``CoreMod.Checked.signed 1 ||
            lhs.isAppOfArity ``CoreMod.Checked.unsigned 1 then
          g ← g.clear d.fvarId
  return [g]

open Lean Meta Elab Tactic in
elab "cmpo_ovf_eqs" : tactic => liftMetaTactic fun g => return [← ovfEqs g]

theorem tmod_cast_fact {A B : Nat} {X Y : Int} (hx : (A : Int) = X) (hy : (B : Int) = Y) :
    X.tmod Y = ((A % B : Nat) : Int) := by
  subst hx hy; rfl

open Lean Meta Elab Tactic in
/-- For the hypotheses `X.tmod Y = _` on integers that are the values `↑A`, `↑B` of
naturals (`↑A = X`), adds `X.tmod Y = ↑(A % B)`. -/
elab "cmpo_tmod_facts" : tactic => withMainContext do
  let tms ← cmp_collectArgs2 (← getMainGoal) fun sub =>
    if sub.isAppOfArity ``Int.tmod 2 then some (sub.getArg! 0, sub.getArg! 1) else none
  let natOf (X : Expr) : MetaM (Option Expr) := do
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let some (_, l, r) := (← instantiateMVars d.type).eq? | continue
      if r == X && l.isAppOfArity ``Nat.cast 3 then return some d.toExpr
    return none
  for (X, Y) in tms do
    let some hx ← natOf X | continue
    let some hy ← natOf Y | continue
    let pf ← mkAppM ``BitvecMod.Cmp.tmod_cast_fact #[hx, hy]
    let (_, g) ← (← getMainGoal).note `htm pf
    replaceMainGoal [g]

theorem cmp_nat_mul_zero (x y : Nat) : (x = 0 → x * y = 0) ∧ (y = 0 → x * y = 0) :=
  ⟨fun h => by simp [h], fun h => by simp [h]⟩

/-- The factors of the products of naturals in `e`, outside binders' scope. -/
partial def cmpMulNats (e : Lean.Expr) (acc : Array (Lean.Expr × Lean.Expr) := #[]) :
    Array (Lean.Expr × Lean.Expr) :=
  let acc :=
    if e.isAppOfArity ``HMul.hMul 6 && e.getArg! 0 == .const ``Nat [] &&
        !e.hasLooseBVars && !acc.contains (e.getArg! 4, e.getArg! 5) then
      acc.push (e.getArg! 4, e.getArg! 5)
    else acc
  match e with
  | .app f a => cmpMulNats a (cmpMulNats f acc)
  | .lam _ t b _ | .forallE _ t b _ => cmpMulNats b (cmpMulNats t acc)
  | .mdata _ b => cmpMulNats b acc
  | _ => acc

open Lean Meta Elab Tactic in
/-- Adds that the products of naturals in the hypotheses are zero when a factor
is: `omega` treats a product as an atom. -/
elab "cmpo_mul_zero" : tactic => withMainContext do
  let mut ps : Array (Expr × Expr) := #[]
  for d in (← getLCtx) do
    unless d.isImplementationDetail do ps := cmpMulNats (← instantiateMVars d.type) ps
  for (a, b) in ps do
    let pf ← mkAppM ``BitvecMod.Cmp.cmp_nat_mul_zero #[a, b]
    let (_, g) ← (← getMainGoal).note `hmz pf
    replaceMainGoal [g]

/-- The conjuncts of a conjunction. -/
partial def cmpConjs (e : Lean.Expr) : List Lean.Expr :=
  if e.isAppOfArity ``And 2 then cmpConjs e.appFn!.appArg! ++ cmpConjs e.appArg! else [e]

open Lean Meta Elab Tactic in
/-- Clears the disjunctions equal to an earlier hypothesis up to the order of
their conjuncts: the facts of a literal can come twice, and each disjunction
doubles the case splits of `omega`. -/
elab "cmpo_dedup_or" : tactic => withMainContext do
  let key (e : Expr) : MetaM (List String) := do
    let l ← (cmpConjs e).mapM fun c => do pure (toString (← ppExpr c))
    pure (l.mergeSort (· ≤ ·))
  let mut seen : Std.HashSet String := {}
  let mut dups : Array FVarId := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``Or 2 then
      let k := toString (← key t.appFn!.appArg!) ++ "|" ++ toString (← key t.appArg!)
      if seen.contains k then dups := dups.push d.fvarId else seen := seen.insert k
  replaceMainGoal [← (← getMainGoal).tryClearMany dups]

end BitvecMod.Cmp

namespace BitvecMod
open BitvecMod.Cmp

set_option hygiene false in
/-- Reduces the goals to facts on the integer values of the atoms. -/
macro "cmpo_pre" : tactic => `(tactic| (
  cmp_dedupe
  (try simp (disch := first | assumption | omega) only [BitvecMod.negOp_some,
    BitvecMod.Cmp.cmp_eq_intMin_iff] at *)
  (try simp only [BitvecMod.divisible, BitvecMod.Prim.divisible, BitvecMod.tdiv,
    BitvecMod.Prim.tdiv, BitvecMod.trem, BitvecMod.Prim.trem, decide_eq_true_eq] at *)
  all_goals (try simp_all [BitVec.slt_eq_decide, BitVec.ult_eq_decide, BitVec.sle_eq_decide,
    BitVec.ule_eq_decide, ← BitVec.toNat_inj, BitvecMod.Cmp.toNat_setWidth_add,
    BitvecMod.Cmp.cmp_binB_ite_l,
    BitvecMod.Cmp.cmp_binB_ite_r,
    -BitVec.ofInt_natCast, -BitVec.toInt_ofInt, -BitVec.toNat_ofInt, -BitVec.toNat_neg,
    -BitVec.toNat_add,
    -BitVec.toNat_sub, -BitVec.toNat_mul, -BitVec.toInt_add, -BitVec.toInt_sub, -BitVec.toInt_mul,
    -BitVec.toNat_udiv, -BitVec.toNat_umod, -BitVec.toInt_srem, -BitVec.toNat_intMin,
    -BitVec.toNat_setWidth])
  all_goals (try simp only [Int.natCast_dvd_natCast, Nat.dvd_iff_mod_eq_zero] at *)
  all_goals (try simp only [Int.dvd_iff_tmod_eq_zero] at *)
  all_goals (try simp (disch := first | assumption | omega) only [BitVec.toNat_intMin_of_pos,
    BitVec.toInt_intMin_of_pos] at *)
  all_goals kanon_split
  all_goals cmpo_ovf_eqs
  all_goals (try simp only [BitvecMod.sadd_ok, BitvecMod.ssub_ok, BitvecMod.smul_ok,
    BitvecMod.uadd_ok, BitvecMod.usub_ok, BitvecMod.umul_ok] at *)
  all_goals (try simp only [BitVec.saddOverflow, BitVec.ssubOverflow, BitVec.smulOverflow,
    BitVec.uaddOverflow, BitVec.usubOverflow, BitVec.umulOverflow, decide_eq_true_eq,
    Bool.or_eq_true] at *)
  all_goals kanon_split
  all_goals cmpo_clear_flags
  all_goals cmpo_mul_facts
  all_goals cmpo_lit_facts
  all_goals cmpo_cmp_bounds
  all_goals cmpo_lit_facts
  all_goals (try cmpo_tmod_facts)
  all_goals (try push_cast at *)))

/-- Closes a goal by reasoning on the integer values of the atoms. -/
macro "cmpo_omega" : tactic => `(tactic| (
  cmpo_pre
  all_goals cmpo_pow_facts
  all_goals cmpo_gen_values
  all_goals (try simp only [Int.natCast_inj] at *)
  all_goals (try subst_vars)
  all_goals cmpo_dedup_or
  all_goals omega))

end BitvecMod

/-! ## The operations on literals, at a width given by an equation -/

namespace BitvecMod.Cmp

open Prim

section
variable {n : Nat} {w : Int} (h : w = n)
include h

theorem lit_emod (z : Int) {k : Nat} (hk : k = n) : BitVec.ofInt n (z % 2 ^ k) = BitVec.ofInt n z := by
  subst hk; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]
theorem lit_add' (a b : Int) : BitVec.ofInt n (Prim.lit_add w a b) = BitVec.ofInt n a + BitVec.ofInt n b := by
  subst h; exact LitOps.ofInt_lit_add a b
theorem lit_sub' (a b : Int) : BitVec.ofInt n (Prim.lit_sub w a b) = BitVec.ofInt n a - BitVec.ofInt n b := by
  subst h; exact LitOps.ofInt_lit_sub a b
theorem lit_mul' (a b : Int) : BitVec.ofInt n (Prim.lit_mul w a b) = BitVec.ofInt n a * BitVec.ofInt n b := by
  subst h; exact LitOps.ofInt_lit_mul a b
theorem lit_neg' (a : Int) : BitVec.ofInt n (Prim.lit_neg w a) = -BitVec.ofInt n a := by
  subst h; exact LitOps.ofInt_lit_neg a
theorem lit_not' (a : Int) : BitVec.ofInt n (Prim.lit_not w a) = ~~~BitVec.ofInt n a := by
  subst h; exact LitOps.ofInt_lit_not a
theorem lit_and' {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    BitVec.ofInt n (Prim.lit_and w a b) = BitVec.ofInt n a &&& BitVec.ofInt n b := by
  subst h; exact LitOps.ofInt_lit_and ha hb
theorem lit_or' {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    BitVec.ofInt n (Prim.lit_or w a b) = BitVec.ofInt n a ||| BitVec.ofInt n b := by
  subst h; exact LitOps.ofInt_lit_or ha hb
theorem lit_xor' {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    BitVec.ofInt n (Prim.lit_xor w a b) = BitVec.ofInt n a ^^^ BitVec.ofInt n b := by
  subst h; exact LitOps.ofInt_lit_xor ha hb
end

theorem lit_not_toNat {n : Nat} (m : Int) :
    Prim.lit_not (n : Int) m = ((~~~BitVec.ofInt n m).toNat : Int) := by
  rw [← LitOps.ofInt_lit_not, Prim.lit_not, LitOps.masked_eq_toNat, LitOps.ofInt_masked_toNat]

theorem zland_natCast (p q : Nat) : Prim.z_land (p : Int) (q : Int) = ((p &&& q : Nat) : Int) := rfl

theorem and_mask_ne {n : Nat} {a m : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n)
    (h : ¬Prim.z_land a (Prim.lit_not (n : Int) m) = 0) (x : BitVec n) :
    ¬BitVec.ofInt n a = BitVec.ofInt n m &&& x := by
  intro e
  apply h
  have ha : a = ((BitVec.ofInt n a).toNat : Int) := by
    rw [toNat_ofInt_of_lt ha0 ha1]; omega
  rw [lit_not_toNat, ha, zland_natCast, ← BitVec.toNat_and, e]
  have : (BitVec.ofInt n m &&& x) &&& ~~~BitVec.ofInt n m = 0#n := by
    ext i hi; simp; intro h _; exact h
  rw [this]; simp

theorem nat_and_mask_eq_zero_iff {z N K : Nat} (hz : z < 2^(N+K)) :
    z &&& ((2^K - 1) * 2^N) = 0 ↔ z < 2^N := by
  rw [← Nat.shiftLeft_eq]
  constructor
  · intro h
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    cases hb : z.testBit i
    · rfl
    have hik : i < N + K := by
      have := Nat.ge_two_pow_of_testBit hb
      refine Nat.lt_of_not_le fun hc => ?_
      have : 2^(N+K) ≤ 2^i := Nat.pow_le_pow_right (by omega) hc
      omega
    have := congrArg (fun x => x.testBit i) h
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit, hb,
      Nat.testBit_two_pow_sub_one] at this
    simp at this
    omega
  · intro h
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit]
    by_cases hi : i < N
    · simp; omega
    · have : z.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [this]

theorem zland_mask_iff {z : Int} {n k : Nat} (h0 : 0 ≤ z) (h1 : z < 2 ^ (n + k)) :
    z_land z (z_lsl (2 ^ k - 1) (n : Int)) = 0 ↔ z < 2 ^ n := by
  obtain ⟨Z, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  have hm : z_lsl (2 ^ k - 1) (n : Int) = (((2 ^ k - 1) * 2 ^ n : Nat) : Int) := by
    have := Nat.one_le_two_pow (n := k)
    simp only [Prim.z_lsl, Int.toNat_natCast]
    rw [Int.natCast_mul, Int.natCast_sub this]
    simp
  rw [hm]
  show Int.ofNat (Z &&& _) = 0 ↔ _
  have h1' : Z < 2 ^ (n + k) := by exact_mod_cast h1
  rw [Int.ofNat_eq_natCast, Int.natCast_eq_zero, nat_and_mask_eq_zero_iff h1']
  constructor <;> intro h <;> exact_mod_cast h

theorem toNat_setWidth_add {n k : Nat} (w : BitVec n) : (w.setWidth (n + k)).toNat = w.toNat :=
  BitVec.toNat_setWidth_of_le (by omega)

theorem udiv_big {w : Nat} {n d : Int} (hn0 : 0 ≤ n) (hn1 : n < 2 ^ w) (hd0 : 0 ≤ d)
    (hd1 : d < 2 ^ w) (h : 2 ^ w - 1 < n * d ∨ n * d < 0) (x : BitVec w) :
    (x.smtUDiv (BitVec.ofInt w d)).toNat ≤ (BitVec.ofInt w n).toNat := by
  have hmul : 0 ≤ n * d := Int.mul_nonneg hn0 hd0
  have h' : 2 ^ w ≤ n * d := by omega
  have hu : (BitVec.ofInt w n).umulOverflow (BitVec.ofInt w d) = true := by
    simp only [BitVec.umulOverflow, ge_iff_le, decide_eq_true_eq]
    rw [toNat_ofInt_of_lt hn0 hn1, toNat_ofInt_of_lt hd0 hd1]
    have e : ((n.toNat * d.toNat : Nat) : Int) = n * d := by
      push_cast; rw [Int.toNat_of_nonneg hn0, Int.toNat_of_nonneg hd0]
    have e2 : ((2 ^ w : Nat) : Int) = 2 ^ w := by push_cast; rfl
    omega
  have := cmp_smtUDiv_ule_of_umulOverflow (x := x) hu
  simpa [BitVec.ule] using this

theorem mul_cancel_nat {M a b d : Nat} (hM : Nat.Coprime M a) (hb : b < M) (hd : d < M)
    (h : a * b % M = a * d % M) : b = d := by
  rcases Nat.le_total b d with hbd | hbd
  · have h1 := Nat.sub_mod_eq_zero_of_mod_eq h.symm
    rw [← Nat.mul_sub] at h1
    have h2 := hM.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero h1)
    have := Nat.eq_zero_of_dvd_of_lt h2 (by omega)
    omega
  · have h1 := Nat.sub_mod_eq_zero_of_mod_eq h
    rw [← Nat.mul_sub] at h1
    have h2 := hM.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero h1)
    have := Nat.eq_zero_of_dvd_of_lt h2 (by omega)
    omega

theorem mul_cancel_odd {w : Nat} {k a b : BitVec w} (h : k.toNat % 2 = 1) :
    k * a = k * b ↔ a = b := by
  refine ⟨fun e => BitVec.eq_of_toNat_eq ?_, fun e => by rw [e]⟩
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_mul] at this
  refine mul_cancel_nat ?_ a.isLt b.isLt this
  apply Nat.Coprime.pow_left
  show Nat.gcd 2 k.toNat = 1
  rw [Nat.gcd_rec, h]; rfl

theorem mul_cancel_odd' {w : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ w)
    (h : z_land z 1 = 1) {a b : BitVec w} : BitVec.ofInt w z * a = BitVec.ofInt w z * b ↔ a = b := by
  apply mul_cancel_odd
  obtain ⟨Z, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  rw [toNat_ofInt_of_lt h0 h1, Int.toNat_natCast]
  have : z_land (Z : Int) 1 = ((Z % 2 : Nat) : Int) := by
    show Int.ofNat (Z &&& 1) = _
    rw [Nat.and_one_is_mod]; rfl
  rw [this] at h; omega

theorem mul_cancel_ovf {w : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ w) (hz : z ≠ 0)
    {a b : BitVec w}
    (h : (BitVec.ofInt w z).smulOverflow a = false ∧ (BitVec.ofInt w z).smulOverflow b = false ∨
      (BitVec.ofInt w z).umulOverflow a = false ∧ (BitVec.ofInt w z).umulOverflow b = false) :
    BitVec.ofInt w z * a = BitVec.ofInt w z * b ↔ a = b := by
  have hk : BitVec.ofInt w z ≠ 0#w := by
    intro e; have := congrArg BitVec.toNat e
    rw [toNat_ofInt_of_lt h0 h1] at this; simp at this; omega
  refine ⟨fun e => ?_, fun e => by rw [e]⟩
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · apply BitVec.eq_of_toInt_eq
    have := congrArg BitVec.toInt e
    rw [toInt_mul_ok ha, toInt_mul_ok hb] at this
    have : (BitVec.ofInt w z).toInt ≠ 0 := by
      intro h0; apply hk; exact BitVec.eq_of_toInt_eq (by simp [h0])
    exact Int.eq_of_mul_eq_mul_left this ‹_›
  · apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat e
    rw [toNat_mul_ok ha, toNat_mul_ok hb] at this
    exact Nat.eq_of_mul_eq_mul_left (BitVec.toNat_pos_of_ne_zero hk) this

end BitvecMod.Cmp

/-! ## The bound of the values of a term by `msb_of` -/

namespace BitvecMod

open Classical Kanon

section
variable {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [Lang S] [KanonBool.Typed S] [Typed S]

/-- The value of a literal of a sort of bit-vectors of positive width. -/
theorem lit_val {ρ : S.Env} {k : Int} {t : S.Ty} {n : Nat} (w : S.WT (mk (.BitVec k) t))
    (ht : t = sort (.TBitVector n)) (hn : (0 : Int) < n) :
    0 ≤ k ∧ k < 2 ^ n ∧ S.ev ρ (mk (.BitVec k) t) = some (bv n (BitVec.ofInt n k)) := by
  subst ht
  rw [WT_mk] at w
  simp only [Node.wt, bv_wf] at w
  obtain ⟨⟨-, hz⟩, -⟩ := w
  obtain ⟨h0, h1⟩ := hz n (by simp)
  refine ⟨h0, by simpa using h1, ?_⟩
  rw [ev_mk]
  simp only [Node.map, Node.eval, ofBV_some]
  rw [width_eq ρ rfl (.inl rfl) hn, Int.toNat_natCast]

/-- A literal that is not zero is in the subsort `Nonzero`. -/
theorem nonzero_lit {z : Int} {t : S.Ty} (w : S.WT (mk (.BitVec z) t)) (hz : z ≠ 0) :
    Nonzero (mk (.BitVec z) t) := by
  intro ρ n x e
  have w' := w
  rw [WT_mk] at w'
  obtain ⟨⟨⟨k, hk, rfl⟩, -⟩, -⟩ := w'
  obtain ⟨k', rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hk)
  obtain ⟨h0, h1, hv⟩ := lit_val (ρ := ρ) w rfl hk
  rw [hv] at e
  simp only [Option.some.injEq, bv, Embed.inj_eq_iff] at e
  cases e
  intro hx
  have := congrArg BitVec.toNat hx
  rw [BitvecMod.toNat_ofInt_of_lt h0 h1] at this
  simp at this; omega

theorem msb_fact (ρ : S.Env) {v : S.Term} {n : Nat} (w : S.WT v)
    (ht : S.ty v = sort (.TBitVector n)) :
    ∀ x : BitVec n, S.ev ρ v = some (bv n x) → (x.toNat : Int) < 2 ^ (Bitvec.msb_of v + 1).toNat :=
  fun x e => msb_bound ρ _ v (Nat.lt_succ_self _) n x w ht e

end

end BitvecMod

namespace BitvecMod

set_option hygiene false in
/-- Normalizes the values of the hypotheses and the goal: the comparisons as
integer facts, the values of the operations on known values, the hypotheses
split. -/
macro "cmp_norm" : tactic => `(tactic| (
  all_goals (try cmp_bool_vars)
  all_goals (try simp only [BitVec.slt, BitVec.sle, BitVec.ult, BitVec.ule, Bool.true_eq_false,
    Bool.false_eq_true, ite_true, ite_false] at *)
  all_goals (try simp only [BitvecMod.Srt.val, KanonBool.Srt.val, BitvecMod.asBV_bv,
    BitvecMod.asBV_eq_some, BitvecMod.asB_vbool, BitvecMod.asB_eq_some, BitvecMod.withW_bv,
    BitvecMod.ofBV_some, BitvecMod.ofB_some, BitvecMod.ckOp_some, BitvecMod.binOp_some,
    BitvecMod.negOp_some, BitvecMod.binB_some, BitvecMod.asBV_ofBV, BitvecMod.asBV_none,
    BitvecMod.asB_none, BitvecMod.withW_none, BitvecMod.ofBV_none, BitvecMod.ofB_none,
    BitvecMod.ckOp_none_l, BitvecMod.ckOp_none_r, BitvecMod.binOp_none_l, BitvecMod.binOp_none_r,
    BitvecMod.negOp_none, BitvecMod.binB_none_l, BitvecMod.binB_none_r, KanonBool.pand_eq_some,
    KanonBool.por_eq_some, KanonBool.pnot_eq_some, KanonBool.peq_eq_some, KanonBool.pite_eq_some,
    BitvecMod.cmp_pite_none,
    Kanon.Embed.inj_eq_iff, Kanon.Embed.proj_inj, Option.bind_eq_bind, Option.bind_some,
    Option.bind_none, Option.map_some, Option.map_none, BitvecMod.cmp_ofBV_ite,
    BitvecMod.cmp_asBV_ite, BitvecMod.cmp_asB_ite, BitvecMod.cmp_ofB_ite, BitvecMod.cmp_withW_ite,
    BitvecMod.cmp_binB_ite_l, BitvecMod.cmp_binB_ite_r, BitvecMod.cmp_binOp_ite_l,
    BitvecMod.cmp_binOp_ite_r, BitvecMod.cmp_map_ite, Option.some.injEq, reduceCtorEq, false_and, and_false,
    ite_true, ite_false, Bool.not_true, Bool.not_false, Option.ite_none_left_eq_some,
    Option.ite_none_right_eq_some] at *)
  all_goals (try simp only [exists_eq_left, exists_eq_left', exists_eq_right, exists_eq_right',
    Kanon.Embed.inj_eq_iff, Sigma.mk.injEq, heq_eq_eq, true_and, and_true, decide_eq_decide,
    exists_and_left, exists_and_right, Int.toNat_natCast, forall_eq, forall_eq',
    Bool.decide_eq_true, Bool.decide_eq_false, decide_eq_true_eq, decide_eq_false_iff_not] at *)
  all_goals (try simp (disch := first | assumption | omega) only [BitvecMod.signed_extract_zero,
    BitvecMod.z_lsl_one, natCast_sub_one_toNat, BitvecMod.Bitvec.unsigned_ub,
    BitvecMod.Cmp.zland_mask_iff] at *)
  all_goals (try simp (disch := first | assumption | omega) only [BitvecMod.cmp_ofInt_two_pow_pred,
    BitVec.toNat_intMin_of_pos, BitVec.toInt_intMin_of_pos] at *)
  all_goals (try simp only [BitvecMod.lit_add, BitvecMod.lit_sub, BitvecMod.lit_mul,
    BitvecMod.lit_neg, BitvecMod.lit_not, BitvecMod.lit_and, BitvecMod.lit_or, BitvecMod.lit_xor,
    BitvecMod.size_of_ty_TBitVector, BitvecMod.size_of_ty_TLoc] at *)
  all_goals (try simp (disch := first | rfl | assumption | omega) only [BitvecMod.Cmp.lit_emod,
    BitvecMod.Cmp.lit_add', BitvecMod.Cmp.lit_sub', BitvecMod.Cmp.lit_mul', BitvecMod.Cmp.lit_neg',
    BitvecMod.Cmp.lit_not', BitvecMod.Cmp.lit_and', BitvecMod.Cmp.lit_or',
    BitvecMod.Cmp.lit_xor'] at *)
  all_goals (try (cmp_split_all <;> subst_vars))
  all_goals (try simp only [Option.some.injEq, Kanon.Embed.inj_eq_iff] at *)
  cmp_widths))

set_option hygiene false in
/-- The value half, reduced to the values of the atoms (without the closers of `cmp_sem`). -/
macro "cmp_sem_pre" : tactic => `(tactic| (
  cmp_sem_core
  cmp_norm
  cmp_norm
  all_goals (try simp only [Kanon.Embed.inj_eq_iff, Bool.true_eq_false, Bool.false_eq_true,
    true_and, false_and, and_false, and_true, or_false, false_or, decide_eq_true_eq,
    decide_eq_false_iff_not, Bool.decide_eq_true, Bool.decide_eq_false, BitvecMod.cmp_true_eq, BitvecMod.cmp_false_eq, BitvecMod.cmp_append_inj] at *)
  all_goals (try cmp_norm_bv_types)
  all_goals (try cmp_clear_arith_eqs)))

set_option hygiene false in
macro "cmp_sem" : tactic => `(tactic| (
  cmp_sem_pre
  all_goals first
    | kanon_close
    | (cmpo_omega; done)
    | (exact BitvecMod.Cmp.udiv_big (by assumption) (by assumption) (by assumption)
        (by assumption) (by omega) _)
    | ((repeat' split at e) <;> (repeat' split) <;> first | kanon_close | (cmpo_omega; done))
    | skip))

set_option hygiene false in
/-- `cmp_sem`, trying `cmpo_omega` before `kanon_close`: for the comparisons of orders, whose
value goals `omega` mostly closes (`kanon_close` tries `grind` before failing). -/
macro "cmp_sem_ord" : tactic => `(tactic| (
  cmp_sem_pre
  all_goals first
    | (cmpo_omega; done)
    | kanon_close
    | (exact BitvecMod.Cmp.udiv_big (by assumption) (by assumption) (by assumption)
        (by assumption) (by omega) _)
    | ((repeat' split at e) <;> (repeat' split) <;> first | (cmpo_omega; done) | kanon_close)
    | skip))

/-- The typing half. -/
macro "cmp_wt" : tactic => `(tactic| (
  intro w
  cmp_facts
  (try simp_all)
  all_goals (try (refine ⟨?_, ?_⟩))
  all_goals first | done | omega | exact Int.pow_pos (by decide) | skip))

/-- Proves an arm, as far as it can. -/
macro "cmp_rule" : tactic => `(tactic| (
  kanon_rule_lift
  all_goals (try bv_vacuous)
  all_goals (try simp only [BitvecMod.proj_mk, KanonBool.proj_mk, Kanon.firstSome_some,
    Kanon.firstSome_none, Kanon.firstSome_nil', Option.getD_some, Option.getD_none,
    BitvecMod.proj_Bool_mk_Bitvec, BitvecMod.proj_Bitvec_mk_Bool, reduceCtorEq] at *)
  all_goals (try dsimp only)
  all_goals (try delta BitvecMod.Bitvec.size)
  all_goals (try (repeat' split))
  all_goals (try cmp_split_ifs)
  all_goals (try contradiction)
  all_goals (try (exact absurd trivial ‹¬True›))
  all_goals (try kanon_lift_body)
  all_goals (try simp only [kanon_spec, kanon_body])
  all_goals (try (cmp_nonzero; done))
  all_goals kanon_on_refines (
    refine Kanon.Sem.Refines.intro ?_ ?_
    · cmp_wt
    · cmp_sem)))

set_option hygiene false in
/-- The value half of a sign test (`v <s 0`), on the sign bit of `v`. -/
macro "cmp_msb_sem" : tactic => `(tactic| (
  cmp_sem_core
  all_goals (try simp only [BitvecMod.cmp_slt_zero] at *)
  cmp_norm
  all_goals (try simp only [BitvecMod.cmp_toInt_lt_zero] at *)
  cmp_norm
  all_goals (try simp only [BitvecMod.cmp_toInt_lt_zero] at *)
  all_goals (try simp only [Kanon.Embed.inj_eq_iff, Bool.true_eq_false, Bool.false_eq_true,
    true_and, false_and, and_false, and_true, or_false, false_or, decide_eq_true_eq,
    decide_eq_false_iff_not, Bool.decide_eq_true, Bool.decide_eq_false, BitvecMod.cmp_true_eq,
    BitvecMod.cmp_false_eq] at *)
  all_goals (try cmp_norm_bv_types)
  all_goals first
    | kanon_close
    | (simp_all [BitVec.msb_signExtend, BitVec.msb_not, BitVec.msb_append, BitVec.msb_setWidth,
        BitVec.msb_srem]; done)
    | (simp_all [BitVec.msb_signExtend, BitVec.msb_not, BitVec.msb_append, BitVec.msb_setWidth,
        BitVec.msb_srem, BitVec.msb_eq_decide]; omega)
    | (cmpo_omega; done)
    | (simp only [BitVec.msb_srem, ofInt_zero'] at *; grind)
    | skip))

/-- Proves an arm of a sign test, as far as it can. -/
macro "cmp_msb_rule" : tactic => `(tactic| (
  kanon_rule_lift
  all_goals (try bv_vacuous)
  all_goals (try simp only [BitvecMod.proj_mk, KanonBool.proj_mk, Kanon.firstSome_some,
    Kanon.firstSome_none, Kanon.firstSome_nil', Option.getD_some, Option.getD_none,
    BitvecMod.proj_Bool_mk_Bitvec, BitvecMod.proj_Bitvec_mk_Bool, reduceCtorEq] at *)
  all_goals (try dsimp only)
  all_goals (try delta BitvecMod.Bitvec.size)
  all_goals (try (repeat' split))
  all_goals (try cmp_split_ifs)
  all_goals (try contradiction)
  all_goals (try (exact absurd trivial ‹¬True›))
  all_goals (try kanon_lift_body)
  all_goals (try simp only [kanon_spec, kanon_body])
  all_goals (try (cmp_nonzero; done))
  all_goals kanon_on_refines (
    refine Kanon.Sem.Refines.intro ?_ ?_
    · cmp_wt
    · cmp_msb_sem)))

end BitvecMod

namespace BitvecMod

/-- The tactic of the comparisons: `cmp_rule`, or on the sign bits (`cmp_msb_rule`). -/
macro "cmp_auto" : tactic => `(tactic| first | (cmp_rule; done) | (cmp_msb_rule; done))

end BitvecMod

namespace BitvecMod

/-- The lifting of an arm, its guards reduced and its conditionals split. -/
macro "cmp_lift" : tactic => `(tactic| (
  kanon_rule_lift
  all_goals (try bv_vacuous)
  all_goals (try simp only [BitvecMod.proj_mk, KanonBool.proj_mk, Kanon.firstSome_some,
    Kanon.firstSome_none, Kanon.firstSome_nil', Option.getD_some, Option.getD_none,
    BitvecMod.proj_Bool_mk_Bitvec, BitvecMod.proj_Bitvec_mk_Bool, reduceCtorEq] at *)
  all_goals (try dsimp only)
  all_goals (try delta BitvecMod.Bitvec.size)
  all_goals (try (repeat' split))
  all_goals (try cmp_split_ifs)
  all_goals (try contradiction)
  all_goals (try (exact absurd trivial ‹¬True›))
  all_goals (try kanon_lift_body)
  all_goals (try simp only [kanon_spec, kanon_body])
  all_goals (try (cmp_nonzero; done))))

/-- `cmp_rule`, with `cmp_sem_ord` (for `lt` and `leq`). -/
macro "cmp_rule_ord" : tactic => `(tactic| (
  cmp_lift
  all_goals kanon_on_refines (
    refine Kanon.Sem.Refines.intro ?_ ?_
    · cmp_wt
    · cmp_sem_ord)))

/-- The typing and value halves of the refinements, as far as `cmp_sem` goes. -/
macro "cmp_halves" : tactic => `(tactic|
  all_goals kanon_on_refines (
    refine Kanon.Sem.Refines.intro (by cmp_wt) ?_
    cmp_sem))

/-- `zmin` is `min` (for `omega`, without splitting). -/
theorem cmp_zmin_eq_min (a b : Int) : Bitvec.zmin a b = min a b := by
  unfold Bitvec.zmin; split <;> rename_i h <;> simp at h <;> omega

/-- `zmax` is `max` (for `omega`, without splitting). -/
theorem cmp_zmax_eq_max (a b : Int) : Bitvec.zmax a b = max a b := by
  unfold Bitvec.zmax; split <;> rename_i h <;> simp at h <;> omega

end BitvecMod

namespace BitvecMod.Cmp

/-- The arithmetic of `lt`/`leq.r_add_add` (signed): moving the constant `L - R` of
the left sum to the right one neither overflows nor changes the comparison. -/
theorem add_add_s_core {w : Nat} {L R a b : BitVec w}
    (hl : L.saddOverflow a = false) (hr : R.saddOverflow b = false)
    (h1 : min 0 L.toInt ≤ L.toInt - R.toInt) (h2 : L.toInt - R.toInt ≤ max 0 L.toInt) :
    a.saddOverflow (L - R) = false ∧
      (a + (L - R)).toInt + (R + b).toInt = (L + a).toInt + b.toInt := by
  have bL := toInt_bounds L
  have bR := toInt_bounds R
  have ba := toInt_bounds a
  have hl' := sadd_ok.1 hl
  have hr' := sadd_ok.1 hr
  have hd : (L - R).toInt = L.toInt - R.toInt := toInt_sub_ok (ssub_ok.2 (by omega))
  have ha : a.saddOverflow (L - R) = false := sadd_ok.2 (by rw [hd]; omega)
  refine ⟨ha, ?_⟩
  rw [toInt_add_ok ha, toInt_add_ok hl, toInt_add_ok hr, hd]
  omega

theorem add_add_slt {w : Nat} {L R a b : BitVec w}
    (hl : L.saddOverflow a = false) (hr : R.saddOverflow b = false)
    (h1 : min 0 L.toInt ≤ L.toInt - R.toInt) (h2 : L.toInt - R.toInt ≤ max 0 L.toInt) :
    a.saddOverflow (L - R) = false ∧
      ((a + (L - R)).toInt < b.toInt ↔ (L + a).toInt < (R + b).toInt) := by
  obtain ⟨h, e⟩ := add_add_s_core hl hr h1 h2
  exact ⟨h, by omega⟩

theorem add_add_sle {w : Nat} {L R a b : BitVec w}
    (hl : L.saddOverflow a = false) (hr : R.saddOverflow b = false)
    (h1 : min 0 L.toInt ≤ L.toInt - R.toInt) (h2 : L.toInt - R.toInt ≤ max 0 L.toInt) :
    a.saddOverflow (L - R) = false ∧
      ((a + (L - R)).toInt ≤ b.toInt ↔ (L + a).toInt ≤ (R + b).toInt) := by
  obtain ⟨h, e⟩ := add_add_s_core hl hr h1 h2
  exact ⟨h, by omega⟩

/-- The arithmetic of `lt`/`leq.r_add_add` (unsigned). -/
theorem add_add_u_core {w : Nat} {l r : Int} {a b : BitVec w}
    (hl : (BitVec.ofInt w l).uaddOverflow a = false)
    (hr : (BitVec.ofInt w r).uaddOverflow b = false)
    (l0 : 0 ≤ l) (l1 : l < 2 ^ w) (r0 : 0 ≤ r) (r1 : r < 2 ^ w) (h : min 0 l ≤ l - r) :
    a.uaddOverflow (BitVec.ofInt w l - BitVec.ofInt w r) = false ∧
      (a + (BitVec.ofInt w l - BitVec.ofInt w r)).toNat + (BitVec.ofInt w r + b).toNat =
        (BitVec.ofInt w l + a).toNat + b.toNat := by
  have el := toNat_ofInt_of_lt l0 l1
  have er := toNat_ofInt_of_lt r0 r1
  have hl' := uadd_ok.1 hl
  have hr' := uadd_ok.1 hr
  have hle : (BitVec.ofInt w l).usubOverflow (BitVec.ofInt w r) = false := usub_ok.2 (by omega)
  have hd := toNat_sub_ok hle
  have ha : a.uaddOverflow (BitVec.ofInt w l - BitVec.ofInt w r) = false :=
    uadd_ok.2 (by rw [hd]; omega)
  refine ⟨ha, ?_⟩
  rw [toNat_add_ok ha, toNat_add_ok hl, toNat_add_ok hr, hd]
  omega

theorem add_add_ult {w : Nat} {l r : Int} {a b : BitVec w}
    (hl : (BitVec.ofInt w l).uaddOverflow a = false)
    (hr : (BitVec.ofInt w r).uaddOverflow b = false)
    (l0 : 0 ≤ l) (l1 : l < 2 ^ w) (r0 : 0 ≤ r) (r1 : r < 2 ^ w) (h : min 0 l ≤ l - r) :
    a.uaddOverflow (BitVec.ofInt w l - BitVec.ofInt w r) = false ∧
      ((a + (BitVec.ofInt w l - BitVec.ofInt w r)).toNat < b.toNat ↔
        (BitVec.ofInt w l + a).toNat < (BitVec.ofInt w r + b).toNat) := by
  obtain ⟨h, e⟩ := add_add_u_core hl hr l0 l1 r0 r1 h
  exact ⟨h, by omega⟩

theorem add_add_ule {w : Nat} {l r : Int} {a b : BitVec w}
    (hl : (BitVec.ofInt w l).uaddOverflow a = false)
    (hr : (BitVec.ofInt w r).uaddOverflow b = false)
    (l0 : 0 ≤ l) (l1 : l < 2 ^ w) (r0 : 0 ≤ r) (r1 : r < 2 ^ w) (h : min 0 l ≤ l - r) :
    a.uaddOverflow (BitVec.ofInt w l - BitVec.ofInt w r) = false ∧
      ((a + (BitVec.ofInt w l - BitVec.ofInt w r)).toNat ≤ b.toNat ↔
        (BitVec.ofInt w l + a).toNat ≤ (BitVec.ofInt w r + b).toNat) := by
  obtain ⟨h, e⟩ := add_add_u_core hl hr l0 l1 r0 r1 h
  exact ⟨h, by omega⟩

theorem add_add_slt2 {w : Nat} {L R a b : BitVec w}
    (hl : L.saddOverflow a = false) (hr : R.saddOverflow b = false)
    (h1 : min 0 R.toInt ≤ R.toInt - L.toInt) (h2 : R.toInt - L.toInt ≤ max 0 R.toInt) :
    b.saddOverflow (R - L) = false ∧
      (a.toInt < (b + (R - L)).toInt ↔ (L + a).toInt < (R + b).toInt) := by
  obtain ⟨h, e⟩ := add_add_s_core hr hl h1 h2
  exact ⟨h, by omega⟩

theorem add_add_ult2 {w : Nat} {l r : Int} {a b : BitVec w}
    (hl : (BitVec.ofInt w l).uaddOverflow a = false)
    (hr : (BitVec.ofInt w r).uaddOverflow b = false)
    (l0 : 0 ≤ l) (l1 : l < 2 ^ w) (r0 : 0 ≤ r) (r1 : r < 2 ^ w) (h : min 0 r ≤ r - l) :
    b.uaddOverflow (BitVec.ofInt w r - BitVec.ofInt w l) = false ∧
      (a.toNat < (b + (BitVec.ofInt w r - BitVec.ofInt w l)).toNat ↔
        (BitVec.ofInt w l + a).toNat < (BitVec.ofInt w r + b).toNat) := by
  obtain ⟨h, e⟩ := add_add_u_core hr hl r0 r1 l0 l1 h
  exact ⟨h, by omega⟩

theorem add_add_sle2 {w : Nat} {L R a b : BitVec w}
    (hl : L.saddOverflow a = false) (hr : R.saddOverflow b = false)
    (h1 : min 0 R.toInt ≤ R.toInt - L.toInt) (h2 : R.toInt - L.toInt ≤ max 0 R.toInt) :
    b.saddOverflow (R - L) = false ∧
      (a.toInt ≤ (b + (R - L)).toInt ↔ (L + a).toInt ≤ (R + b).toInt) := by
  obtain ⟨h, e⟩ := add_add_s_core hr hl h1 h2
  exact ⟨h, by omega⟩

theorem add_add_ule2 {w : Nat} {l r : Int} {a b : BitVec w}
    (hl : (BitVec.ofInt w l).uaddOverflow a = false)
    (hr : (BitVec.ofInt w r).uaddOverflow b = false)
    (l0 : 0 ≤ l) (l1 : l < 2 ^ w) (r0 : 0 ≤ r) (r1 : r < 2 ^ w) (h : min 0 r ≤ r - l) :
    b.uaddOverflow (BitVec.ofInt w r - BitVec.ofInt w l) = false ∧
      (a.toNat ≤ (b + (BitVec.ofInt w r - BitVec.ofInt w l)).toNat ↔
        (BitVec.ofInt w l + a).toNat ≤ (BitVec.ofInt w r + b).toNat) := by
  obtain ⟨h, e⟩ := add_add_u_core hr hl r0 r1 l0 l1 h
  exact ⟨h, by omega⟩

end BitvecMod.Cmp

