import Bvr.Lib.Tactic

/-!
# Comparisons

Tactics and lemmas for the alternatives of `bv_lt` and `bv_leq`. `bvr_cmp`
lifts the body (splitting all its conditionals), reduces the value half of the
refinement to the values of the atoms (`bvr_cmp_sem`, keeping the literals as
`BitVec` values), and closes the goals with `omega`, on the integer values
(`toInt`, `toNat`) of the atoms, generalized, with the facts that it needs
(`bvr_cmp_omega`): the overflow facts, the bounds of the values, of their sums,
differences and negations, the relation of signed and unsigned values, the
cancellation of common factors and the quotients by constants.

Three helpers of the rules have their own lemmas: `unsigned_ub`
(`den_le_unsigned_ub`), `cancellable` (`cancellable_den`) and `lt_zero_aux`
(`refines_lt_zero_aux`).
-/

namespace Bvr.Lib

open Classical

/-! ## Booleans and widths -/

@[simp] theorem denB_of_bool {FS ρ} (b : Bool) : denB FS ρ (of_bool b) = some b := by
  cases b <;> rfl

@[simp] theorem WT_of_bool (b : Bool) : (of_bool b).WT := by
  cases b <;> simp [of_bool, v_true, v_false, WT_bool]

@[simp] theorem ty_of_bool (b : Bool) : (of_bool b).ty = .bool := by cases b <;> rfl

theorem ite_of_pos {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem binB_ite_l {α : Type} {f : α → α → Bool} {c : Prop} [Decidable c] (a a' b : Option α) :
    binB f (if c then a else a') b = if c then binB f a b else binB f a' b := by
  split <;> rfl

theorem binB_ite_r {α : Type} {f : α → α → Bool} {c : Prop} [Decidable c] (a b b' : Option α) :
    binB f a (if c then b else b') = if c then binB f a b else binB f a b' := by
  split <;> rfl

theorem WT_mk_masked {n z : Int} : (mk_masked n z).WT ↔ 0 < n := by
  refine ⟨fun w => ?_, mk_masked_WT⟩
  obtain ⟨k, hk, h, -⟩ := WT_bitVec.1 w
  rcases h with h | h <;> simp at h; omega

theorem exists_nat_of_pos {w : Int} (h : 0 < w) : ∃ n : Nat, w = n ∧ 0 < n :=
  ⟨w.toNat, by omega, by omega⟩

open Lean Meta Elab Tactic in
/-- Replaces the positive integer widths `w` (hypotheses `0 < w`) by natural
numbers. -/
partial def natWidths (g : MVarId) : MetaM MVarId := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOfArity ``LT.lt 4 do continue
    let w := ty.getArg! 3
    unless w.isFVar && (← whnfR (← inferType w)).isConstOf ``Int do continue
    let pf ← mkAppM ``exists_nat_of_pos #[d.toExpr]
    let (h, g) ← (← g.assert `hw (← inferType pf) pf).intro1P
    let [sg] := (← g.cases h).toList | return g
    let g := sg.mvarId
    return ← g.withContext do
      let some e := (← getLCtx).findDecl? fun d' =>
          if (d'.type.isAppOfArity ``And 2) && d'.type.appFn!.appArg!.isAppOfArity ``Eq 3 &&
            d'.type.appFn!.appArg!.appFn!.appArg! == w then some d' else none
        | return g
      let [sg] := (← g.cases e.fvarId).toList | return g
      let g := sg.mvarId
      g.withContext do
        let some eq := (← getLCtx).findDecl? fun d' =>
            if d'.type.isAppOfArity ``Eq 3 && d'.type.appFn!.appArg! == w then some d' else none
          | return g
        natWidths (← subst g eq.fvarId)
  return g

open Lean Meta Elab Tactic in
elab "bvr_nat_widths" : tactic => liftMetaTactic fun g => return [← natWidths g]

/-! ## The helpers, on values of known width -/

section
variable {n : Nat} (x : BitVec n)

theorem is_min_of_mk (s : Bool) (hn : 0 < n) :
    is_min_of s ⟨n, x⟩ = decide (if s then x.toInt = -2 ^ (n - 1) else x.toNat = 0) := by
  cases s <;> simp [is_min_of, min_for_true hn]

theorem is_max_of_mk (s : Bool) (hn : 0 < n) :
    is_max_of s ⟨n, x⟩ =
      decide (if s then x.toInt = 2 ^ (n - 1) - 1 else (x.toNat : Int) = 2 ^ n - 1) := by
  cases s <;> simp [is_max_of, max_for_true hn]

theorem const_keeps_in_range_mk (s : Bool) (y : BitVec n) :
    const_keeps_in_range s ⟨n, x⟩ ⟨n, y⟩ =
      decide ((0 ≤ to_z s ⟨n, x⟩ ∧ 0 ≤ to_z s ⟨n, x⟩ - to_z s ⟨n, y⟩ ∧
          to_z s ⟨n, x⟩ - to_z s ⟨n, y⟩ ≤ to_z s ⟨n, x⟩) ∨
        (to_z s ⟨n, x⟩ ≤ 0 ∧ to_z s ⟨n, x⟩ ≤ to_z s ⟨n, x⟩ - to_z s ⟨n, y⟩ ∧
          to_z s ⟨n, x⟩ - to_z s ⟨n, y⟩ ≤ 0)) := by
  unfold const_keeps_in_range zmin zmax
  generalize to_z s ⟨n, x⟩ = a; generalize to_z s ⟨n, y⟩ = b
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  split <;> split <;> omega

theorem is_int_min_mk' (hn : 0 < n) : is_int_min ⟨n, x⟩ = decide (x.toInt = -2 ^ (n - 1)) := by
  simp [is_int_min, min_for_true hn]

end

theorem sign_bit_eq {n : Nat} (hn : 0 < n) :
    BitVec.ofInt n (zshiftl 1 ((n : Int) - 1) % 2 ^ n) = BitVec.intMin n := by
  have e : zshiftl 1 ((n : Int) - 1) = 2 ^ (n - 1) := by
    simp only [zshiftl, Int.one_mul]; congr 1; omega
  have h1 : (2 : Int) ^ (n - 1) < 2 ^ n := by
    have : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by omega) (by omega)
    exact_mod_cast this
  rw [e, Int.emod_eq_of_lt (by have := two_pow_pos' (n - 1); omega) h1]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_intMin_of_pos hn, toNat_ofInt_of_lt (by have := two_pow_pos' (n - 1); omega) h1]
  have : (2 : Int) ^ (n - 1) = ((2 ^ (n - 1) : Nat) : Int) := by push_cast; rfl
  rw [this, Int.toNat_natCast]

theorem eq_intMin_iff {n : Nat} (hn : 0 < n) (x : BitVec n) :
    x = BitVec.intMin n ↔ x.toInt = -2 ^ (n - 1) := by
  rw [← BitVec.toInt_inj, BitVec.toInt_intMin_of_pos hn]

/-! ## The helpers on terms: `unsigned_ub`, `cancellable` -/

theorem two_pow_mono' {a b : Int} (h : a ≤ b) : (2 : Int) ^ a.toNat ≤ 2 ^ b.toNat := by
  have : 2 ^ a.toNat ≤ 2 ^ b.toNat := Nat.pow_le_pow_right (by omega) (by omega)
  exact_mod_cast this

theorem lt_two_pow_log2 {z : Int} (hz : 0 < z) : z < 2 ^ (log2 z + 1).toNat := by
  have hl := Nat.lt_log2_self (n := z.toNat)
  have e : (log2 z + 1).toNat = Nat.log2 z.toNat + 1 := by simp [log2]
  rw [e]
  have : ((z.toNat : Nat) : Int) < ((2 ^ (Nat.log2 z.toNat + 1) : Nat) : Int) := by
    exact_mod_cast hl
  push_cast at this; have := Int.toNat_of_nonneg (Int.le_of_lt hz); omega

theorem msb_of_bound_aux {FS : FloatSem} {ρ : Env} (K : Nat) : ∀ (v : Term), sizeOf v < K →
    ∀ {n : Nat} {x : BitVec n}, v.WT → v.ty = .bitVector n → den FS ρ n v = some x →
    (x.toNat : Int) < 2 ^ (msb_of v + 1).toNat := by
  induction K with
  | zero => intro v hv; omega
  | succ K ih =>
  intro v hK n x w ht h
  have hx : (x.toNat : Int) < 2 ^ n := by have := x.isLt; exact_mod_cast this
  have gen : msb_of v = size v - 1 → (x.toNat : Int) < 2 ^ (msb_of v + 1).toNat := by
    intro e; rw [e]; simp [size, ht]; exact hx
  rcases v with ⟨_ | _ | _ | _ | z | _ | ⟨op, a⟩ | ⟨op, a, b⟩ | ⟨op, g, l, r⟩ | _ | _ | _, T⟩
  all_goals simp only [Term.ty_mk] at ht
  all_goals subst ht
  case bitVec =>
    obtain ⟨-, h0, h1⟩ := WT_bitVec_bv.1 w
    simp only [den, Option.some.injEq] at h; subst h
    rw [msb_of_lit]
    split
    · rw [toNat_ofInt_of_lt h0 (by simpa using h1)]
      have := lt_two_pow_log2 (by omega : 0 < z); omega
    · simp only [size_of_ty_bitVector]; simpa using hx
  case unop =>
    cases op
    case bvExtend s k =>
      cases s
      · obtain ⟨⟨m, hm, ha, hk, e⟩, wa⟩ := WT_unop.1 w
        simp only [Ty.sort_eq, Ty.bitVector.injEq] at ha e
        obtain ⟨m, rfl⟩ : ∃ m' : Nat, m = m' := ⟨m.toNat, by omega⟩
        simp only [den, ha, Int.toNat_natCast, Option.map_eq_some_iff, Bool.false_eq_true,
          ite_false] at h
        obtain ⟨xa, ea, rfl⟩ := h
        have ih := ih a (by simp at hK; omega) wa ha ea
        have hmn : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
        have := xa.isLt
        rw [msb_of]
        simp only [firstSome, BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (by omega : xa.toNat < 2 ^ n)]
        simpa [HOrElse.hOrElse, OrElse.orElse, Option.orElse] using ih
      · exact gen (by rw [msb_of]; simp [firstSome]; all_goals (intros; simp_all))
    all_goals exact gen (by rw [msb_of]; simp [firstSome]; all_goals (intros; simp_all))
  case binop =>
    cases op
    case bitAnd =>
      obtain ⟨⟨⟨m, hm, ha⟩, hb, e⟩, wa, wb⟩ := WT_binop.1 w
      simp only [Ty.sort_eq] at ha hb e
      replace ha : a.ty = .bitVector n := e.symm
      simp only [den] at h
      cases ea : den FS ρ n a <;> cases eb : den FS ρ n b <;> simp [ea, eb, binOp] at h
      subst h
      rename_i xa xb
      have h1 := ih a (by simp at hK; omega) wa ha ea
      have h2 := ih b (by simp at hK; omega) wb (hb.trans ha) eb
      have l1 : xa.toNat &&& xb.toNat ≤ xa.toNat := Nat.and_le_left
      have l2 : xa.toNat &&& xb.toNat ≤ xb.toNat := Nat.and_le_right
      rw [msb_of]; simp only [firstSome, zmin]
      simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse]
      split <;> omega
    all_goals exact gen (by rw [msb_of]; simp [firstSome]; all_goals (intros; simp_all))
  case triop =>
    cases op
    case ite =>
      obtain ⟨⟨hg, hb, e⟩, wg, wl, wr⟩ := WT_triop.1 w
      simp only [Ty.sort_eq] at hg hb e
      simp only [den] at h
      have h1 := fun xl (el : den FS ρ n l = some xl) =>
        ih l (by simp at hK; omega) wl e.symm el
      have h2 := fun xr (er : den FS ρ n r = some xr) =>
        ih r (by simp at hK; omega) wr (hb.trans e.symm) er
      rw [msb_of]; simp only [firstSome, zmax]
      simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse]
      have m1 := two_pow_mono' (a := msb_of l + 1) (b := max (msb_of l) (msb_of r) + 1) (by omega)
      have m2 := two_pow_mono' (a := msb_of r + 1) (b := max (msb_of l) (msb_of r) + 1) (by omega)
      have : (if msb_of r ≤ msb_of l then msb_of l else msb_of r) = max (msb_of l) (msb_of r) := by
        split <;> omega
      rw [this]
      split at h
      · have := h1 x h; omega
      · have := h2 x h; omega
      · simp at h
    all_goals exact gen (by rw [msb_of]; simp [firstSome]; all_goals (intros; simp_all))
  all_goals exact gen (by rw [msb_of]; simp [firstSome]; all_goals (intros; simp_all))

/-- The values of a bit-vector term are below `2 ^ (msb_of v + 1)`. -/
theorem msb_of_bound {FS : FloatSem} {ρ : Env} {v : Term} {n : Nat} {x : BitVec n}
    (w : v.WT) (ht : v.ty = .bitVector n) (h : den FS ρ n v = some x) :
    (x.toNat : Int) < 2 ^ (msb_of v + 1).toNat :=
  msb_of_bound_aux (sizeOf v + 1) v (by omega) w ht h

theorem den_le_unsigned_ub {FS : FloatSem} {ρ : Env} {k : Kind} {n : Nat}
    (w : (Term.mk k (.bitVector n)).WT) :
    ∀ x, den FS ρ n (Term.mk k (.bitVector n)) = some x →
      (x.toNat : Int) ≤ unsigned_ub (Term.mk k (.bitVector n)) := by
  intro x h
  have := msb_of_bound w rfl h
  simp only [unsigned_ub, zshiftl, Int.one_mul]; omega

open Lean in
/-- The float semantics and the environment of the context. -/
def findSemantics (lctx : LocalContext) : Option (Expr × Expr) := do
  let fs ← lctx.findDecl? fun d => if d.type.isConstOf ``Bvr.FloatSem then some d.toExpr else none
  let ρ ← lctx.findDecl? fun d => if d.type.isConstOf ``Bvr.Env then some d.toExpr else none
  return (fs, ρ)

open Lean Meta Elab Tactic in
/-- Adds `den_le_unsigned_ub` for the well-typed terms of the context, when the
goal or a hypothesis mentions `unsigned_ub`. -/
elab "bvr_ub_facts" : tactic => liftMetaTactic fun g => g.withContext do
  let mut used := (← instantiateMVars (← g.getType)).find? (·.isConstOf ``unsigned_ub) |>.isSome
  for d in (← getLCtx) do
    if !d.isImplementationDetail &&
        ((← instantiateMVars d.type).find? (·.isConstOf ``unsigned_ub)).isSome then used := true
  unless used do return [g]
  let lctx ← getLCtx
  let some (fs, ρ) := findSemantics lctx | return [g]
  let mut g := g
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``Bvr.Term.WT 1 then
      try
        let pf ← mkAppOptM ``den_le_unsigned_ub #[some fs, some ρ, none, none, some d.toExpr]
        let (_, g') ← (← g.assert `hub (← inferType pf) pf).intro1P
        g := g'
      catch _ => pure ()
  return [g]

/-- The cancellable factors are positive (as signed integers when `s`). -/
theorem cancellable_den {FS : FloatSem} {ρ : Env} {s : Bool} {k : Kind} {n : Nat}
    (w : (Term.mk k (.bitVector n)).WT) (h : cancellable s (Term.mk k (.bitVector n)) = true) :
    ∀ A, den FS ρ n (Term.mk k (.bitVector n)) = some A →
      if s then 0 < A.toInt else 0 < A.toNat := by
  intro A hA
  cases k
  case bitVec z =>
    obtain ⟨-, h0, h1⟩ := WT_bitVec_bv.1 w
    simp only [den, Option.some.injEq] at hA; subst hA
    cases s
    · unfold cancellable sure_neq at h
      simp [firstSome, ty, size, bv_zero, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at h
      simp only [Bool.false_eq_true, ite_false]
      rw [toNat_ofInt_of_lt h0 (by simpa using h1)]; omega
    · simpa [cancellable, firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse] using h
  all_goals cases s
  all_goals (unfold cancellable at h; try unfold sure_neq at h)
  all_goals simp [firstSome, ty, size, bv_zero, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at h

open Lean Meta Elab Tactic in
/-- Adds `cancellable_den` for the cancellable terms of the context. -/
elab "bvr_cancel_facts" : tactic => liftMetaTactic fun g => g.withContext do
  let lctx ← getLCtx
  let some (fs, ρ) := findSemantics lctx | return [g]
  let mut g := g
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, _) := ty.eq? | continue
    unless lhs.isAppOfArity ``Bvr.cancellable 2 do continue
    let a := lhs.appArg!
    let some wt := lctx.findDecl? fun d' =>
        if d'.type.isAppOfArity ``Bvr.Term.WT 1 && d'.type.appArg! == a then some d'.toExpr
        else none
      | continue
    try
      let pf ← mkAppOptM ``cancellable_den
        #[some fs, some ρ, none, none, none, some wt, some d.toExpr]
      let (_, g') ← (← g.assert `hcan (← inferType pf) pf).intro1P
      g := g'
    catch _ => pure ()
  return [g]

/-- A quotient by `d` is at most `n` when `n * d` overflows. -/
theorem smtUDiv_ule_of_umulOverflow {w : Nat} {x n d : BitVec w} (h : n.umulOverflow d = true) :
    (x.smtUDiv d).ule n = true := by
  simp only [BitVec.umulOverflow, decide_eq_true_eq] at h
  have hd : d.toNat ≠ 0 := by intro e; rw [e] at h; have := Nat.two_pow_pos w; omega
  have := x.isLt
  simp only [BitVec.ule, decide_eq_true_eq, smtUDiv_toNat hd]
  have : x.toNat < (n.toNat + 1) * d.toNat := by rw [Nat.add_mul]; omega
  have := (Nat.div_lt_iff_lt_mul (by omega)).2 this
  omega

/-! ## The sign of a term (`lt_zero_aux`) -/

section
variable {FS : FloatSem} {O : Ops}

/-- `v <s 0`, the specification of `lt_zero_aux`. -/
abbrev LtZero (v : Term) : Term := .mk (.binop (.lt true) v (bv_zero (size v))) .bool

theorem WT_LtZero {v : Term} {n : Nat} (hn : 0 < n) (w : v.WT) (ht : v.ty = .bitVector n) :
    (LtZero v).WT := by
  simp [WT_binop, Binop.WT, bv_zero, size, ty, ht, WT_bitVec_bv, w]; omega

theorem denB_LtZero {ρ} {v : Term} {n : Nat} (hn : 0 < n) (ht : v.ty = .bitVector n) :
    denB FS ρ (LtZero v) = (den FS ρ n v).map BitVec.msb := by
  simp only [denB, ht, bv_zero, size, ty, size_of_ty_bitVector, Int.toNat_natCast,
    Int.natCast_pos, hn, ite_true, den, BitVec.ofInt_ofNat]
  cases den FS ρ n v <;> simp [BitVec.slt_zero_eq_msb]

/-- Refinement of `v <s 0`, by the sign of the value of `v`. -/
theorem refines_ltZero {v r : Term} (hr : ∀ n : Nat, 0 < n → v.WT → v.ty = .bitVector n →
      r.WT ∧ r.ty = .bool ∧ ∀ ρ x, den FS ρ n v = some x → denB FS ρ r = some x.msb) :
    Refines FS (LtZero v) r := by
  refine Refines.denB (fun _ => rfl) (fun w => ?_) (fun w ρ b h => ?_)
  all_goals
    obtain ⟨⟨⟨m, hm, ht⟩, -, -⟩, wv, -⟩ := WT_binop.1 w
    simp only [Ty.sort_eq] at ht
    obtain ⟨n, rfl⟩ : ∃ n : Nat, m = n := ⟨m.toNat, by omega⟩
    have hn : 0 < n := by omega
    obtain ⟨wr, tr, hr⟩ := hr n hn wv ht
  · exact ⟨wr, tr⟩
  · rw [denB_LtZero hn ht] at h
    cases e : den FS ρ n v <;> rw [e] at h <;> simp at h
    subst h; exact hr ρ _ e

/-- `ite g p p` is `p`. -/
theorem refines_ite_same {g p : Term} :
    Refines FS (.mk (.triop .ite g p p) .bool) p := by
  refine Refines.denB (fun _ => rfl) (fun w => ?_) (fun w ρ b h => ?_)
  · obtain ⟨⟨-, -, e⟩, -, wp, -⟩ := WT_triop.1 w
    simp at e; exact ⟨wp, e.symm⟩
  · simp only [denB] at h
    split at h <;> simp_all

theorem lt_zero_aux_refines (hO : O.Sound FS) (K : Nat) : ∀ v : Term, sizeOf v < K →
    Refines FS (LtZero v) (lt_zero_aux O v) := by
  induction K with
  | zero => intro v h; omega
  | succ K ih =>
  intro v hK
  have IH := fun a (h : sizeOf a < sizeOf v) => ih a (by omega)
  rcases v with ⟨_ | _ | _ | _ | _ | _ | ⟨op, a⟩ | ⟨op, a, b⟩ | ⟨op, g, l, r⟩ | _ | _ | _, T⟩
  case unop =>
    have IHa := IH a (by simp; omega)
    cases op
    case bvExtend s k =>
      cases s
      · by_cases hk : 0 < k
        · rw [lt_zero_aux]; simp only [firstSome]
          simp only [HOrElse.hOrElse, OrElse.orElse, Option.orElse, gt_iff_lt, hk, decide_true,
            ite_true, Option.getD_some]
          refine refines_ltZero fun n hn w ht => ⟨by simp [v_false, WT_bool], rfl, fun ρ x h => ?_⟩
          obtain ⟨⟨m, hm, ha, hk', e⟩, wa⟩ := WT_unop.1 w
          simp only [Ty.sort_eq, Term.ty_mk] at ha e ht
          rw [ht] at e; simp at e
          obtain ⟨m, rfl⟩ : ∃ m' : Nat, m = m' := ⟨m.toNat, by omega⟩
          simp only [den, ha, Int.toNat_natCast, Option.map_eq_some_iff] at h
          obtain ⟨xa, -, rfl⟩ := h
          simp [v_false, denB, BitVec.msb_setWidth, BitVec.getLsbD_of_ge xa (n - 1) (by omega)]
        · rw [lt_zero_aux]; simp only [firstSome]
          simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse, hk]
          exact Refines.refl
      · rw [lt_zero_aux]; simp only [firstSome]
        simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse]
        refine Refines.trans (refines_ltZero fun n hn w ht => ?_) IHa
        obtain ⟨⟨m, hm, ha, hk, e⟩, wa⟩ := WT_unop.1 w
        simp only [Ty.sort_eq, Term.ty_mk] at ha e ht
        rw [ht] at e; simp at e
        obtain ⟨m, rfl⟩ : ∃ m' : Nat, m = m' := ⟨m.toNat, by omega⟩
        refine ⟨WT_LtZero (by omega) wa ha, rfl, fun ρ x h => ?_⟩
        simp only [den, ha, Int.toNat_natCast, Option.map_eq_some_iff] at h
        obtain ⟨xa, ea, rfl⟩ := h
        rw [denB_LtZero (by omega) ha, ea]
        simp only [Option.map_some, ite_true, BitVec.msb_signExtend]
        by_cases hmn : m ≥ n
        · obtain rfl : m = n := by omega
          simp [hn, BitVec.msb]
        · simp [hmn, hn]
    case bvNot =>
      rw [lt_zero_aux]; simp only [firstSome]
      simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse]
      refine Refines.trans (refines_ltZero fun n hn w ht => ?_) (lift_b_not hO IHa)
      obtain ⟨⟨m, hm, -, e⟩, wa⟩ := WT_unop.1 w
      simp only [Ty.sort_eq, Term.ty_mk] at e ht
      rw [ht] at e; have ha := e.symm
      refine ⟨by simp [b_not.spec, WT_unop, Unop.WT, WT_LtZero hn wa ha], rfl, fun ρ x h => ?_⟩
      simp only [den, Option.map_eq_some_iff] at h
      obtain ⟨xa, ea, rfl⟩ := h
      show Option.map (fun b => !b) (denB FS ρ (LtZero a)) = _
      rw [denB_LtZero hn ha, ea]; simp [hn]
    case bvOfBool k =>
      rw [lt_zero_aux]; simp only [firstSome]
      simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse]
      by_cases hk : 1 < k
      · simp only [hk, ite_true, Option.getD_some]
        refine refines_ltZero fun n hn w ht => ⟨by simp [v_false, WT_bool], rfl, fun ρ x h => ?_⟩
        obtain ⟨⟨-, hb, e⟩, wb⟩ := WT_unop.1 w
        simp only [Ty.sort_eq, Term.ty_mk] at hb e ht
        rw [ht] at e; simp at e; subst e
        simp only [den, Option.map_eq_some_iff] at h
        obtain ⟨c, -, rfl⟩ := h
        cases c <;> simp [v_false, denB] <;> omega
      · simp [hk]; exact Refines.refl
    all_goals (rw [lt_zero_aux]; simp only [firstSome])
    all_goals simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse]
    all_goals first | exact Refines.refl | (intros; simp_all)
  case binop =>
    have IHa := IH a (by simp; omega)
    cases op
    case rem s =>
      cases s
      · rw [lt_zero_aux]; simp only [firstSome]
        simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse]
        all_goals first | exact Refines.refl | (intros; simp_all)
      rw [lt_zero_aux]; simp only [firstSome]
      simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse]
      refine Refines.trans (refines_ltZero fun n hn w ht => ?_)
        (lift_b_and hO IHa (lift_b_not hO (lift_sem_eq hO Refines.refl Refines.refl)))
      obtain ⟨⟨-, hb, e⟩, wa, wb⟩ := WT_binop.1 w
      simp only [Ty.sort_eq, Term.ty_mk] at hb e ht
      subst ht
      have ha : a.ty = .bitVector n := e.symm
      rw [ha] at hb
      refine ⟨?_, rfl, fun ρ x h => ?_⟩
      · simp [b_and.spec, b_not.spec, sem_eq.spec, WT_binop, WT_unop, Binop.WT, Unop.WT,
          WT_LtZero hn wa ha, bv_zero, WT_bitVec_bv, w]; omega
      · simp only [den] at h
        cases ea : den FS ρ n a <;> cases eb : den FS ρ n b <;> simp [ea, eb, binOp] at h
        subst h
        show andB (denB FS ρ (LtZero a)) ((denB FS ρ (sem_eq.spec _ _)).map (!·)) = _
        rw [denB_LtZero hn ha, ea]
        simp [sem_eq.spec, denB, hn, den, ea, eb, binOp, BitVec.msb_srem, bv_zero]
    case bvConcat =>
      rw [lt_zero_aux]; simp only [firstSome]
      simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse]
      refine Refines.trans (refines_ltZero fun n hn w ht => ?_) IHa
      obtain ⟨⟨m1, m2, h1, h2, ha, hb, e⟩, wa, wb⟩ := WT_binop.1 w
      simp only [Ty.sort_eq, Term.ty_mk] at ha hb e ht
      rw [ht] at e; simp at e
      obtain ⟨m1, rfl⟩ : ∃ m' : Nat, m1 = m' := ⟨m1.toNat, by omega⟩
      obtain ⟨m2, rfl⟩ : ∃ m' : Nat, m2 = m' := ⟨m2.toNat, by omega⟩
      obtain rfl : n = m1 + m2 := by omega
      refine ⟨WT_LtZero (by omega) wa ha, rfl, fun ρ x h => ?_⟩
      simp only [den, ha, hb, Int.toNat_natCast] at h
      cases ea : den FS ρ m1 a <;> cases eb : den FS ρ m2 b <;> simp [ea, eb] at h
      subst h
      rw [denB_LtZero (by omega) ha, ea]
      simp [BitVec.msb_append, show m1 ≠ 0 by omega]
    all_goals (rw [lt_zero_aux]; simp only [firstSome])
    all_goals simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse]
    all_goals first | exact Refines.refl | (intros; simp_all)
  case triop =>
    cases op
    case ite =>
      have IHl := IH l (by simp; omega)
      have IHr := IH r (by simp; omega)
      rw [lt_zero_aux]; simp only [firstSome]
      simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse, equal]
      split
      · rename_i heq
        refine Refines.trans (refines_ltZero fun n hn w ht => ?_)
          (Refines.trans (Refines.ite (g := g) Refines.refl IHl (heq ▸ IHr) (fun _ => rfl))
            refines_ite_same)
        obtain ⟨⟨hg, hb, e⟩, wg, wl, wr⟩ := WT_triop.1 w
        simp only [Ty.sort_eq, Term.ty_mk] at hg hb e ht
        rw [ht] at e
        refine ⟨?_, rfl, fun ρ x h => ?_⟩
        · simp [WT_triop, Triop.WT, hg, wg, WT_LtZero hn wl e.symm,
            WT_LtZero hn wr (hb.trans e.symm)]
        · simp only [den] at h
          show (match denB FS ρ g with
            | some true => denB FS ρ (LtZero l) | some false => denB FS ρ (LtZero r)
            | none => none) = _
          rw [denB_LtZero hn e.symm, denB_LtZero hn (hb.trans e.symm)]
          split at h <;> simp_all
      · exact Refines.refl
    all_goals (rw [lt_zero_aux]; simp only [firstSome])
    all_goals simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse]
    all_goals first | exact Refines.refl | (intros; simp_all)
  all_goals (rw [lt_zero_aux]; simp only [firstSome])
  all_goals simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse]
  all_goals first | exact Refines.refl | (intros; simp_all)

theorem refines_lt_zero_aux (hO : O.Sound FS) {v : Term} {T : Ty} :
    Refines FS (bv_lt.spec true v (.mk (.bitVec 0) T)) (lt_zero_aux O v) := by
  refine Refines.of_WT fun w => ?_
  obtain ⟨⟨⟨m, -, ha⟩, hb, -⟩, -, -⟩ := WT_binop.1 w
  simp only [Ty.sort_eq, Term.ty_mk] at ha hb
  have : Term.mk (.bitVec 0) T = bv_zero (size v) := by simp [bv_zero, size, ty, ha, hb]
  rw [bv_lt.spec, this]
  exact lt_zero_aux_refines hO _ v (Nat.lt_succ_self _)

end

/-! ## Facts for `omega` -/

theorem toInt_neg_cases {w : Nat} (x : BitVec w) :
    (-x).toInt = -x.toInt ∨ ((-x).toInt = x.toInt ∧ x.toInt = -2 ^ (w - 1)) := by
  by_cases h : x = BitVec.intMin w
  · subst h
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · simp [BitVec.toInt_zero_length]
    · right; simp [BitVec.neg_intMin, BitVec.toInt_intMin, hw]
  · exact .inl (BitVec.toInt_neg_of_ne_intMin h)

theorem toNat_neg_cases {w : Nat} (x : BitVec w) :
    (x.toNat = 0 ∧ (-x).toNat = 0) ∨ (0 < x.toNat ∧ ((-x).toNat : Int) = 2 ^ w - x.toNat) := by
  rw [BitVec.toNat_neg]
  have := x.isLt
  by_cases h : x.toNat = 0
  · left; simp [h]
  · right; rw [Nat.mod_eq_of_lt (by omega), Int.ofNat_sub (by omega)]; push_cast; omega

theorem toNat_add_cases {w : Nat} (x y : BitVec w) :
    ((x + y).toNat : Int) = x.toNat + y.toNat ∨
      ((x + y).toNat : Int) = x.toNat + y.toNat - 2 ^ w := by
  have := x.isLt; have := y.isLt
  have e : ((2 ^ w : Nat) : Int) = 2 ^ w := by push_cast; rfl
  rw [BitVec.toNat_add]
  by_cases h : x.toNat + y.toNat < 2 ^ w
  · left; rw [Nat.mod_eq_of_lt h]; push_cast; rfl
  · right
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Int.ofNat_sub (by omega), e]
    push_cast; rfl

theorem toNat_sub_cases {w : Nat} (x y : BitVec w) :
    ((x - y).toNat : Int) = x.toNat - y.toNat ∨
      ((x - y).toNat : Int) = x.toNat - y.toNat + 2 ^ w := by
  have := x.isLt; have := y.isLt
  have e : ((2 ^ w : Nat) : Int) = 2 ^ w := by push_cast; rfl
  rw [BitVec.toNat_sub]
  by_cases h : y.toNat ≤ x.toNat
  · left
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Int.ofNat_sub (by omega),
      Int.natCast_add, Int.ofNat_sub (by omega), e]
    omega
  · right
    rw [Nat.mod_eq_of_lt (by omega), Int.natCast_add, Int.ofNat_sub (by omega), e]
    omega

theorem toNat_bounds {w : Nat} (x : BitVec w) : (x.toNat : Int) < 2 ^ w := by
  have := x.isLt; exact_mod_cast this

theorem toInt_toNat_cases {w : Nat} (x : BitVec w) :
    (2 * (x.toNat : Int) < 2 ^ w ∧ x.toInt = x.toNat) ∨
      (2 ^ w ≤ 2 * (x.toNat : Int) ∧ x.toInt = x.toNat - 2 ^ w) := by
  have e : ((2 ^ w : Nat) : Int) = 2 ^ w := by push_cast; rfl
  rw [BitVec.toInt_eq_toNat_cond, e]
  split
  · left; exact ⟨by omega, rfl⟩
  · right; exact ⟨by omega, rfl⟩

/-- The powers of two of a width, for `omega`. -/
theorem two_pow_facts (w : Nat) :
    ((2 ^ w : Nat) : Int) = (2 : Int) ^ w ∧ ((2 ^ (w - 1) : Nat) : Int) = (2 : Int) ^ (w - 1) ∧
      ((2 : Int) ^ w = 2 * 2 ^ (w - 1) ∨ w = 0) ∧ (0 : Int) < 2 ^ (w - 1) := by
  refine ⟨by push_cast; rfl, by push_cast; rfl, ?_, two_pow_pos' _⟩
  rcases Nat.eq_zero_or_pos w with h | h
  · exact .inr h
  · exact .inl (two_pow_pred h)

/-- Cancelling a positive factor, for `omega`. -/
theorem mul_cmp_facts (p q r : Int) :
    0 < p → (p * q < p * r ↔ q < r) ∧ (p * q ≤ p * r ↔ q ≤ r) := fun h =>
  ⟨Int.mul_lt_mul_left h, Int.mul_le_mul_left h⟩

theorem nat_mul_cmp_facts (p q r : Nat) :
    0 < p → (p * q < p * r ↔ q < r) ∧ (p * q ≤ p * r ↔ q ≤ r) := fun h =>
  ⟨Nat.mul_lt_mul_left h, Nat.mul_le_mul_left_iff h⟩

/-- `tdiv_facts`, for natural numbers. -/
theorem div_facts (C2 C1 X : Nat) : C1 ≠ 0 →
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
theorem tdiv_facts (C2 C1 X : Int) : C1 ≠ 0 →
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

theorem toInt_smtSDiv_facts {w : Nat} (a b : BitVec w) : b.toInt ≠ 0 →
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

theorem toNat_smtUDiv_facts {w : Nat} (a b : BitVec w) : b.toNat ≠ 0 →
    (a.smtUDiv b).toNat = a.toNat / b.toNat := smtUDiv_toNat

/-! ## Adding the facts -/

open Lean Meta in
/-- The subterms `x` of the goal and hypotheses (bit-vectors of any width) such
that `f x` is a subterm, where `p` recognizes `f x` and returns `x`. -/
def collectArgs (g : MVarId) (p : Expr → Option Expr) : MetaM (Array Expr) := g.withContext do
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
def addFacts (g : MVarId) (lems : List Name) (xs : Array Expr) : MetaM MVarId := do
  let mut g := g
  for x in xs do
    for lem in lems do
      let pf ← g.withContext (mkAppM lem #[x])
      let (_, g') ← (← g.assert `hbd (← g.withContext (inferType pf)) pf).intro1P
      g := g'
  return g

open Lean Meta in
/-- `collectArgs`, for binary functions. -/
def collectArgs2 (g : MVarId) (p : Expr → Option (Expr × Expr)) :
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
def addFacts2 (g : MVarId) (lem : Name) (xys : Array (Expr × Expr)) : MetaM MVarId := do
  let mut g := g
  for (x, y) in xys do
    let pf ← g.withContext (mkAppM lem #[x, y])
    let (_, g') ← (← g.assert `hbd (← g.withContext (inferType pf)) pf).intro1P
    g := g'
  return g

open Lean Meta Elab Tactic in
/-- Adds the facts on the values of the bit-vectors of the goal and hypotheses
that `omega` needs: their bounds, those of their negations, and the relation
between their signed and unsigned values (when both occur). -/
elab "bvr_cmp_bounds" : tactic => liftMetaTactic fun g => do
  let arg (f : Name) (e : Expr) : Option Expr :=
    if e.isAppOfArity f 2 then some e.appArg! else none
  let neg (f : Name) (e : Expr) : Option Expr :=
    (arg f e).bind fun x => if x.isAppOfArity ``Neg.neg 3 then some x.appArg! else none
  let g ← addFacts g [``toInt_neg_cases] (← collectArgs g (neg ``BitVec.toInt))
  let g ← addFacts g [``toNat_neg_cases] (← collectArgs g (neg ``BitVec.toNat))
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
  let g ← addFacts2 g ``toNat_add_cases
    (← unknown ``HAdd.hAdd (← collectArgs2 g (bin ``HAdd.hAdd)))
  let g ← addFacts2 g ``toNat_sub_cases
    (← unknown ``HSub.hSub (← collectArgs2 g (bin ``HSub.hSub)))
  let dedup (xs : Array Expr) : MetaM (Array Expr) := g.withContext do
    xs.foldlM (init := #[]) fun acc x => do
      if ← acc.anyM (isDefEq x ·) then return acc else return acc.push x
  let is ← dedup (← collectArgs g (arg ``BitVec.toInt))
  let ns ← dedup (← collectArgs g (arg ``BitVec.toNat))
  let g ← addFacts g [``toInt_bounds] is
  let g ← addFacts g [``toNat_bounds] ns
  return [← addFacts g [``toInt_toNat_cases] (is.filter ns.contains)]

open Lean Meta Elab Tactic in
/-- Adds the facts on the powers of two of the widths of the bit-vectors of the
context. -/
elab "bvr_pow_facts" : tactic => liftMetaTactic fun g => g.withContext do
  let mut ws : Array Expr := #[]
  for d in (← getLCtx) do
    let ty ← whnfR (← instantiateMVars d.type)
    if ty.isAppOfArity ``BitVec 1 && !ws.contains ty.appArg! then ws := ws.push ty.appArg!
  return [← addFacts g [``two_pow_facts] ws]

open Lean Meta in
/-- Generalizes the values (`toInt`, `toNat`) of the bit-vectors of the goal
and hypotheses, and the powers of two, so that `omega` treats them as atoms. -/
partial def genValues (g : MVarId) : MetaM MVarId := g.withContext do
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
  genValues g

open Lean Meta Elab Tactic in
elab "bvr_gen_values" : tactic => liftMetaTactic fun g => return [← genValues g]

open Lean Meta in
/-- The products `p * q` of integers (or natural numbers) of the goal and
hypotheses. -/
def collectProducts (g : MVarId) (int : Bool) : MetaM (Array (Expr × Expr)) :=
  collectArgs2 g fun e =>
    if e.isAppOfArity ``HMul.hMul 6 && (e.getArg! 0).isConstOf (if int then ``Int else ``Nat) &&
        (e.getArg! 4).int?.isNone && (e.getArg! 5).int?.isNone &&
        (e.getArg! 4).nat?.isNone && (e.getArg! 5).nat?.isNone then
      some (e.getArg! 4, e.getArg! 5)
    else none

open Lean Meta Elab Tactic in
/-- Adds the facts on the products and quotients of the goal and hypotheses
that `omega` needs: cancelling a common factor of two products, and the
quotients by a divisor that also multiplies. -/
elab "bvr_mul_facts" : tactic => liftMetaTactic fun g => do
  let mut g := g
  for (int, lem) in [(true, ``mul_cmp_facts), (false, ``nat_mul_cmp_facts)] do
    let ps ← collectProducts g int
    for (p, q) in ps do
      for (p', r) in ps do
        if p == p' && q != r then
          let pf ← g.withContext (mkAppM lem #[p, q, r])
          let (_, g') ← (← g.assert `hmul (← g.withContext (inferType pf)) pf).intro1P
          g := g'
  let divs (f : Name) := collectArgs2 g fun e =>
    if e.isAppOfArity f 3 then some (e.getArg! 1, e.getArg! 2) else none
  let sdivs ← divs ``BitVec.smtSDiv
  let udivs ← divs ``BitVec.smtUDiv
  g ← addFacts2 g ``toInt_smtSDiv_facts sdivs
  g ← addFacts2 g ``toNat_smtUDiv_facts udivs
  for (int, ds, val, lem) in [(true, sdivs, ``BitVec.toInt, ``tdiv_facts),
      (false, udivs, ``BitVec.toNat, ``div_facts)] do
    let ps ← collectProducts g int
    for (a, b) in ds do
      let (c2, c1) ← g.withContext do return (← mkAppM val #[a], ← mkAppM val #[b])
      for (x, q) in ps do
        if ← g.withContext (isDefEq q c1) then
          let pf ← g.withContext (mkAppM lem #[c2, c1, x])
          let (_, g') ← (← g.assert `hdiv (← g.withContext (inferType pf)) pf).intro1P
          g := g'
  return [g]

open Lean Meta Elab Tactic in
/-- Clears the facts that only hold under an unknown checked flag
(`c.signed = true → _`), which `omega` cannot use. -/
elab "bvr_clear_flags" : tactic => liftMetaTactic fun g => g.withContext do
  let mut g := g
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let .forallE _ dom _ _ := ty then
      if let some (_, lhs, _) := dom.eq? then
        if lhs.isAppOfArity ``Bvr.Checked.signed 1 || lhs.isAppOfArity ``Bvr.Checked.unsigned 1 then
          g ← g.clear d.fvarId
  return [g]

/-! ## Tactics -/

/-- `bvr_wt`, for the terms with masked literals (such as the sign bit). -/
macro "bvr_cmp_wt" : tactic => `(tactic| (
  simp only [mk_bv, WT_binop, WT_unop, WT_triop, WT_mk_masked, mk_masked_ty, Term.ty_mk,
    Ty.sort_eq]
  bvr_wt))

/-- `bvr_facts`, keeping the literals as values (`BitVec.ofInt n z`). -/
macro "bvr_cmp_facts" : tactic => `(tactic| (
  (try simp [WT_binop, WT_unop, WT_triop, Binop.WT, Unop.WT, Triop.WT, bv_zero, bv_one,
    mk_masked, mk_bv, -bv_of_lit_bv, -bv_of_lit_bv', -to_z_mk] at *)
  (try bvr_split)
  (try bvr_destruct_tys)
  (try simp only [Term.ty_mk] at *)
  (try subst_vars)
  (try simp only [Ty.bitVector.injEq, Ty.loc.injEq] at *)
  (try subst_vars)
  (try simp [WT_binop, WT_unop, WT_triop, Binop.WT, Unop.WT, Triop.WT, bv_zero, bv_one,
    mk_masked, mk_bv, -bv_of_lit_bv, -bv_of_lit_bv', -to_z_mk] at *)
  (try bvr_split)
  (try subst_vars)))

/-- `bvr_rule_core`, splitting all the conditionals of the body. -/
macro "bvr_cmp_core" : tactic => `(tactic| (
  intro FS O hO
  intros
  (try bvr_flags)
  (try subst_vars)
  simp only [bvr_spec, ty, signed_to_unsigned_cmp]
  (repeat' split)
  all_goals (try bvr_lift_body)
  all_goals (try simp only [bvr_spec, ty])
  all_goals (try exact Refines.refl)
  all_goals (try apply Refines.denB (fun _ => rfl))))

/-- The value half of `Refines.denB`, reduced to facts on the values of the
atoms, with the literals as variables. -/
macro "bvr_cmp_sem" : tactic => `(tactic| (
  intro w ρ x h
  have w' := w
  bvr_cmp_facts
  bvr_nat_widths
  bvr_lits
  simp only [denB_of_bool, Int.natCast_pos, Int.toNat_natCast, BitVec.ofInt_ofNat] at *
  simp (disch := assumption) only [ite_of_pos, sign_bit_eq] at *
  bvr_ub_facts
  bvr_cancel_facts
  bvr_cases
  all_goals bvr_bool_vars
  all_goals (try simp only [Option.some.injEq, forall_eq, forall_eq'] at *)
  all_goals (try (simp [ckOp] at h; done))
  all_goals (try (repeat' split at h))
  all_goals (try simp only [sub_overflows_mk (hn := by assumption),
    add_overflows_mk (hn := by assumption), mul_overflows_mk (hn := by assumption),
    is_int_min_mk' (hn := by assumption), is_min_of_mk (hn := by assumption),
    is_max_of_mk (hn := by assumption)] at *)))

/-- Reduces the goals left by `bvr_cmp_sem` to facts on the integer values of
the atoms. -/
macro "bvr_cmp_pre" : tactic => `(tactic| (
  (try simp (disch := assumption) only [negOp_some, eq_intMin_iff] at *)
  all_goals simp_all [BitVec.slt_eq_decide, BitVec.ult_eq_decide, BitVec.sle_eq_decide,
    BitVec.ule_eq_decide, ← BitVec.toNat_inj, binB_ite_l, binB_ite_r, -BitVec.toInt_ofInt,
    -BitVec.toNat_ofInt, -BitVec.toNat_neg, -BitVec.toNat_add, -BitVec.toNat_sub,
    -BitVec.toNat_mul, -BitVec.toInt_add, -BitVec.toInt_sub, -BitVec.toInt_mul,
    -BitVec.toNat_udiv, -BitVec.toNat_umod, -BitVec.toInt_srem, -BitVec.toNat_intMin,
    divisible, const_keeps_in_range_mk]
  all_goals (try simp only [Int.natCast_dvd_natCast, Nat.dvd_iff_mod_eq_zero] at *)
  all_goals (try simp only [Int.dvd_iff_tmod_eq_zero] at *)
  all_goals (try simp (disch := assumption) only [BitVec.toNat_intMin_of_pos,
    BitVec.toInt_intMin_of_pos] at *)
  all_goals bvr_split
  all_goals bvr_ovf_eqs
  all_goals (try simp only [sadd_ok, ssub_ok, smul_ok, uadd_ok, usub_ok, umul_ok] at *)
  all_goals (try simp only [BitVec.saddOverflow, BitVec.ssubOverflow, BitVec.smulOverflow,
    BitVec.uaddOverflow, BitVec.usubOverflow, BitVec.umulOverflow, decide_eq_true_eq,
    Bool.or_eq_true] at *)
  all_goals bvr_split
  all_goals bvr_clear_flags
  all_goals bvr_mul_facts
  all_goals bvr_cmp_bounds
  all_goals (try push_cast at *)))

/-- Closes the goals left by `bvr_cmp_sem`, by reasoning on the integer values
of the atoms. -/
macro "bvr_cmp_omega" : tactic => `(tactic| (
  bvr_cmp_pre
  all_goals bvr_pow_facts
  all_goals bvr_gen_values
  all_goals omega))

/-- Proves the statement of an alternative of `bv_lt` or `bv_leq`, as far as
it can. -/
macro "bvr_cmp" : tactic => `(tactic| (
  bvr_cmp_core
  all_goals first
    | (bvr_wt; done)
    | (bvr_cmp_wt; done)
    | (bvr_cmp_sem
       all_goals (try (bvr_cmp_omega; done)))))

/-- `bvr_cmp`, with lemmas for the value goals that `omega` does not close. -/
syntax "bvr_cmp_using " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| bvr_cmp_using [$ls,*]) => `(tactic| (
      bvr_cmp_core
      all_goals first
        | (bvr_wt; done)
        | (bvr_cmp_wt; done)
        | (bvr_cmp_sem
           all_goals (try (simp_all [$ls,*]; done))
           all_goals (try (bvr_cmp_omega; done)))))

end Bvr.Lib
