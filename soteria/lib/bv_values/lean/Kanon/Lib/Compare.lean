import Kanon.Lib.Msb

/-!
# Comparisons

Tactics and lemmas for the alternatives of `bv_lt` and `bv_leq`. `kanon_cmp`
lifts the body (splitting all its conditionals), reduces the value half of the
refinement to the values of the atoms (`kanon_cmp_sem`, keeping the literals as
`BitVec` values), and closes the goals with `omega`, on the integer values
(`toInt`, `toNat`) of the atoms, generalized, with the facts that it needs
(`kanon_cmp_omega`): the overflow facts, the bounds of the values, of their sums,
differences and negations, the relation of signed and unsigned values, the
cancellation of common factors and the quotients by constants.

Three helpers of the rules have their own lemmas: `unsigned_ub`
(`den_le_unsigned_ub`), `cancellable` (`cancellable_den`) and `lt_zero_aux`
(`refines_lt_zero_aux`).
-/

namespace Kanon.Lib

open Classical

/-! ## Booleans and widths -/


theorem binB_ite_l {α : Type} {f : α → α → Bool} {c : Prop} [Decidable c] (a a' b : Option α) :
    binB f (if c then a else a') b = if c then binB f a b else binB f a' b := by
  split <;> rfl

theorem binB_ite_r {α : Type} {f : α → α → Bool} {c : Prop} [Decidable c] (a b b' : Option α) :
    binB f a (if c then b else b') = if c then binB f a b else binB f a b' := by
  split <;> rfl

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
  have e : zshiftl 1 ((n : Int) - 1) = ((2 ^ (n - 1) : Nat) : Int) := by
    simp only [zshiftl, Int.one_mul]; push_cast; congr 1; omega
  rw [BitVec.ofInt_emod_two_pow, e, BitVec.ofInt_natCast, ← BitVec.toNat_inj,
    BitVec.toNat_intMin_of_pos hn, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.two_pow_pred_lt_two_pow hn)]

theorem eq_intMin_iff {n : Nat} (hn : 0 < n) (x : BitVec n) :
    x = BitVec.intMin n ↔ x.toInt = -2 ^ (n - 1) := by
  rw [← BitVec.toInt_inj, BitVec.toInt_intMin_of_pos hn]

/-! ## The helpers on terms: `unsigned_ub`, `cancellable` -/

/-- The values of a bit-vector term are below `2 ^ (msb_of v + 1)`. -/
theorem msb_of_bound {FS : FloatSem} {ρ : Env} {v : Term} {n : Nat} {x : BitVec n}
    (w : v.WT) (ht : v.ty = .TBitVector n) (h : den FS ρ n v = some x) :
    (x.toNat : Int) < 2 ^ (msb_of v + 1).toNat := by
  exact_mod_cast den_msb w ht h

theorem den_le_unsigned_ub {FS : FloatSem} {ρ : Env} {k : Kind} {n : Nat}
    (w : (Term.mk k (.TBitVector n)).WT) :
    ∀ x, den FS ρ n (Term.mk k (.TBitVector n)) = some x →
      (x.toNat : Int) ≤ unsigned_ub (Term.mk k (.TBitVector n)) := by
  intro x h
  have := msb_of_bound w rfl h
  simp only [unsigned_ub, zshiftl, Int.one_mul]; omega

open Lean in
/-- The float semantics and the environment of the context. -/
def findSemantics (lctx : LocalContext) : Option (Expr × Expr) := do
  let fs ← lctx.findDecl? fun d => if d.type.isConstOf ``Kanon.FloatSem then some d.toExpr else none
  let ρ ← lctx.findDecl? fun d => if d.type.isConstOf ``Kanon.Env then some d.toExpr else none
  return (fs, ρ)

open Lean Meta Elab Tactic in
/-- Adds `den_le_unsigned_ub` for the well-typed terms of the context, when the
goal or a hypothesis mentions `unsigned_ub`. -/
elab "kanon_ub_facts" : tactic => liftMetaTactic fun g => g.withContext do
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
    if ty.isAppOfArity ``Kanon.Term.WT 1 then
      try
        let pf ← mkAppOptM ``den_le_unsigned_ub #[some fs, some ρ, none, none, some d.toExpr]
        let (_, g') ← (← g.assert `hub (← inferType pf) pf).intro1P
        g := g'
      catch _ => pure ()
  return [g]

/-- The cancellable factors are positive (as signed integers when `s`). -/
theorem cancellable_den {FS : FloatSem} {ρ : Env} {s : Bool} {k : Kind} {n : Nat}
    (w : (Term.mk k (.TBitVector n)).WT) (h : cancellable s (Term.mk k (.TBitVector n)) = true) :
    ∀ A, den FS ρ n (Term.mk k (.TBitVector n)) = some A →
      if s then 0 < A.toInt else 0 < A.toNat := by
  intro A hA
  cases k
  case BitVec z =>
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
elab "kanon_cancel_facts" : tactic => liftMetaTactic fun g => g.withContext do
  let lctx ← getLCtx
  let some (fs, ρ) := findSemantics lctx | return [g]
  let mut g := g
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, _) := ty.eq? | continue
    unless lhs.isAppOfArity ``Kanon.cancellable 2 do continue
    let a := lhs.appArg!
    let some wt := lctx.findDecl? fun d' =>
        if d'.type.isAppOfArity ``Kanon.Term.WT 1 && d'.type.appArg! == a then some d'.toExpr
        else none
      | continue
    try
      let pf ← mkAppOptM ``cancellable_den
        #[some fs, some ρ, none, none, none, some wt, some d.toExpr]
      let (_, g') ← (← g.assert `hcan (← inferType pf) pf).intro1P
      g := g'
    catch _ => pure ()
  return [g]

/-- An addition that cannot wrap around, by the bounds on its operands, may be
checked unsigned. -/
theorem Refines.add_no_wrap {FS : FloatSem} {c : Checked} {a b : Term} {t : Ty} :
    Refines FS (.mk (.Binop (.Add c) a b) t) (.mk (.Binop (.Add (no_wrap c a b)) a b) t) := by
  unfold no_wrap
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨_, h⟩ := h
    refine Refines.den (fun w => ?_) (fun w => ?_) (fun n w ht ρ x e => ?_)
    · have ⟨w1, _, _⟩ := WT_binop.1 w
      simp only [Binop.WT] at w1
      obtain ⟨⟨m, _, _⟩, _, ht⟩ := w1
      exact ⟨m, by simp_all⟩
    · have ⟨w1, wa, wb⟩ := WT_binop.1 w
      exact ⟨WT_binop.2 ⟨by simpa [Binop.WT] using w1, wa, wb⟩, rfl⟩
    · have ⟨w1, wa, wb⟩ := WT_binop.1 w
      simp only [Binop.WT, Term.ty_mk] at w1 ht
      obtain ⟨⟨_, _, ha⟩, hb, htt⟩ := w1
      rcases a with ⟨ka, Ta⟩
      rcases b with ⟨kb, Tb⟩
      simp only [Term.ty_mk] at ha hb htt
      subst htt; subst hb
      subst ht
      simp only [Ty.sort_eq] at *
      simp only [Lib.den] at e ⊢
      cases ea : Lib.den FS ρ n (Term.mk ka (.TBitVector n)) <;>
        cases eb : Lib.den FS ρ n (Term.mk kb (.TBitVector n)) <;> rw [ea, eb] at e <;>
        simp only [ckOp, reduceCtorEq] at e ⊢
      rename_i xa xb
      have la := den_le_unsigned_ub wa xa ea
      have lb := den_le_unsigned_ub wb xb eb
      simp only [size_eq, Term.ty_mk, size_of_ty_bitVector, zshiftl, Int.one_mul] at h
      have hn : ((2 ^ n : Nat) : Int) = (2 : Int) ^ ((n : Int)).toNat := by simp
      have hov : xa.uaddOverflow xb = false := uadd_ok.2 (by omega)
      simp only [hov, Bool.and_false, Bool.or_false] at e ⊢
      exact e
  · exact Sem.Refines.refl

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

/-! ## Facts for `omega` -/

theorem toInt_neg_cases {w : Nat} (x : BitVec w) :
    (-x).toInt = -x.toInt ∨ ((-x).toInt = x.toInt ∧ x.toInt = -2 ^ (w - 1)) := by
  rw [BitVec.toInt_neg_eq_ite]
  split
  · next h => subst h; rcases Nat.eq_zero_or_pos w with rfl | hw <;>
      simp [BitVec.toInt_zero_length, BitVec.toInt_intMin_of_pos, *]
  · exact .inl rfl

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
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem toNat_sub_cases {w : Nat} (x y : BitVec w) :
    ((x - y).toNat : Int) = x.toNat - y.toNat ∨
      ((x - y).toNat : Int) = x.toNat - y.toNat + 2 ^ w := by
  have := x.isLt; have := y.isLt
  have e : ((2 ^ w : Nat) : Int) = 2 ^ w := by push_cast; rfl
  rw [BitVec.toNat_sub]
  by_cases h : y.toNat ≤ x.toNat
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem toNat_bounds {w : Nat} (x : BitVec w) : (x.toNat : Int) < 2 ^ w := by
  have := x.isLt; exact_mod_cast this

theorem toInt_toNat_cases {w : Nat} (x : BitVec w) :
    (2 * (x.toNat : Int) < 2 ^ w ∧ x.toInt = x.toNat) ∨
      (2 ^ w ≤ 2 * (x.toNat : Int) ∧ x.toInt = x.toNat - 2 ^ w) := by
  have e : ((2 ^ w : Nat) : Int) = 2 ^ w := by push_cast; rfl
  rw [BitVec.toInt_eq_toNat_cond, e]; split <;> omega

/-- The powers of two of a width, for `omega`. -/
theorem two_pow_facts (w : Nat) :
    ((2 ^ w : Nat) : Int) = (2 : Int) ^ w ∧ ((2 ^ (w - 1) : Nat) : Int) = (2 : Int) ^ (w - 1) ∧
      ((2 : Int) ^ w = 2 * 2 ^ (w - 1) ∨ w = 0) ∧ (0 : Int) < 2 ^ (w - 1) := by
  refine ⟨by push_cast; rfl, by push_cast; rfl, ?_, Int.pow_pos (by decide)⟩
  rcases Nat.eq_zero_or_pos w with h | h
  · exact .inr h
  · exact .inl (by rw [← Int.pow_succ', Nat.sub_add_cancel h])

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
elab "kanon_cmp_bounds" : tactic => liftMetaTactic fun g => do
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
elab "kanon_pow_facts" : tactic => liftMetaTactic fun g => g.withContext do
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
elab "kanon_gen_values" : tactic => liftMetaTactic fun g => return [← genValues g]

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
elab "kanon_mul_facts" : tactic => liftMetaTactic fun g => do
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
elab "kanon_clear_flags" : tactic => liftMetaTactic fun g => g.withContext do
  let mut g := g
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let .forallE _ dom _ _ := ty then
      if let some (_, lhs, _) := dom.eq? then
        if lhs.isAppOfArity ``Kanon.Checked.signed 1 || lhs.isAppOfArity ``Kanon.Checked.unsigned 1 then
          g ← g.clear d.fvarId
  return [g]

/-! ## Tactics -/

/-- `kanon_facts`, keeping the literals as values (`BitVec.ofInt n z`). -/
macro "kanon_cmp_facts" : tactic => `(tactic| (
  (try simp [WT_binop, WT_unop, WT_triop, Binop.WT, Unop.WT, Triop.WT, bv_zero, bv_one,
    mk_masked, mk_bv, -bv_of_lit_bv, -bv_of_lit_bv', -to_z_mk] at *)
  (try kanon_split)
  (try kanon_destruct_tys)
  (try simp only [Term.ty_mk] at *)
  (try subst_vars)
  (try simp only [Ty.TBitVector.injEq, Ty.TLoc.injEq] at *)
  (try subst_vars)
  (try simp [WT_binop, WT_unop, WT_triop, Binop.WT, Unop.WT, Triop.WT, bv_zero, bv_one,
    mk_masked, mk_bv, -bv_of_lit_bv, -bv_of_lit_bv', -to_z_mk] at *)
  (try kanon_split)
  (try subst_vars)))

/-- The value half of `Refines.denB`, reduced to facts on the values of the
atoms, with the literals as variables. -/
macro "kanon_cmp_sem" : tactic => `(tactic| (
  intro w ρ x h
  have w' := w
  kanon_cmp_facts
  kanon_nat_widths
  kanon_lits
  simp only [denB_of_bool, Int.natCast_pos, Int.toNat_natCast, BitVec.ofInt_ofNat] at *
  simp (disch := assumption) only [ite_eq_left, sign_bit_eq] at *
  kanon_ub_facts
  kanon_cancel_facts
  kanon_cases
  all_goals kanon_bool_vars
  all_goals (try simp only [Option.some.injEq, forall_eq, forall_eq'] at *)
  all_goals (try (simp [ckOp] at h; done))
  all_goals (try (repeat' split at h))
  all_goals (try simp only [sub_overflows_mk (hn := by assumption),
    add_overflows_mk (hn := by assumption), mul_overflows_mk (hn := by assumption),
    is_int_min_mk' (hn := by assumption), is_min_of_mk (hn := by assumption),
    is_max_of_mk (hn := by assumption)] at *)))

/-- Reduces the goals left by `kanon_cmp_sem` to facts on the integer values of
the atoms. -/
macro "kanon_cmp_pre" : tactic => `(tactic| (
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
  all_goals kanon_split
  all_goals kanon_ovf_eqs
  all_goals (try simp only [sadd_ok, ssub_ok, smul_ok, uadd_ok, usub_ok, umul_ok] at *)
  all_goals (try simp only [BitVec.saddOverflow, BitVec.ssubOverflow, BitVec.smulOverflow,
    BitVec.uaddOverflow, BitVec.usubOverflow, BitVec.umulOverflow, decide_eq_true_eq,
    Bool.or_eq_true] at *)
  all_goals kanon_split
  all_goals kanon_clear_flags
  all_goals kanon_mul_facts
  all_goals kanon_cmp_bounds
  all_goals (try push_cast at *)))

/-- Closes the goals left by `kanon_cmp_sem`, by reasoning on the integer values
of the atoms. -/
macro "kanon_cmp_omega" : tactic => `(tactic| (
  kanon_cmp_pre
  all_goals kanon_pow_facts
  all_goals kanon_gen_values
  all_goals omega))

/-- Proves the statement of an alternative of `bv_lt` or `bv_leq`, as far as
it can. -/
macro "kanon_cmp" : tactic => `(tactic| (
  kanon_rule_core
  all_goals first
    | (kanon_wt_bv; done)
    | (kanon_cmp_sem
       all_goals (try (kanon_cmp_omega; done)))))

/-- `kanon_cmp`, with lemmas for the value goals that `omega` does not close. -/
syntax "kanon_cmp_using " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| kanon_cmp_using [$ls,*]) => `(tactic| (
      kanon_rule_core
      all_goals first
        | (kanon_wt_bv; done)
        | (kanon_cmp_sem
           all_goals (try (simp_all [$ls,*]; done))
           all_goals (try (kanon_cmp_omega; done)))))

attribute [kanon_tactic "kanon_cmp"] bv_lt.spec bv_leq.spec

end Kanon.Lib
