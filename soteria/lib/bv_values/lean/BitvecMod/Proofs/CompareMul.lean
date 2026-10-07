import BitvecMod.Proofs.CompareLib
import KanonBool.Proofs

/-!
# The arms of the comparisons of a product by a constant with a constant

`lt`/`leq` `.r_mul_const` (`x * c1 ⋚ c2`) and `.r_const_mul` (`c2 ⋚ x * c1`), checked in the
signedness of the comparison: the product is exact, so the comparison is one of `x` with the
truncated quotient `c2 / c1`, strict or not depending on the sign of `c1` and on whether `c1`
divides `c2` (the guards of the rules).

The proofs read the value of the left side once (`*_lhs`: the value of `x`, the absence of
overflow, the comparison of bit-vectors), compute that of each branch of the right side, and
close the comparison of integers by `omega` with the facts on truncated division
(`Cmp.cmp_tdiv_facts`, `Cmp.cmp_div_facts`).
-/

noncomputable section

namespace BitvecMod

open Classical Kanon

section
variable {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [Lang S] [KanonBool.Typed S]
  [CoreMod.Typed S] [Typed S]

/-- A literal `c` is in the range of the sort `τ` (the typing of literals). -/
def MulLit (c : Int) (τ : S.Ty) : Prop :=
  ∀ n, τ = sort (.TBitVector n) ∨ τ = sort (.TLoc n) → 0 ≤ c ∧ c < 2 ^ n.toNat

set_option hygiene false in
/-- The value of the left side of a comparison of `x * c1` with `c2`, from that of `x`. -/
macro "mul_lhs_tac" : tactic => `(tactic| (
  have hw : Values.width (D := S.toDom) (S.ty x) = n := by
    rw [hx]; simpa using width_sort (S := S) ρ (.inl rfl) hN
  rcases ev_cases (ρ := ρ) wx hx with hv | ⟨_, hv, -, xv, rfl⟩
  · simp [ev_mk, Node.eval, Node.map, hv] at e
  · replace hv : S.ev ρ x = some (bv n xv) := hv
    simp only [ev_mk, Node.eval, Node.map, hv] at e
    rw [hw] at e
    simp only [asBV_bv, ofBV_some] at e
    rw [ckOp_some] at e
    refine ⟨xv, hv, ?_⟩
    cases hov : (ck.signed && xv.smulOverflow (BitVec.ofInt n c1) ||
        ck.unsigned && xv.umulOverflow (BitVec.ofInt n c1))
    · rw [hov] at e
      simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff] at hov
      simp only [Bool.false_eq_true, ↓reduceIte, ofBV_some, withW_bv, asBV_bv, binB_some,
        ofB_some, Option.some.injEq] at e
      exact ⟨fun hs => hov.1.resolve_left (by simp [hs]),
        fun hu => hov.2.resolve_left (by simp [hu]), e.symm⟩
    · rw [hov] at e
      simp at e))

omit [KanonBool.Typed S] [CoreMod.Typed S] [Typed S] in
/-- The typing of `lt s (x * c1) c2`. -/
theorem lt_mc_wt {s : Bool} {ck : CoreMod.Checked} {x : S.Term} {c1 c2 : Int}
    {t5 t7 t10 : S.Ty}
    (w : S.WT (mk (.Lt s (mk (.Mul ck x (mk (.BitVec c1) t5)) t7) (mk (.BitVec c2) t10))
      (KanonBool.sort .TBool))) :
    ∃ N : Int, 0 < N ∧ S.ty x = sort (.TBitVector N) ∧ t5 = S.ty x ∧ t7 = S.ty x ∧
      t10 = S.ty x ∧ S.WT x ∧ MulLit c1 (S.ty x) ∧ MulLit c2 (S.ty x) := by
  simp only [WT_mk, Node.wt, Node.All, ty_mk, bv_wf] at w
  obtain ⟨⟨-, h10, -⟩, ⟨⟨⟨N, hN, hx⟩, h5, h7⟩, wx, ⟨-, r1⟩, -⟩, ⟨-, r2⟩, -⟩ := w
  subst h10 h7 h5
  exact ⟨N, hN, hx, rfl, rfl, rfl, wx, r1, r2⟩

omit [KanonBool.Typed S] [CoreMod.Typed S] in
/-- The value of `lt s (x * c1) c2`: that of `x`, a bit-vector of the width of the sorts, whose
product by `c1` does not overflow in the checked signedness. -/
theorem lt_mc_lhs {ρ : S.Env} {v : S.Val} {s : Bool} {ck : CoreMod.Checked} {x : S.Term}
    {c1 c2 : Int} {t5 t7 t10 : S.Ty}
    (w : S.WT (mk (.Lt s (mk (.Mul ck x (mk (.BitVec c1) t5)) t7) (mk (.BitVec c2) t10))
      (KanonBool.sort .TBool)))
    (e : S.ev ρ (mk (.Lt s (mk (.Mul ck x (mk (.BitVec c1) t5)) t7) (mk (.BitVec c2) t10))
      (KanonBool.sort .TBool)) = some v) :
    ∃ n : Nat, 0 < n ∧ S.ty x = sort (.TBitVector n) ∧ t5 = S.ty x ∧ t7 = S.ty x ∧
      t10 = S.ty x ∧ 0 ≤ c1 ∧ c1 < 2 ^ n ∧ 0 ≤ c2 ∧ c2 < 2 ^ n ∧
      ∃ xv : BitVec n, S.ev ρ x = some (bv _ xv) ∧
        (ck.signed = true → xv.smulOverflow (BitVec.ofInt _ c1) = false) ∧
        (ck.unsigned = true → xv.umulOverflow (BitVec.ofInt _ c1) = false) ∧
        v = KanonBool.Values.vbool.inj
          (if s then (xv * BitVec.ofInt _ c1).slt (BitVec.ofInt _ c2)
          else (xv * BitVec.ofInt _ c1).ult (BitVec.ofInt _ c2)) := by
  obtain ⟨N, hN, hx, rfl, rfl, rfl, wx, r1, r2⟩ := lt_mc_wt w
  obtain ⟨hc1a, hc1b⟩ := r1 N (.inl hx)
  obtain ⟨hc2a, hc2b⟩ := r2 N (.inl hx)
  obtain ⟨n, rfl⟩ : ∃ n : Nat, N = n := ⟨N.toNat, by omega⟩
  simp only [Int.toNat_natCast] at hc1b hc2b
  refine ⟨n, by omega, hx, rfl, rfl, rfl, hc1a, hc1b, hc2a, hc2b, ?_⟩
  mul_lhs_tac

omit [KanonBool.Typed S] [CoreMod.Typed S] [Typed S] in
/-- The typing of `lt s c2 (x * c1)`. -/
theorem lt_cm_wt {s : Bool} {ck : CoreMod.Checked} {x : S.Term} {c1 c2 : Int}
    {t2 t7 t9 : S.Ty}
    (w : S.WT (mk (.Lt s (mk (.BitVec c2) t2) (mk (.Mul ck x (mk (.BitVec c1) t7)) t9))
      (KanonBool.sort .TBool))) :
    ∃ N : Int, 0 < N ∧ S.ty x = sort (.TBitVector N) ∧ t2 = S.ty x ∧ t7 = S.ty x ∧
      t9 = S.ty x ∧ S.WT x ∧ MulLit c1 (S.ty x) ∧ MulLit c2 (S.ty x) := by
  simp only [WT_mk, Node.wt, Node.All, ty_mk, bv_wf] at w
  obtain ⟨⟨-, h9, -⟩, ⟨⟨-, r2⟩, -⟩, ⟨⟨⟨N, hN, hx⟩, h7, h9'⟩, wx, ⟨-, r1⟩, -⟩⟩ := w
  subst h9' h7 h9
  exact ⟨N, hN, hx, rfl, rfl, rfl, wx, r1, r2⟩

omit [KanonBool.Typed S] [CoreMod.Typed S] in
/-- The value of `lt s c2 (x * c1)`, as `lt_cm_wt` for `x * c1 < c2`. -/
theorem lt_cm_lhs {ρ : S.Env} {v : S.Val} {s : Bool} {ck : CoreMod.Checked} {x : S.Term}
    {c1 c2 : Int} {t2 t7 t9 : S.Ty}
    (w : S.WT (mk (.Lt s (mk (.BitVec c2) t2) (mk (.Mul ck x (mk (.BitVec c1) t7)) t9))
      (KanonBool.sort .TBool)))
    (e : S.ev ρ (mk (.Lt s (mk (.BitVec c2) t2) (mk (.Mul ck x (mk (.BitVec c1) t7)) t9))
      (KanonBool.sort .TBool)) = some v) :
    ∃ n : Nat, 0 < n ∧ S.ty x = sort (.TBitVector n) ∧ t2 = S.ty x ∧ t7 = S.ty x ∧
      t9 = S.ty x ∧ 0 ≤ c1 ∧ c1 < 2 ^ n ∧ 0 ≤ c2 ∧ c2 < 2 ^ n ∧
      ∃ xv : BitVec n, S.ev ρ x = some (bv _ xv) ∧
        (ck.signed = true → xv.smulOverflow (BitVec.ofInt _ c1) = false) ∧
        (ck.unsigned = true → xv.umulOverflow (BitVec.ofInt _ c1) = false) ∧
        v = KanonBool.Values.vbool.inj
          (if s then (BitVec.ofInt _ c2).slt (xv * BitVec.ofInt _ c1)
          else (BitVec.ofInt _ c2).ult (xv * BitVec.ofInt _ c1)) := by
  obtain ⟨N, hN, hx, rfl, rfl, rfl, wx, r1, r2⟩ := lt_cm_wt w
  obtain ⟨hc1a, hc1b⟩ := r1 N (.inl hx)
  obtain ⟨hc2a, hc2b⟩ := r2 N (.inl hx)
  obtain ⟨n, rfl⟩ : ∃ n : Nat, N = n := ⟨N.toNat, by omega⟩
  simp only [Int.toNat_natCast] at hc1b hc2b
  refine ⟨n, by omega, hx, rfl, rfl, rfl, hc1a, hc1b, hc2a, hc2b, ?_⟩
  mul_lhs_tac

omit [KanonBool.Typed S] [CoreMod.Typed S] [Typed S] in
/-- The typing of `leq s (x * c1) c2`. -/
theorem leq_mc_wt {s : Bool} {ck : CoreMod.Checked} {x : S.Term} {c1 c2 : Int}
    {t5 t7 t10 : S.Ty}
    (w : S.WT (mk (.Leq s (mk (.Mul ck x (mk (.BitVec c1) t5)) t7) (mk (.BitVec c2) t10))
      (KanonBool.sort .TBool))) :
    ∃ N : Int, 0 < N ∧ S.ty x = sort (.TBitVector N) ∧ t5 = S.ty x ∧ t7 = S.ty x ∧
      t10 = S.ty x ∧ S.WT x ∧ MulLit c1 (S.ty x) ∧ MulLit c2 (S.ty x) := by
  simp only [WT_mk, Node.wt, Node.All, ty_mk, bv_wf] at w
  obtain ⟨⟨-, h10, -⟩, ⟨⟨⟨N, hN, hx⟩, h5, h7⟩, wx, ⟨-, r1⟩, -⟩, ⟨-, r2⟩, -⟩ := w
  subst h10 h7 h5
  exact ⟨N, hN, hx, rfl, rfl, rfl, wx, r1, r2⟩

omit [KanonBool.Typed S] [CoreMod.Typed S] in
/-- The value of `leq s (x * c1) c2`: that of `x`, a bit-vector of the width of the sorts, whose
product by `c1` does not overflow in the checked signedness. -/
theorem leq_mc_lhs {ρ : S.Env} {v : S.Val} {s : Bool} {ck : CoreMod.Checked} {x : S.Term}
    {c1 c2 : Int} {t5 t7 t10 : S.Ty}
    (w : S.WT (mk (.Leq s (mk (.Mul ck x (mk (.BitVec c1) t5)) t7) (mk (.BitVec c2) t10))
      (KanonBool.sort .TBool)))
    (e : S.ev ρ (mk (.Leq s (mk (.Mul ck x (mk (.BitVec c1) t5)) t7) (mk (.BitVec c2) t10))
      (KanonBool.sort .TBool)) = some v) :
    ∃ n : Nat, 0 < n ∧ S.ty x = sort (.TBitVector n) ∧ t5 = S.ty x ∧ t7 = S.ty x ∧
      t10 = S.ty x ∧ 0 ≤ c1 ∧ c1 < 2 ^ n ∧ 0 ≤ c2 ∧ c2 < 2 ^ n ∧
      ∃ xv : BitVec n, S.ev ρ x = some (bv _ xv) ∧
        (ck.signed = true → xv.smulOverflow (BitVec.ofInt _ c1) = false) ∧
        (ck.unsigned = true → xv.umulOverflow (BitVec.ofInt _ c1) = false) ∧
        v = KanonBool.Values.vbool.inj
          (if s then (xv * BitVec.ofInt _ c1).sle (BitVec.ofInt _ c2)
          else (xv * BitVec.ofInt _ c1).ule (BitVec.ofInt _ c2)) := by
  obtain ⟨N, hN, hx, rfl, rfl, rfl, wx, r1, r2⟩ := leq_mc_wt w
  obtain ⟨hc1a, hc1b⟩ := r1 N (.inl hx)
  obtain ⟨hc2a, hc2b⟩ := r2 N (.inl hx)
  obtain ⟨n, rfl⟩ : ∃ n : Nat, N = n := ⟨N.toNat, by omega⟩
  simp only [Int.toNat_natCast] at hc1b hc2b
  refine ⟨n, by omega, hx, rfl, rfl, rfl, hc1a, hc1b, hc2a, hc2b, ?_⟩
  mul_lhs_tac

omit [KanonBool.Typed S] [CoreMod.Typed S] [Typed S] in
/-- The typing of `leq s c2 (x * c1)`. -/
theorem leq_cm_wt {s : Bool} {ck : CoreMod.Checked} {x : S.Term} {c1 c2 : Int}
    {t2 t7 t9 : S.Ty}
    (w : S.WT (mk (.Leq s (mk (.BitVec c2) t2) (mk (.Mul ck x (mk (.BitVec c1) t7)) t9))
      (KanonBool.sort .TBool))) :
    ∃ N : Int, 0 < N ∧ S.ty x = sort (.TBitVector N) ∧ t2 = S.ty x ∧ t7 = S.ty x ∧
      t9 = S.ty x ∧ S.WT x ∧ MulLit c1 (S.ty x) ∧ MulLit c2 (S.ty x) := by
  simp only [WT_mk, Node.wt, Node.All, ty_mk, bv_wf] at w
  obtain ⟨⟨-, h9, -⟩, ⟨⟨-, r2⟩, -⟩, ⟨⟨⟨N, hN, hx⟩, h7, h9'⟩, wx, ⟨-, r1⟩, -⟩⟩ := w
  subst h9' h7 h9
  exact ⟨N, hN, hx, rfl, rfl, rfl, wx, r1, r2⟩

omit [KanonBool.Typed S] [CoreMod.Typed S] in
/-- The value of `leq s c2 (x * c1)`, as `leq_cm_wt` for `x * c1 < c2`. -/
theorem leq_cm_lhs {ρ : S.Env} {v : S.Val} {s : Bool} {ck : CoreMod.Checked} {x : S.Term}
    {c1 c2 : Int} {t2 t7 t9 : S.Ty}
    (w : S.WT (mk (.Leq s (mk (.BitVec c2) t2) (mk (.Mul ck x (mk (.BitVec c1) t7)) t9))
      (KanonBool.sort .TBool)))
    (e : S.ev ρ (mk (.Leq s (mk (.BitVec c2) t2) (mk (.Mul ck x (mk (.BitVec c1) t7)) t9))
      (KanonBool.sort .TBool)) = some v) :
    ∃ n : Nat, 0 < n ∧ S.ty x = sort (.TBitVector n) ∧ t2 = S.ty x ∧ t7 = S.ty x ∧
      t9 = S.ty x ∧ 0 ≤ c1 ∧ c1 < 2 ^ n ∧ 0 ≤ c2 ∧ c2 < 2 ^ n ∧
      ∃ xv : BitVec n, S.ev ρ x = some (bv _ xv) ∧
        (ck.signed = true → xv.smulOverflow (BitVec.ofInt _ c1) = false) ∧
        (ck.unsigned = true → xv.umulOverflow (BitVec.ofInt _ c1) = false) ∧
        v = KanonBool.Values.vbool.inj
          (if s then (BitVec.ofInt _ c2).sle (xv * BitVec.ofInt _ c1)
          else (BitVec.ofInt _ c2).ule (xv * BitVec.ofInt _ c1)) := by
  obtain ⟨N, hN, hx, rfl, rfl, rfl, wx, r1, r2⟩ := leq_cm_wt w
  obtain ⟨hc1a, hc1b⟩ := r1 N (.inl hx)
  obtain ⟨hc2a, hc2b⟩ := r2 N (.inl hx)
  obtain ⟨n, rfl⟩ : ∃ n : Nat, N = n := ⟨N.toNat, by omega⟩
  simp only [Int.toNat_natCast] at hc1b hc2b
  refine ⟨n, by omega, hx, rfl, rfl, rfl, hc1a, hc1b, hc2a, hc2b, ?_⟩
  mul_lhs_tac


/-- A non-zero literal in range is a non-zero bit-vector. -/
theorem mul_ofInt_ne_zero {n : Nat} {c : Int} (h0 : 0 ≤ c) (h1 : c < 2 ^ n) (hc : c ≠ 0) :
    (BitVec.ofInt n c).toNat ≠ 0 ∧ (BitVec.ofInt n c).toInt ≠ 0 := by
  have e := toNat_ofInt_of_lt h0 h1
  refine ⟨by omega, fun h => ?_⟩
  have : BitVec.ofInt n c = 0#n := BitVec.eq_of_toInt_eq (by simpa using h)
  rw [this] at e; simp at e; omega

/-- `Cmp.cmp_tdiv_facts` for a positive divisor (fewer cases for `omega`). -/
theorem mul_tdiv_pos (C2 C1 X : Int) (h : 0 < C1) :
    C2 = C2.tdiv C1 * C1 + C2.tmod C1 ∧ (0 ≤ C2 → 0 ≤ C2.tmod C1) ∧ (C2 ≤ 0 → C2.tmod C1 ≤ 0) ∧
    -C1 < C2.tmod C1 ∧ C2.tmod C1 < C1 ∧
    (X ≤ C2.tdiv C1 - 1 → X * C1 ≤ C2.tdiv C1 * C1 - C1) ∧
    (C2.tdiv C1 + 1 ≤ X → C2.tdiv C1 * C1 + C1 ≤ X * C1) ∧
    (X = C2.tdiv C1 → X * C1 = C2.tdiv C1 * C1) := by
  obtain ⟨e, h0, h1, h2, -, h3, h4, h5⟩ := Cmp.cmp_tdiv_facts C2 C1 X (by omega)
  exact ⟨e, h0, h1, (h2 h).1, (h2 h).2, fun hx => (h3 hx).1 h, fun hx => (h4 hx).1 h, h5⟩

/-- `Cmp.cmp_tdiv_facts` for a negative divisor. -/
theorem mul_tdiv_neg (C2 C1 X : Int) (h : C1 < 0) :
    C2 = C2.tdiv C1 * C1 + C2.tmod C1 ∧ (0 ≤ C2 → 0 ≤ C2.tmod C1) ∧ (C2 ≤ 0 → C2.tmod C1 ≤ 0) ∧
    C1 < C2.tmod C1 ∧ C2.tmod C1 < -C1 ∧
    (X ≤ C2.tdiv C1 - 1 → C2.tdiv C1 * C1 - C1 ≤ X * C1) ∧
    (C2.tdiv C1 + 1 ≤ X → X * C1 ≤ C2.tdiv C1 * C1 + C1) ∧
    (X = C2.tdiv C1 → X * C1 = C2.tdiv C1 * C1) := by
  obtain ⟨e, h0, h1, -, h2, h3, h4, h5⟩ := Cmp.cmp_tdiv_facts C2 C1 X (by omega)
  exact ⟨e, h0, h1, (h2 h).1, (h2 h).2, fun hx => (h3 hx).2 h, fun hx => (h4 hx).2 h, h5⟩

/-- Divisibility of literals in range, on their natural numbers. -/
theorem mul_dvd_toNat {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ∣ b ↔ b.toNat % a.toNat = 0 := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  simp only [Int.natCast_dvd_natCast, Int.toNat_natCast, Nat.dvd_iff_mod_eq_zero]

set_option hygiene false in
/-- Closes the comparison of the values of the two sides of a branch, signed: the product and
the quotient as those of the integers, then `omega`. -/
macro "mul_int_signed" : tactic => `(tactic| (
  have hs := hs ‹_›
  obtain ⟨-, hc1⟩ := mul_ofInt_ne_zero (n := n) c1a c1b ‹¬c1 = 0›
  have hb := toInt_bounds xv
  have hd1 : (BitVec.ofInt n c1).toInt = -1 →
      (BitVec.ofInt n c2).toInt.tmod (BitVec.ofInt n c1).toInt = 0 := fun h => by
    rw [h]; exact Int.tmod_eq_zero_of_dvd (Int.neg_dvd.2 (Int.one_dvd _))
  have hm1 : (BitVec.ofInt n c1).toInt = -1 →
      xv.toInt * (BitVec.ofInt n c1).toInt = -xv.toInt := fun h => by rw [h]; omega
  simp only [Int.dvd_iff_tmod_eq_zero, decide_eq_true_eq] at *
  simp only [BitVec.slt, BitVec.sle, toInt_mul_ok hs]
  (try rw [Cmp.cmp_toInt_smtSDiv_facts _ _ hc1 (by omega)])
  first
    | have := mul_tdiv_pos (BitVec.ofInt n c2).toInt (BitVec.ofInt n c1).toInt xv.toInt (by omega)
    | have := mul_tdiv_neg (BitVec.ofInt n c2).toInt (BitVec.ofInt n c1).toInt xv.toInt (by omega)
  simp only [decide_eq_decide, Bool.false_eq, Bool.true_eq, decide_eq_false_iff_not,
    decide_eq_true_eq]
  generalize (BitVec.ofInt n c2).toInt = C2 at *
  generalize (BitVec.ofInt n c1).toInt = C1 at *
  generalize xv.toInt = X at *
  omega))

set_option hygiene false in
/-- `mul_int_signed`, unsigned: on the natural numbers. -/
macro "mul_int_unsigned" : tactic => `(tactic| (
  have hu := hu ‹_›
  obtain ⟨hc1, -⟩ := mul_ofInt_ne_zero (n := n) c1a c1b ‹¬c1 = 0›
  simp only [BitVec.ult, BitVec.ule, toNat_mul_ok hu]
  (try rw [smtUDiv_toNat hc1])
  simp only [toNat_ofInt_of_lt c1a c1b, toNat_ofInt_of_lt c2a c2b, decide_eq_decide, Bool.false_eq,
    Bool.true_eq, decide_eq_false_iff_not, decide_eq_true_eq]
  have := Cmp.cmp_div_facts c2.toNat c1.toNat xv.toNat (by omega)
  simp only [mul_dvd_toNat c1a c2a] at *
  generalize xv.toNat = X at *
  omega))

set_option hygiene false in
/-- A branch of a comparison of `x * c1` with `c2`: the typing, and the values by the lemmas `W`
and `L` of the left side. -/
macro "mul_branch " W:ident L:ident : tactic => `(tactic| (
  refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · obtain ⟨N, hN, hx, rfl, rfl, rfl, wx, r1, r2⟩ := $W w
    have hex : ∃ n, 0 < n ∧ S.ty x = sort (.TBitVector n) := ⟨N, hN, hx⟩
    simp only [WT_mk, Node.wt, Node.All, ty_mk, bv_wf, KanonBool.WT_v_true, KanonBool.WT_v_false,
      KanonBool.v_true, KanonBool.v_false, KanonBool.WT_mk, KanonBool.Node.wt, KanonBool.Node.All,
      KanonBool.ty_mk, hex, wx, and_true, true_and, and_self]
    all_goals ((try constructor) <;> assumption)
  · obtain ⟨n, hn, hx, rfl, rfl, rfl, c1a, c1b, c2a, c2b, xv, hv, hs, hu, rfl⟩ := $L w e
    clear e w
    have hw : Values.width (D := S.toDom) (S.ty x) = n := by
      rw [hx]; simpa using width_sort (S := S) ρ (.inl rfl) (show (0 : Int) < n by omega)
    simp only [ty_mk, show size_of_ty (S.ty x) = n by rw [hx, size_of_ty_TBitVector],
      signed_extract_zero hn, Prim.divisible, decide_eq_true_eq, Bitvec.to_z, Bitvec.is_int_min,
      Bitvec.min_for, z_lsl_one, natCast_sub_one_toNat, ↓reduceIte, true_and,
      Bool.true_and, Bool.and_true, Bool.false_and, Bool.and_eq_true] at *
    (try (obtain rfl : signed = false := by simpa using ‹¬signed = true›))
    simp only [ev_mk, Node.eval, Node.map, hv, KanonBool.ev_v_true, KanonBool.ev_v_false]
    (try rw [hw])
    simp only [asBV_bv, ofBV_some, binOp_some, withW_bv, binB_some, ofB_some, ↓reduceIte,
      Option.some.injEq, Kanon.Embed.inj_eq_iff, Bool.false_eq_true]
    first | mul_int_unsigned | mul_int_signed))

open Lean Elab Tactic in
/-- Forgets the tag of the main goal (`kanon_lift_body` looks for the goal tagged `hl` that it
creates, which the tags of `by_cases` hide). -/
elab "mul_untag" : tactic => do (← getMainGoal).setTag .anonymous

set_option hygiene false in
/-- The lifting of an arm: its guards, the signedness `signed` by cases, the conditionals of its
body split (by cases on their conditions, `cmp_split_ifs`), and the calls of its body as their
specs. -/
macro "mul_lift" : tactic => `(tactic| (
  (try kanon_guards)
  (try kanon_split)
  (try subst_vars)
  (try simp only [kanon_spec, kanon_body])
  (try dsimp only)
  cases signed <;> simp only [Bitvec.checked_has, Bitvec.to_z, ↓reduceIte, Bool.false_eq_true,
    false_and, true_and, and_true] at *
  all_goals cmp_split_ifs
  all_goals (try (mul_untag; kanon_lift_body))
  all_goals (try simp only [kanon_spec, kanon_body])))
end

/-- An arm comparing `x * c1` with `c2` (`W`, `L`: the typing and the value of its left side). -/
macro "mul_arm " W:ident L:ident : tactic => `(tactic| (
  mul_lift
  all_goals first | mul_branch $W $L | (cmp_nonzero; done)))

end BitvecMod
