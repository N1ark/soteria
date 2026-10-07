import BitvecMod.Proofs.ArithLib
import BitvecMod.Statements.Bool.eq

/-!
# The proofs of the arms `r_msb` and `r_mul_const` of `Bool.eq`

`r_msb` compares the low bits below the bound on the most significant bits;
`r_mul_const` characterizes `k = c * x`, without overflow, by the quotient `k / c`.
-/

namespace BitvecMod

namespace BoolEq
open Arith

theorem eq_iff_extract_low {n k : Nat} {x y : BitVec n} (hx : (x.toNat : Int) < 2 ^ k)
    (hy : (y.toNat : Int) < 2 ^ k) : x = y ↔ x.extractLsb' 0 k = y.extractLsb' 0 k := by
  have e : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by push_cast; rfl
  rw [← BitVec.toNat_inj, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, Nat.shiftRight_zero, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem msb_lift {x : Nat} {p q : Int} (h : (x : Int) < 2 ^ (p + 1).toNat) (hpq : p + 1 ≤ q) :
    (x : Int) < 2 ^ q.toNat :=
  Int.lt_of_lt_of_le h (pow_le_pow_int (by omega))

variable {n : Nat}

theorem toInt_eq_iff_ofInt {x : BitVec n} {q : Int} (h0 : 0 < n)
    (hr : -2 ^ (n - 1) ≤ q ∧ q < 2 ^ (n - 1)) : x.toInt = q ↔ x = BitVec.ofInt n q := by
  constructor
  · intro h; rw [← BitVec.toInt_inj, BitVec.toInt_ofInt_eq_self h0 hr.1 hr.2, h]
  · intro h; rw [h, BitVec.toInt_ofInt_eq_self h0 hr.1 hr.2]

theorem mul_eq_s (k c x : BitVec n) (hov : c.smulOverflow x = false) :
    (k = c * x) ↔
      (if c.toInt = 0 then k.toInt = 0
       else if k.toInt = 0 then x = 0#n
       else if c.toInt ∣ k.toInt then
         ((-2 ^ (n - 1) ≤ k.toInt.tdiv c.toInt ∧ k.toInt.tdiv c.toInt < 2 ^ (n - 1)) ∧
           x = BitVec.ofInt n (k.toInt.tdiv c.toInt))
       else False) := by
  rw [← BitVec.toInt_inj, toInt_mul_ok hov]
  have bx := toInt_bounds x
  by_cases hc : c.toInt = 0
  · simp only [hc, ↓reduceIte, Int.zero_mul]
  simp only [hc, ↓reduceIte]
  by_cases hk : k.toInt = 0
  · simp only [hk, ↓reduceIte]
    rw [← BitVec.toInt_inj, BitVec.toInt_zero]
    constructor
    · intro h
      rcases Int.mul_eq_zero.1 h.symm with h | h
      · exact absurd h hc
      · exact h
    · intro h; rw [h, Int.mul_zero]
  simp only [hk, ↓reduceIte]
  by_cases hd : c.toInt ∣ k.toInt
  · simp only [hd, ↓reduceIte]
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; exact absurd (by simp [BitVec.eq_nil c]) hc
      · exact h0
    have hq := Int.mul_tdiv_cancel' hd
    generalize k.toInt.tdiv c.toInt = q at *
    rw [← hq, Int.mul_eq_mul_left_iff hc]
    constructor
    · intro h; subst h
      exact ⟨bx, (toInt_eq_iff_ofInt hn bx).1 rfl⟩
    · rintro ⟨hr, h⟩
      exact ((toInt_eq_iff_ofInt hn hr).2 h).symm
  · simp only [hd, ↓reduceIte, iff_false]
    intro h; exact hd ⟨_, h⟩

theorem mul_eq_u (k c x : BitVec n) (hov : c.umulOverflow x = false) :
    (k = c * x) ↔
      (if (c.toNat : Int) = 0 then (k.toNat : Int) = 0
       else if (k.toNat : Int) = 0 then x = 0#n
       else if (c.toNat : Int) ∣ (k.toNat : Int) then
         ((0 ≤ (k.toNat : Int).tdiv c.toNat ∧ (k.toNat : Int).tdiv c.toNat < 2 ^ n) ∧
           x = BitVec.ofInt n ((k.toNat : Int).tdiv c.toNat))
       else False) := by
  rw [← BitVec.toNat_inj, toNat_mul_ok hov, ← Int.ofNat_inj, Int.natCast_mul]
  have bx := toNat_lt_int x
  by_cases hc : (c.toNat : Int) = 0
  · simp only [hc, ↓reduceIte, Int.zero_mul]
  simp only [hc, ↓reduceIte]
  by_cases hk : (k.toNat : Int) = 0
  · simp only [hk, ↓reduceIte]
    rw [← BitVec.toNat_inj, BitVec.toNat_zero, ← Int.ofNat_inj]
    constructor
    · intro h
      rcases Int.mul_eq_zero.1 h.symm with h | h
      · exact absurd h hc
      · exact h
    · intro h; rw [h, Int.natCast_zero, Int.mul_zero]
  simp only [hk, ↓reduceIte]
  by_cases hd : (c.toNat : Int) ∣ (k.toNat : Int)
  · simp only [hd, ↓reduceIte]
    have hq := Int.mul_tdiv_cancel' hd
    generalize (k.toNat : Int).tdiv c.toNat = q at *
    rw [← hq, Int.mul_eq_mul_left_iff hc]
    have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
    constructor
    · intro h; subst h
      refine ⟨bx, ?_⟩
      rw [← BitVec.toNat_inj, BitVec.toNat_ofInt, e, Int.emod_eq_of_lt bx.1 bx.2, Int.toNat_natCast]
    · rintro ⟨hr, h⟩
      rw [h, BitVec.toNat_ofInt, e, Int.emod_eq_of_lt hr.1 hr.2, Int.toNat_of_nonneg hr.1]
  · simp only [hd, ↓reduceIte, iff_false]
    intro h; exact hd ⟨_, h⟩

theorem toNat_ofInt_lit {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ n) :
    ((BitVec.ofInt n z).toNat : Int) = z :=
  (lit_facts n z).1 h0 h1

theorem ofInt_ne_zero {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ n) (hz : z ≠ 0) :
    BitVec.ofInt n z ≠ 0#n := by
  intro h
  have := toNat_ofInt_lit h0 h1
  rw [h, BitVec.toNat_zero] at this
  omega

theorem toNat_dvd_iff {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : a.toNat ∣ b.toNat ↔ a ∣ b := by
  rw [← Int.natCast_dvd_natCast, Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb]

end BoolEq

section
variable {D : Kanon.Dom} [Values D]

theorem BoolEq.ofBV_ite_eq {n : Nat} {p : Prop} [Decidable p] {v : BitVec n} {w1 : D.Val} :
    ofBV n (if p then none else some v) = some w1 ↔ ¬p ∧ bv n v = w1 := by
  split <;> simp_all [ofBV]

theorem BoolEq.bv_inj {n : Nat} {a b : BitVec n} : (bv (D := D) n a = bv n b) ↔ a = b := by
  simp only [bv, Kanon.Embed.inj_eq_iff, Sigma.mk.injEq, heq_eq_eq, true_and]

end

@[kanon_arm] theorem Bool.eq.r_msb.main.proof : Bool.eq.r_msb.main.Stmt := by
  (try intro _)
  intros
  kanon_rule_lift
  all_goals (try simp only [Kanon.Embed.proj_eq_some_iff] at *)
  all_goals kanon_on_refines (
    (try dsimp only)
    bv_split_ifs
    all_goals (try kanon_lift_body)
    all_goals (try simp only [kanon_spec, kanon_body])
    all_goals (try first
      | kanon_refl
      | (kanon_comm; done)))
  all_goals kanon_on_refines (
    refine Kanon.Sem.Refines.intro ?_ ?_
    · bv_arith_wt
    bv_arith_sem_core)
  all_goals (try (repeat' (first
    | (simp only [BitvecMod.ckOp_some, BitvecMod.ckOp_none_l, BitvecMod.ckOp_none_r,
        BitvecMod.binOp_some, BitvecMod.binOp_none_l, BitvecMod.binOp_none_r,
        BitvecMod.negOp_some, BitvecMod.negOp_none, Option.some.injEq, reduceCtorEq, Option.map_none, Option.map_some, BitvecMod.binB_some, BitvecMod.binB_none_l, BitvecMod.binB_none_r, BitvecMod.ofB_none, BitvecMod.ofB_some] at e)
    | split at e)))
  all_goals (try subst e)
  all_goals (try bv_arith_lit_ops)
  all_goals (refine ⟨_, _, rfl, rfl, ?_⟩)
  all_goals (simp only [Kanon.Embed.inj_eq_iff, Sigma.mk.injEq, heq_eq_eq, true_and])
  all_goals (rw [decide_eq_decide]; apply BoolEq.eq_iff_extract_low
    <;> exact BoolEq.msb_lift (by assumption) (by omega))

@[kanon_arm] theorem Bool.eq.r_mul_const.main.proof : Bool.eq.r_mul_const.main.Stmt := by
  (try intro _)
  intros
  kanon_rule_lift
  all_goals (try simp only [Kanon.Embed.proj_eq_some_iff] at *)
  all_goals kanon_on_refines (
    (try dsimp only)
    bv_split_ifs
    all_goals (try kanon_lift_body)
    all_goals (try simp only [kanon_spec, kanon_body])
    all_goals (try first
      | kanon_refl
      | (kanon_comm; done)))
  all_goals kanon_on_refines (
    refine Kanon.Sem.Refines.intro ?_ ?_
    · bv_arith_wt
    bv_arith_sem_core)
  all_goals (try (repeat' (first
    | (simp only [BitvecMod.ckOp_some, BitvecMod.ckOp_none_l, BitvecMod.ckOp_none_r,
        BitvecMod.binOp_some, BitvecMod.binOp_none_l, BitvecMod.binOp_none_r,
        BitvecMod.negOp_some, BitvecMod.negOp_none, Option.some.injEq, reduceCtorEq, Option.map_none, Option.map_some, BitvecMod.binB_some, BitvecMod.binB_none_l, BitvecMod.binB_none_r, BitvecMod.ofB_none, BitvecMod.ofB_some] at e)
    | split at e)))
  all_goals (try subst e)
  all_goals (try bv_arith_lit_ops)
  all_goals (try bv_arith_bools)
  all_goals (try simp_all)
  all_goals (try simp only [BoolEq.ofBV_ite_eq] at *)
  all_goals first
    | obtain ⟨hov, rfl⟩ := ‹¬_ ∧ bv _ _ = _›
    | subst ‹bv _ _ = _›
  all_goals (simp only [BoolEq.bv_inj])
  all_goals (try simp only [Bool.not_eq_true, not_or] at hov)
  all_goals (try first
    | rw [BoolEq.mul_eq_u _ _ _ (by first | exact hov | exact hov.2)]
    | rw [BoolEq.mul_eq_s _ _ _ (by first | exact hov | exact hov.1)])
  all_goals (try simp (disch := assumption) only [BoolEq.toNat_ofInt_lit] at *)
  all_goals (try simp only [BitVec.toInt_ofInt, BitVec.toNat_zero, Int.natCast_zero] at *)
  all_goals (simp_all [BoolEq.ofInt_ne_zero, Prim.divisible, Prim.tdiv, BoolEq.toNat_dvd_iff])
  all_goals (intros; omega)

end BitvecMod
