import Bvr.Lib.Compare

/-! Addition, subtraction, multiplication and division, proved per alternative. -/

namespace Bvr

open Classical Lib

theorem factor_ok {n : Nat} {a b x y : BitVec n} (hab : a.toNat ≠ 0 ∨ b.toNat ≠ 0)
    (hd : a.toNat ∣ b.toNat) (h1 : a.umulOverflow x = false) (h2 : b.umulOverflow y = false)
    (h3 : (a * x).uaddOverflow (b * y) = false) :
    ckOp ⟨false, true⟩ BitVec.smulOverflow BitVec.umulOverflow (· * ·) (some a)
      (ckOp ⟨false, true⟩ BitVec.saddOverflow BitVec.uaddOverflow (· + ·) (some x)
        (if (b.smtUDiv a).umulOverflow y = true then none else some (b.smtUDiv a * y))) =
      some (a * x + b * y) := by
  have ha : a.toNat ≠ 0 := fun h => by
    rw [h] at hd; have := Nat.eq_zero_of_zero_dvd hd; omega
  obtain ⟨q, hq⟩ := hd
  have hc : (b.smtUDiv a).toNat = q := by
    rw [smtUDiv_toNat ha, hq, Nat.mul_div_cancel_left _ (by omega)]
  have e1 := toNat_mul_ok h1
  have e2 := toNat_mul_ok h2
  rw [uadd_ok, e1, e2] at h3
  rw [umul_ok] at h1 h2
  have hA : 1 ≤ a.toNat := by omega
  have l1 : q * y.toNat ≤ b.toNat * y.toNat := by
    rw [hq, Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ hA
  have l2 : x.toNat ≤ a.toNat * x.toNat := Nat.le_mul_of_pos_left _ hA
  have o1 : (b.smtUDiv a).umulOverflow y = false := by rw [umul_ok, hc]; omega
  have e3 := toNat_mul_ok o1
  have o2 : x.uaddOverflow (b.smtUDiv a * y) = false := by rw [uadd_ok, e3, hc]; omega
  have e4 := toNat_add_ok o2
  have hs : a.toNat * (x.toNat + q * y.toNat) = a.toNat * x.toNat + b.toNat * y.toNat := by
    rw [hq, Nat.mul_add, Nat.mul_assoc]
  have o3 : a.umulOverflow (x + b.smtUDiv a * y) = false := by
    rw [umul_ok, e4, e3, hc, hs]; omega
  simp only [o1, o2, o3, ckOp, Bool.false_eq_true, ite_false, Bool.false_and, Bool.true_and,
    Bool.false_or, Option.some.injEq]
  apply BitVec.eq_of_toNat_eq
  rw [toNat_mul_ok o3, e4, e3, hc, hs, toNat_add_ok (by rw [uadd_ok, e1, e2]; omega), e1, e2]

theorem factor_ok' {n : Nat} {a b x y : BitVec n} (ha : a.toNat ≠ 0 ∨ b.toNat ≠ 0)
    (hd : a.toNat ∣ b.toNat)
    (h1 : a.umulOverflow x = false) (h2 : b.umulOverflow y = false)
    (h3 : (b * y).uaddOverflow (a * x) = false) :
    ckOp ⟨false, true⟩ BitVec.smulOverflow BitVec.umulOverflow (· * ·) (some a)
      (ckOp ⟨false, true⟩ BitVec.saddOverflow BitVec.uaddOverflow (· + ·) (some x)
        (if (b.smtUDiv a).umulOverflow y = true then none else some (b.smtUDiv a * y))) =
      some (b * y + a * x) := by
  rw [BitVec.add_comm]
  exact factor_ok ha hd h1 h2 (by rw [uadd_ok] at *; omega)

theorem umul_add_ok {n : Nat} {a x y : BitVec n} (h1 : a.umulOverflow x = false)
    (h2 : a.umulOverflow y = false) (h3 : (a * x).uaddOverflow (a * y) = false) :
    a.umulOverflow (x + y) = false := by
  rw [uadd_ok, toNat_mul_ok h1, toNat_mul_ok h2, ← Nat.mul_add] at h3
  rw [umul_ok, BitVec.toNat_add]
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.mod_le _ _)) h3

theorem mul_div_ok {w : Nat} {n d x : BitVec w} (hd0 : d.toNat ≠ 0) (hd : d.toNat ∣ n.toNat)
    (h : n.umulOverflow x = false) :
    x.umulOverflow (n.smtUDiv d) = false ∧ x * n.smtUDiv d = (n * x).smtUDiv d := by
  obtain ⟨q, hq⟩ := hd
  have hc : (n.smtUDiv d).toNat = q := by
    rw [smtUDiv_toNat hd0, hq, Nat.mul_div_cancel_left _ (by omega)]
  have e := toNat_mul_ok h
  rw [umul_ok] at h
  have l : x.toNat * q ≤ n.toNat * x.toNat := by
    rw [hq, Nat.mul_comm, Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
  have o : x.umulOverflow (n.smtUDiv d) = false := by rw [umul_ok, hc]; omega
  refine ⟨o, BitVec.eq_of_toNat_eq ?_⟩
  rw [toNat_mul_ok o, hc, smtUDiv_toNat hd0, e, hq, Nat.mul_assoc,
    Nat.mul_div_cancel_left _ (by omega), Nat.mul_comm]

theorem div_mul_ok {w : Nat} {n d x : BitVec w} (hn0 : n.toNat ≠ 0) (hd : n.toNat ∣ d.toNat)
    (h : n.umulOverflow x = false) : x.smtUDiv (d.smtUDiv n) = (n * x).smtUDiv d := by
  obtain ⟨q, hq⟩ := hd
  have hc : (d.smtUDiv n).toNat = q := by
    rw [smtUDiv_toNat hn0, hq, Nat.mul_div_cancel_left _ (by omega)]
  by_cases hq0 : q = 0
  · have h1 : d.smtUDiv n = 0#w := BitVec.eq_of_toNat_eq (by simp [hc, hq0])
    have h2 : d = 0#w := BitVec.eq_of_toNat_eq (by simp [hq, hq0])
    rw [h1, h2]; simp [BitVec.smtUDiv_eq]
  · have e := toNat_mul_ok h
    apply BitVec.eq_of_toNat_eq
    have hd0 : d.toNat ≠ 0 := by rw [hq]; exact Nat.mul_ne_zero hn0 hq0
    rw [smtUDiv_toNat (b := d.smtUDiv n) (by omega), smtUDiv_toNat (a := n * x) hd0, hc, e, hq,
      Nat.mul_div_mul_left _ _ (by omega)]

theorem div_div_ok {w : Nat} {a b x : BitVec w} (ha : a.toNat ≠ 0)
    (h : a.umulOverflow b = false) : (x.smtUDiv a).smtUDiv b = x.smtUDiv (a * b) := by
  have e := toNat_mul_ok h
  by_cases hb : b.toNat = 0
  · have h0 : b = 0#w := BitVec.eq_of_toNat_eq (by simp [hb])
    subst h0; simp [BitVec.smtUDiv_eq]
  · have hab : (a * b).toNat ≠ 0 := by rw [e]; exact Nat.mul_ne_zero ha hb
    apply BitVec.eq_of_toNat_eq
    rw [smtUDiv_toNat hb, smtUDiv_toNat ha, smtUDiv_toNat hab, e, Nat.div_div_eq_div_mul]

/-- Division of a zero-extended value by a constant that fits in the value. -/
theorem zext_div_ok {m n : Nat} (hmn : m ≤ n) (x : BitVec m) {z : Int} (h0 : 0 ≤ z)
    (hz : 0 < z ∧ z < 2 ^ m ∨ m = n) (hzn : z < 2 ^ n) :
    (x.setWidth n).smtUDiv (BitVec.ofInt n z) = (x.smtUDiv (BitVec.ofInt m z)).setWidth n := by
  rcases hz with ⟨hz0, hzm⟩ | rfl
  · have hm : (BitVec.ofInt m z).toNat ≠ 0 := by rw [toNat_ofInt_of_lt h0 hzm]; omega
    have hn : (BitVec.ofInt n z).toNat ≠ 0 := by rw [toNat_ofInt_of_lt h0 hzn]; omega
    have := x.isLt
    have hp : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hmn
    apply BitVec.eq_of_toNat_eq
    rw [smtUDiv_toNat hn, BitVec.toNat_setWidth, BitVec.toNat_setWidth, smtUDiv_toNat hm,
      toNat_ofInt_of_lt h0 hzm, toNat_ofInt_of_lt h0 hzn, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by have := Nat.div_le_self x.toNat z.toNat; omega)]
  · simp

@[bvr_arm] theorem bv_add.r_default.main.proof : bv_add.r_default.main.Stmt := by
  intro FS O hO checked v1 v2
  simp only [bv_add.spec, mk_commut_binop]
  refine Refines.trans Refines.add_no_wrap ?_
  split
  · exact Refines.refl
  · exact Refines.comm (by simp [Binop.Comm]) (fun _ => rfl)

@[bvr_arm] theorem bv_add.r_factor.main.proof : bv_add.r_factor.main.Stmt := by
  bvr_rule_sem
  all_goals bvr_split
  all_goals subst_vars
  all_goals first
    | exact umul_add_ok ‹_› ‹_› ‹_›
    | exact BitVec.mul_add ..

@[bvr_arm] theorem bv_add.r_factor_const.main.proof : bv_add.r_factor_const.main.Stmt := by
  bvr_rule_sem
  all_goals bvr_split
  all_goals subst_vars
  all_goals first
    | exact factor_ok (by bvr_nat) (by bvr_nat) ‹_› ‹_› ‹_›
    | exact factor_ok' (by bvr_nat) (by bvr_nat) ‹_› ‹_› ‹_›

@[bvr_arm] theorem bv_mul.r_neg.main.proof : bv_mul.r_neg.main.Stmt := by
  bvr_rule_sem
  all_goals simp_all [smulOverflow_neg_swap]

@[bvr_arm] theorem bv_mul.r_mul_const.main.proof : bv_mul.r_mul_const.main.Stmt := by
  bvr_rule_sem
  all_goals simp_all [BitVec.mul_assoc, umul_assoc_ok, smul_assoc_ok]

@[bvr_arm] theorem bv_div.r_mul_div.main.proof : bv_div.r_mul_div.main.Stmt := by
  bvr_rule_sem
  all_goals bvr_split
  all_goals subst_vars
  all_goals first
    | exact (mul_div_ok (by bvr_nat) (by bvr_nat) ‹_›).1
    | exact (mul_div_ok (by bvr_nat) (by bvr_nat) ‹_›).2

@[bvr_arm] theorem bv_div.r_div_mul.main.proof : bv_div.r_div_mul.main.Stmt := by
  bvr_rule_sem
  all_goals bvr_split
  all_goals subst_vars
  all_goals exact div_mul_ok (by bvr_nat) (by bvr_nat) ‹_›

@[bvr_arm] theorem bv_div.r_div_div.main.proof : bv_div.r_div_div.main.Stmt := by
  bvr_rule_sem
  all_goals bvr_split
  all_goals subst_vars
  all_goals exact (div_div_ok (by bvr_nat) ‹_›).symm

@[bvr_arm] theorem bv_div.r_zext.main.proof : bv_div.r_zext.main.Stmt := by
  bvr_rule_sem
  all_goals bvr_split
  all_goals subst_vars
  all_goals
    rw [msb_of_lit, size_of_ty_bitVector] at *
    simp (disch := assumption) only [emod_two_pow_of_lt, Int.max_eq_left] at *
    refine (zext_div_ok (by omega) _ ‹_› ?_ ‹_›).symm
    split at *
    · exact .inl ⟨‹_›, lt_two_pow_log2 ‹_› ‹_›⟩
    · exact .inr (by omega)

end Bvr
