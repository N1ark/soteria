import BitvecMod.Tactic
import BitvecMod.LitOps

/-!
# The arithmetic of the bitvec module

The lemmas and tactics of the arms of `Bitvec.add`, `sub`, `mul`, `neg`,
`not_`, `and_`, `or_`, `xor`, `of_bool`, `to_bool`, `not_bool` and of the
overflow functions (option B's `Lib/Ovf.lean` and `Lib/Arith.lean`, on the
values of option C):

- the overflow flags of `BitVec` through integers (`sadd_ok`, …), and the
  helpers of the rules on literals in range (`overflows_add`, `fold_checked`,
  …) as operations on their values, at the integer width `w` of a sort
  (`BitVec w.toNat`);
- `bv_arith`, the tactic of the arms of these functions: `bv_auto`'s steps,
  with the value goals closed by these lemmas (`bv_arith_close`).
-/

noncomputable section

namespace BitvecMod.Arith

open Classical Kanon Prim LitOps

set_option linter.unusedSectionVars false

theorem two_pow_pos (n : Nat) : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)


/-- The integer that a bit-vector stands for, in a signedness. -/
abbrev iv (s : Bool) {w : Nat} (x : BitVec w) : Int := if s then x.toInt else x.toNat

theorem zasr_zero (z : Int) : zasr z 0 = z := by simp [zasr]

theorem signed_extract_zero {n : Nat} (hn : 0 < n) (z : Int) :
    signed_extract z 0 (n : Int) = (BitVec.ofInt n z).toInt := by
  have h2 : ((2 : Int) ^ n + 1) / 2 = 2 ^ (n - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Int.pow_succ]; omega
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  simp only [Prim.signed_extract, zasr_zero, Int.toNat_natCast, BitVec.toInt_ofInt, Int.bmod, e, h2]
  split <;> split <;> omega

theorem z_lsl_one (k : Int) : Prim.z_lsl 1 k = 2 ^ k.toNat := by simp [Prim.z_lsl]

/-! ## Integers modulo powers of two -/

theorem ofInt_emod_two_pow (n : Nat) (z : Int) :
    BitVec.ofInt n (z % 2 ^ n) = BitVec.ofInt n z := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]

theorem emod_two_pow_nonneg (z : Int) (n : Nat) : 0 ≤ z % 2 ^ n :=
  Int.emod_nonneg _ (Int.ne_of_gt (Int.pow_pos (by decide)))

theorem emod_two_pow_lt (z : Int) (n : Nat) : z % 2 ^ n < 2 ^ n :=
  Int.emod_lt_of_pos _ (Int.pow_pos (by decide))

theorem toNat_ofInt_of_lt {n : Nat} {k : Int} (h0 : 0 ≤ k) (h1 : k < 2 ^ n) :
    (BitVec.ofInt n k).toNat = k.toNat := by
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt h0 (by push_cast; exact h1)]

theorem emod_two_pow_of_lt {n : Nat} {k : Int} (h0 : 0 ≤ k) (h1 : k < 2 ^ n) :
    k % 2 ^ n = k := Int.emod_eq_of_lt h0 h1

theorem smtUDiv_toNat {n : Nat} {a b : BitVec n} (hb : b.toNat ≠ 0) :
    (a.smtUDiv b).toNat = a.toNat / b.toNat := by
  simp [BitVec.smtUDiv_eq, ← BitVec.toNat_inj, hb]

theorem popcountNat_eq_zero : ∀ {m : Nat}, popcountNat m = 0 → m = 0
  | 0, _ => rfl
  | k + 1, h => by
      rw [popcountNat] at h
      have : (k + 1) / 2 < k + 1 := by omega
      have := popcountNat_eq_zero (m := (k + 1) / 2) (by omega)
      omega

theorem popcountNat_eq_one : ∀ {m : Nat}, popcountNat m = 1 → ∃ j, m = 2 ^ j
  | 0, h => by simp [popcountNat] at h
  | k + 1, h => by
      rw [popcountNat] at h
      have : (k + 1) / 2 < k + 1 := by omega
      by_cases hm : (k + 1) % 2 = 1
      · have := popcountNat_eq_zero (m := (k + 1) / 2) (by omega)
        exact ⟨0, by omega⟩
      · obtain ⟨j, hj⟩ := popcountNat_eq_one (m := (k + 1) / 2) (by omega)
        exact ⟨j + 1, by rw [Nat.pow_succ]; omega⟩

/-! ## Overflows, through integers -/

theorem ovf_comm {n : Nat} (x y : BitVec n) : (x.saddOverflow y = y.saddOverflow x) ∧
    (x.uaddOverflow y = y.uaddOverflow x) ∧ (x.smulOverflow y = y.smulOverflow x) ∧
    (x.umulOverflow y = y.umulOverflow x) := by
  simp [BitVec.saddOverflow, BitVec.uaddOverflow, BitVec.smulOverflow,
    BitVec.umulOverflow, Int.add_comm, Nat.add_comm, Int.mul_comm, Nat.mul_comm]

theorem ssubOverflow_zero_left {n : Nat} (hn : 0 < n) (x : BitVec n) :
    (0#n).ssubOverflow x = decide (x = BitVec.intMin n) := by
  have := BitVec.le_toInt x; have := BitVec.toInt_lt (x := x)
  rw [Bool.eq_iff_iff]
  simp [BitVec.ssubOverflow, ← BitVec.toInt_inj, BitVec.toInt_intMin_of_pos hn]; omega

section
variable {w : Nat} {x y : BitVec w}

theorem sadd_ok : x.saddOverflow y = false ↔
    -2 ^ (w - 1) ≤ x.toInt + y.toInt ∧ x.toInt + y.toInt < 2 ^ (w - 1) := by
  simp [BitVec.saddOverflow]; omega

theorem ssub_ok : x.ssubOverflow y = false ↔
    -2 ^ (w - 1) ≤ x.toInt - y.toInt ∧ x.toInt - y.toInt < 2 ^ (w - 1) := by
  simp [BitVec.ssubOverflow]; omega

theorem smul_ok : x.smulOverflow y = false ↔
    -2 ^ (w - 1) ≤ x.toInt * y.toInt ∧ x.toInt * y.toInt < 2 ^ (w - 1) := by
  simp [BitVec.smulOverflow]; omega

theorem uadd_ok : x.uaddOverflow y = false ↔ x.toNat + y.toNat < 2 ^ w := by
  simp [BitVec.uaddOverflow]

theorem usub_ok : x.usubOverflow y = false ↔ y.toNat ≤ x.toNat := by
  simp [BitVec.usubOverflow]

theorem umul_ok : x.umulOverflow y = false ↔ x.toNat * y.toNat < 2 ^ w := by
  simp [BitVec.umulOverflow]

theorem toInt_add_ok (h : x.saddOverflow y = false) : (x + y).toInt = x.toInt + y.toInt :=
  BitVec.toInt_add_of_not_saddOverflow (by simp [h])

theorem toInt_sub_ok (h : x.ssubOverflow y = false) : (x - y).toInt = x.toInt - y.toInt :=
  BitVec.toInt_sub_of_not_ssubOverflow (by simp [h])

theorem toInt_mul_ok (h : x.smulOverflow y = false) : (x * y).toInt = x.toInt * y.toInt :=
  BitVec.toInt_mul_of_not_smulOverflow (by simp [h])

theorem toNat_add_ok (h : x.uaddOverflow y = false) : (x + y).toNat = x.toNat + y.toNat :=
  BitVec.toNat_add_of_not_uaddOverflow (by simp [h])

theorem toNat_sub_ok (h : x.usubOverflow y = false) : (x - y).toNat = x.toNat - y.toNat :=
  BitVec.toNat_sub_of_not_usubOverflow (by simp [h])

theorem toNat_mul_ok (h : x.umulOverflow y = false) : (x * y).toNat = x.toNat * y.toNat :=
  BitVec.toNat_mul_of_not_umulOverflow (by simp [h])

end

theorem smulOverflow_neg_swap {n : Nat} {c v : BitVec n} (hc : c ≠ BitVec.intMin n)
    (hv : v ≠ BitVec.intMin n) : (-c).smulOverflow v = c.smulOverflow (-v) := by
  simp only [BitVec.smulOverflow, BitVec.toInt_neg_of_ne_intMin hc,
    BitVec.toInt_neg_of_ne_intMin hv, Int.neg_mul, Int.mul_neg]

theorem umul_assoc_ok {n : Nat} {x y z : BitVec n} (h1 : x.umulOverflow y = false)
    (h2 : (x * y).umulOverflow z = false) : x.umulOverflow (y * z) = false := by
  have e := toNat_mul_ok h1
  rw [umul_ok] at *
  rw [e] at h2
  have : (y * z).toNat ≤ y.toNat * z.toNat := by rw [BitVec.toNat_mul]; exact Nat.mod_le _ _
  calc x.toNat * (y * z).toNat ≤ x.toNat * (y.toNat * z.toNat) := Nat.mul_le_mul_left _ this
    _ = x.toNat * y.toNat * z.toNat := (Nat.mul_assoc ..).symm
    _ < 2 ^ n := h2

theorem smul_assoc_ok {n : Nat} {x y z : BitVec n} (h1 : x.smulOverflow y = false)
    (h2 : (x * y).smulOverflow z = false) (h3 : y.smulOverflow z = false) :
    x.smulOverflow (y * z) = false := by
  rwa [← BitVec.smulOverflow_assoc (by simp [h1]) (by simp [h3])]

theorem toInt_bounds {w : Nat} (x : BitVec w) :
    -2 ^ (w - 1) ≤ x.toInt ∧ x.toInt < 2 ^ (w - 1) :=
  ⟨BitVec.le_toInt x, BitVec.toInt_lt⟩

open Lean Meta Elab Tactic in
/-- Adds the integer meaning of the non-overflow hypotheses. -/
def ovfEqs (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.eq? | continue
    unless rhs.isConstOf ``Bool.false do continue
    let lems := [(``BitVec.saddOverflow, ``toInt_add_ok), (``BitVec.ssubOverflow, ``toInt_sub_ok),
      (``BitVec.smulOverflow, ``toInt_mul_ok), (``BitVec.uaddOverflow, ``toNat_add_ok),
      (``BitVec.usubOverflow, ``toNat_sub_ok), (``BitVec.umulOverflow, ``toNat_mul_ok)]
    for (f, lem) in lems do
      if lhs.isAppOfArity f 3 then
        let pf ← mkAppM lem #[d.toExpr]
        let (_, g') ← (← g.assert `hovf (← inferType pf) pf).intro1P
        g := g'
  return g


theorem arith_exists_concat_width {a b : Int} {P : Int → Int → Prop} :
    (∃ n, 0 < n ∧ ∃ m, 0 < m ∧ a = n ∧ b = m ∧ P n m) ↔ 0 < a ∧ 0 < b ∧ P a b :=
  ⟨fun ⟨_, h0, _, h1, e1, e2, h⟩ => by subst e1 e2; exact ⟨h0, h1, h⟩,
    fun ⟨h0, h1, h⟩ => ⟨_, h0, _, h1, rfl, rfl, h⟩⟩

theorem arith_exists_concat_width' {a b : Int} {P : Int → Int → Prop} :
    (∃ n m, 0 < n ∧ 0 < m ∧ a = n ∧ b = m ∧ P n m) ↔ 0 < a ∧ 0 < b ∧ P a b :=
  ⟨fun ⟨_, _, h0, h1, e1, e2, h⟩ => by subst e1 e2; exact ⟨h0, h1, h⟩,
    fun ⟨h0, h1, h⟩ => ⟨_, _, h0, h1, rfl, rfl, h⟩⟩

theorem arith_exists_extend_width {a : Int} {P : Int → Prop} :
    (∃ n, 0 < n ∧ a = n ∧ P n) ↔ 0 < a ∧ P a :=
  ⟨fun ⟨_, h0, e, h⟩ => by subst e; exact ⟨h0, h⟩, fun ⟨h0, h⟩ => ⟨_, h0, rfl, h⟩⟩

theorem arith_one_lt_two_pow {k : Nat} : (1 : Int) < 2 ^ k ↔ 0 < k := by
  have e : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by push_cast; rfl
  rw [← e]; constructor
  · intro h
    have : 1 < 2 ^ k := by omega
    exact Nat.pos_of_ne_zero (fun h0 => by subst h0; simp at this)
  · intro h; have := Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.1 h); omega

/-! ## Overflows -/

section
variable {n : Nat} (x y : BitVec n)

theorem arith_saddOverflow_comm : x.saddOverflow y = y.saddOverflow x := by
  simp [BitVec.saddOverflow, Int.add_comm]
theorem arith_uaddOverflow_comm : x.uaddOverflow y = y.uaddOverflow x := by
  simp [BitVec.uaddOverflow, Nat.add_comm]
theorem arith_smulOverflow_comm : x.smulOverflow y = y.smulOverflow x := by
  simp [BitVec.smulOverflow, Int.mul_comm]
theorem arith_umulOverflow_comm : x.umulOverflow y = y.umulOverflow x := by
  simp [BitVec.umulOverflow, Nat.mul_comm]

end

theorem arith_ofInt_eq_ofInt_iff {n : Nat} {a b : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n)
    (hb0 : 0 ≤ b) (hb1 : b < 2 ^ n) : BitVec.ofInt n a = BitVec.ofInt n b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toInt h
    have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
    have h2 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofInt, e, Int.emod_eq_of_lt ha0 ha1, Int.emod_eq_of_lt hb0 hb1] at h2
    omega
  · rintro rfl; rfl

theorem arith_ofInt_eq_zero_iff {n : Nat} {a : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) :
    BitVec.ofInt n a = 0#n ↔ a = 0 := by
  have h := arith_ofInt_eq_ofInt_iff (n := n) ha0 ha1 (Int.le_refl 0) (Int.pow_pos (by decide))
  rw [← h]; rfl

theorem arith_zero_eq_ofInt_iff {n : Nat} {a : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) :
    0#n = BitVec.ofInt n a ↔ a = 0 := by
  rw [eq_comm, arith_ofInt_eq_zero_iff ha0 ha1]

theorem arith_toNat_ofInt {n : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ n) :
    (BitVec.ofInt n z).toNat = z.toNat := by
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  rw [BitVec.toNat_ofInt, e, Int.emod_eq_of_lt h0 h1]

theorem arith_toNat_ofInt_sub {n : Nat} {a b : Int} (hb0 : 0 ≤ b) (hba : b ≤ a) (ha1 : a < 2 ^ n) :
    (BitVec.ofInt n a - BitVec.ofInt n b).toNat = (a - b).toNat := by
  rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def, arith_toNat_ofInt hb0 (by omega), arith_toNat_ofInt (by omega) ha1]
      omega),
    arith_toNat_ofInt hb0 (by omega), arith_toNat_ofInt (by omega) ha1]
  omega

theorem arith_natCast_lt_two_pow (n : Nat) : (n : Int) < 2 ^ n := by
  have := Nat.lt_two_pow_self (n := n)
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  omega

theorem arith_ite_lt {c : Prop} [Decidable c] {a b B : Int} (ha : c → a < B) (hb : ¬c → b < B) :
    (if c then a else b) < B := by
  split <;> simp_all

theorem arith_ite_nonneg {c : Prop} [Decidable c] {a b : Int} (ha : c → 0 ≤ a) (hb : ¬c → 0 ≤ b) :
    0 ≤ if c then a else b := by
  split <;> simp_all


/-! ## Overflow facts, through integers -/

section
variable {w : Nat} {x y : BitVec w}

theorem arith_sadd_ovf : x.saddOverflow y = true ↔
    x.toInt + y.toInt < -2 ^ (w - 1) ∨ 2 ^ (w - 1) ≤ x.toInt + y.toInt := by
  simp [BitVec.saddOverflow]; omega
theorem arith_ssub_ovf : x.ssubOverflow y = true ↔
    x.toInt - y.toInt < -2 ^ (w - 1) ∨ 2 ^ (w - 1) ≤ x.toInt - y.toInt := by
  simp [BitVec.ssubOverflow]; omega
theorem arith_smul_ovf : x.smulOverflow y = true ↔
    x.toInt * y.toInt < -2 ^ (w - 1) ∨ 2 ^ (w - 1) ≤ x.toInt * y.toInt := by
  simp [BitVec.smulOverflow]; omega
theorem arith_uadd_ovf : x.uaddOverflow y = true ↔ 2 ^ w ≤ x.toNat + y.toNat := by
  simp [BitVec.uaddOverflow]
theorem arith_usub_ovf : x.usubOverflow y = true ↔ x.toNat < y.toNat := by
  simp [BitVec.usubOverflow]
theorem arith_umul_ovf : x.umulOverflow y = true ↔ 2 ^ w ≤ x.toNat * y.toNat := by
  simp [BitVec.umulOverflow]


theorem ofInt_zero' (n : Nat) : BitVec.ofInt n 0 = 0#n := by
  apply BitVec.eq_of_toNat_eq; simp

theorem zero_saddOverflow : (0#w).saddOverflow x = false := by
  rw [sadd_ok]; have := toInt_bounds x; simp; omega
theorem saddOverflow_zero : x.saddOverflow 0#w = false := by
  rw [sadd_ok]; have := toInt_bounds x; simp; omega
theorem zero_uaddOverflow : (0#w).uaddOverflow x = false := by
  rw [uadd_ok]; have := x.isLt; simp; omega
theorem uaddOverflow_zero : x.uaddOverflow 0#w = false := by
  rw [uadd_ok]; have := x.isLt; simp; omega
theorem ssubOverflow_zero : x.ssubOverflow 0#w = false := by
  rw [ssub_ok]; have := toInt_bounds x; simp; omega
theorem usubOverflow_zero : x.usubOverflow 0#w = false := by
  rw [usub_ok]; simp
theorem zero_smulOverflow : (0#w).smulOverflow x = false := by
  rw [smul_ok]; simp; have : (0 : Int) < 2 ^ (w - 1) := Int.pow_pos (by decide); omega
theorem smulOverflow_zero : x.smulOverflow 0#w = false := by
  rw [smul_ok]; simp; have : (0 : Int) < 2 ^ (w - 1) := Int.pow_pos (by decide); omega
theorem zero_umulOverflow : (0#w).umulOverflow x = false := by
  rw [umul_ok]; simp; exact Nat.two_pow_pos w
theorem umulOverflow_zero : x.umulOverflow 0#w = false := by
  rw [umul_ok]; simp; exact Nat.two_pow_pos w

theorem zero_saddOverflow' : ((0 : BitVec w)).saddOverflow x = false := by
  rw [sadd_ok]; have := toInt_bounds x; simp; omega
theorem saddOverflow_zero' : x.saddOverflow (0 : BitVec w) = false := by
  rw [sadd_ok]; have := toInt_bounds x; simp; omega
theorem zero_uaddOverflow' : ((0 : BitVec w)).uaddOverflow x = false := by
  rw [uadd_ok]; have := x.isLt; simp; omega
theorem uaddOverflow_zero' : x.uaddOverflow (0 : BitVec w) = false := by
  rw [uadd_ok]; have := x.isLt; simp; omega
theorem ssubOverflow_zero' : x.ssubOverflow (0 : BitVec w) = false := by
  rw [ssub_ok]; have := toInt_bounds x; simp; omega
theorem usubOverflow_zero' : x.usubOverflow (0 : BitVec w) = false := by
  rw [usub_ok]; simp
theorem zero_smulOverflow' : ((0 : BitVec w)).smulOverflow x = false := by
  rw [smul_ok]; simp; have : (0 : Int) < 2 ^ (w - 1) := Int.pow_pos (by decide); omega
theorem smulOverflow_zero' : x.smulOverflow (0 : BitVec w) = false := by
  rw [smul_ok]; simp; have : (0 : Int) < 2 ^ (w - 1) := Int.pow_pos (by decide); omega
theorem zero_umulOverflow' : ((0 : BitVec w)).umulOverflow x = false := by
  rw [umul_ok]; simp; exact Nat.two_pow_pos w
theorem umulOverflow_zero' : x.umulOverflow (0 : BitVec w) = false := by
  rw [umul_ok]; simp; exact Nat.two_pow_pos w

theorem sadd_ovf_fold : (x.toInt + y.toInt < -2 ^ (w - 1) ∨ x.toInt + y.toInt > 2 ^ (w - 1) - 1) ↔
    x.saddOverflow y = true := by
  rw [arith_sadd_ovf]; omega
theorem ssub_ovf_fold : (x.toInt - y.toInt < -2 ^ (w - 1) ∨ x.toInt - y.toInt > 2 ^ (w - 1) - 1) ↔
    x.ssubOverflow y = true := by
  rw [arith_ssub_ovf]; omega
theorem smul_ovf_fold : (x.toInt * y.toInt < -2 ^ (w - 1) ∨ x.toInt * y.toInt > 2 ^ (w - 1) - 1) ↔
    x.smulOverflow y = true := by
  rw [arith_smul_ovf]; omega

end

theorem arith_smulOverflow_neg_swap' {n : Nat} {c v : BitVec n} (hc : c ≠ BitVec.intMin n)
    (hv : v ≠ BitVec.intMin n) : (-c).smulOverflow v = (-v).smulOverflow c := by
  rw [smulOverflow_neg_swap hc hv, arith_smulOverflow_comm]

theorem arith_umul_assoc_ok₂ {n : Nat} {x y z : BitVec n} (h1 : y.umulOverflow x = false)
    (h2 : (y * x).umulOverflow z = false) : x.umulOverflow (y * z) = false :=
  umul_assoc_ok (by rwa [arith_umulOverflow_comm]) (by rwa [BitVec.mul_comm])

theorem arith_umul_assoc_ok₃ {n : Nat} {x y z : BitVec n} (h1 : x.umulOverflow y = false)
    (h2 : z.umulOverflow (x * y) = false) : x.umulOverflow (y * z) = false :=
  umul_assoc_ok h1 (by rwa [arith_umulOverflow_comm])

theorem arith_umul_assoc_ok₄ {n : Nat} {x y z : BitVec n} (h1 : y.umulOverflow x = false)
    (h2 : z.umulOverflow (y * x) = false) : x.umulOverflow (y * z) = false :=
  arith_umul_assoc_ok₂ h1 (by rwa [arith_umulOverflow_comm])

theorem arith_smul_assoc_ok₂ {n : Nat} {x y z : BitVec n} (h1 : y.smulOverflow x = false)
    (h2 : (y * x).smulOverflow z = false) (h3 : y.smulOverflow z = false) :
    x.smulOverflow (y * z) = false :=
  smul_assoc_ok (by rwa [arith_smulOverflow_comm]) (by rwa [BitVec.mul_comm]) h3

theorem arith_smul_assoc_ok₃ {n : Nat} {x y z : BitVec n} (h1 : x.smulOverflow y = false)
    (h2 : z.smulOverflow (x * y) = false) (h3 : y.smulOverflow z = false) :
    x.smulOverflow (y * z) = false :=
  smul_assoc_ok h1 (by rwa [arith_smulOverflow_comm]) h3

theorem arith_smul_assoc_ok₄ {n : Nat} {x y z : BitVec n} (h1 : y.smulOverflow x = false)
    (h2 : z.smulOverflow (y * x) = false) (h3 : y.smulOverflow z = false) :
    x.smulOverflow (y * z) = false :=
  arith_smul_assoc_ok₂ h1 (by rwa [arith_smulOverflow_comm]) h3

theorem arith_umul_add_ok {n : Nat} {a x y : BitVec n} (h1 : a.umulOverflow x = false)
    (h2 : a.umulOverflow y = false) (h3 : (a * x).uaddOverflow (a * y) = false) :
    a.umulOverflow (x + y) = false := by
  rw [uadd_ok, toNat_mul_ok h1, toNat_mul_ok h2, ← Nat.mul_add] at h3
  rw [umul_ok, BitVec.toNat_add]
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.mod_le _ _)) h3

theorem arith_factor_ok {n : Nat} {a b x y : BitVec n} (hab : a.toNat ≠ 0 ∨ b.toNat ≠ 0)
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
  rw [toNat_mul_ok o3, e4, e3, hc, hs,
    toNat_add_ok (by rw [uadd_ok, e1, e2]; omega), e1, e2]

theorem arith_factor_ok' {n : Nat} {a b x y : BitVec n} (ha : a.toNat ≠ 0 ∨ b.toNat ≠ 0)
    (hd : a.toNat ∣ b.toNat)
    (h1 : a.umulOverflow x = false) (h2 : b.umulOverflow y = false)
    (h3 : (b * y).uaddOverflow (a * x) = false) :
    ckOp ⟨false, true⟩ BitVec.smulOverflow BitVec.umulOverflow (· * ·) (some a)
      (ckOp ⟨false, true⟩ BitVec.saddOverflow BitVec.uaddOverflow (· + ·) (some x)
        (if (b.smtUDiv a).umulOverflow y = true then none else some (b.smtUDiv a * y))) =
      some (b * y + a * x) := by
  rw [BitVec.add_comm]
  exact arith_factor_ok ha hd h1 h2 (by rw [uadd_ok] at *; omega)

open Lean in
/-- The subterms of `e` (without loose bound variables) that satisfy `p`. -/
partial def arithSubterms (p : Expr → Bool) (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc := if p e && !e.hasLooseBVars && !acc.contains e then acc.push e else acc
  match e with
  | .app f a => arithSubterms p a (arithSubterms p f acc)
  | .lam _ t b _ | .forallE _ t b _ => arithSubterms p b (arithSubterms p t acc)
  | .letE _ t v b _ => arithSubterms p b (arithSubterms p v (arithSubterms p t acc))
  | .mdata _ b => arithSubterms p b acc
  | .proj _ _ b => arithSubterms p b acc
  | _ => acc

section
variable {n : Nat}

theorem toInt_cond (x : BitVec n) :
    (2 * (x.toNat : Int) < 2 ^ n ∧ x.toInt = x.toNat) ∨
      (2 ^ n ≤ 2 * (x.toNat : Int) ∧ x.toInt = x.toNat - 2 ^ n) := by
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  rw [BitVec.toInt_eq_toNat_cond]
  split
  · left; exact ⟨by omega, rfl⟩
  · right; exact ⟨by omega, by rw [e]⟩

theorem toNat_lt_int (x : BitVec n) : 0 ≤ (x.toNat : Int) ∧ (x.toNat : Int) < 2 ^ n := by
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  have := x.isLt; omega

theorem toNat_add_cases (x y : BitVec n) :
    ((x + y).toNat : Int) = x.toNat + y.toNat ∨ ((x + y).toNat : Int) + 2 ^ n = x.toNat + y.toNat := by
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  have := x.isLt; have := y.isLt
  rw [BitVec.toNat_add]
  by_cases h : x.toNat + y.toNat < 2 ^ n
  · left; rw [Nat.mod_eq_of_lt h]; push_cast; rfl
  · right; rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem toNat_sub_cases (x y : BitVec n) :
    ((x - y).toNat : Int) + y.toNat = x.toNat ∨ ((x - y).toNat : Int) + y.toNat = x.toNat + 2 ^ n := by
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  have := x.isLt; have := y.isLt
  rw [BitVec.toNat_sub]
  by_cases h : y.toNat ≤ x.toNat
  · left
    rw [show 2 ^ n - y.toNat + x.toNat = (x.toNat - y.toNat) + 2 ^ n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    omega
  · right; rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem toNat_neg_cases (x : BitVec n) :
    ((-x).toNat : Int) + x.toNat = 0 ∨ ((-x).toNat : Int) + x.toNat = 2 ^ n := by
  have := toNat_sub_cases 0#n x
  rw [BitVec.zero_sub] at this
  simpa using this

theorem two_pow_cast (n : Nat) :
    ((2 : Nat) : Int) ^ n = (2 : Int) ^ n ∧ ((2 : Nat) : Int) ^ (n - 1) = (2 : Int) ^ (n - 1) ∧
      (((2 ^ n : Nat)) : Int) = (2 : Int) ^ n := by
  refine ⟨rfl, rfl, by push_cast; rfl⟩

theorem two_pow_pred (n : Nat) : n = 0 ∨ ((2 : Int) ^ n = 2 * 2 ^ (n - 1) ∧ 2 ^ n = 2 * 2 ^ (n - 1)) := by
  rcases n with _ | k
  · exact .inl rfl
  · right; simp only [Nat.add_sub_cancel]; constructor
    · rw [Int.pow_succ]; omega
    · rw [Nat.pow_succ]; omega

end

open Lean Meta Elab Tactic in
/-- Adds what `omega` needs of the `toInt`s and `toNat`s of the goal and
hypotheses: their bounds, the `toInt`s through the `toNat`s, the `toNat`s of
sums and differences through those of their operands, and `2 ^ n` through
`2 ^ (n - 1)`. The facts on `x.toInt` (a disjunction, which `omega` splits) are
only added when `x.toInt` occurs: on a fresh `x.toInt` they constrain nothing. -/
def arithOvfBounds (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  let mut exprs : Array Expr := #[← instantiateMVars (← g.getType)]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then exprs := exprs.push (← instantiateMVars d.type)
  let mut atoms : Array Expr := #[]
  let mut intAtoms : Array Expr := #[]
  for e in exprs do
    let subs := arithSubterms
      (fun sub => sub.isAppOfArity ``BitVec.toInt 2 || sub.isAppOfArity ``BitVec.toNat 2) e
    atoms := atoms ++ (subs.map (·.appArg!)).filter (!atoms.contains ·)
    for sub in subs do
      if sub.isAppOfArity ``BitVec.toInt 2 && !intAtoms.contains sub.appArg! then
        intAtoms := intAtoms.push sub.appArg!
  -- the operands of the sums and differences, recursively
  let mut i := 0
  while i < atoms.size do
    let x := atoms[i]!
    if x.isAppOfArity ``HAdd.hAdd 6 || x.isAppOfArity ``HSub.hSub 6 then
      for y in [x.getArg! 4, x.getArg! 5] do
        unless atoms.contains y do atoms := atoms.push y
    if x.isAppOfArity ``Neg.neg 3 then
      unless atoms.contains x.appArg! do atoms := atoms.push x.appArg!
    i := i + 1
  let mut widths : Array Expr := #[]
  let addFact (g : MVarId) (pf : Expr) : MetaM MVarId := do
    let (_, g') ← (← g.assert `hbd (← inferType pf) pf).intro1P
    return g'
  for x in atoms do
    let lems := if intAtoms.contains x then [``toInt_bounds, ``toNat_lt_int, ``toInt_cond]
      else [``toNat_lt_int]
    for lem in lems do
      g ← addFact g (← mkAppM lem #[x])
    if x.isAppOfArity ``HAdd.hAdd 6 then
      g ← addFact g (← mkAppM ``toNat_add_cases #[x.getArg! 4, x.getArg! 5])
    if x.isAppOfArity ``HSub.hSub 6 then
      g ← addFact g (← mkAppM ``toNat_sub_cases #[x.getArg! 4, x.getArg! 5])
    if x.isAppOfArity ``Neg.neg 3 then
      g ← addFact g (← mkAppM ``toNat_neg_cases #[x.appArg!])
    let ty ← whnfR (← inferType x)
    if ty.isAppOfArity ``BitVec 1 && !widths.contains ty.appArg! then
      widths := widths.push ty.appArg!
      g ← addFact g (← mkAppM ``two_pow_pred #[ty.appArg!])
      g ← addFact g (← mkAppM ``two_pow_cast #[ty.appArg!])
  return g

open Lean Meta Elab Tactic in
/-- Case splits the booleans and the checked flags of the context. -/
partial def arithSplitBools (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars d.type)
    if ty.isConstOf ``Bool || ty.isConstOf ``CoreMod.Checked then
      let subgoals ← g.cases d.fvarId
      return ← subgoals.toList.foldlM (init := []) fun acc sg =>
        return acc ++ (← arithSplitBools sg.mvarId)
  return [g]

theorem arith_add_left_comm {w : Nat} (x y z : BitVec w) : x + (y + z) = y + (x + z) := by
  rw [← BitVec.add_assoc, BitVec.add_comm x y, BitVec.add_assoc]

theorem arith_mul_left_comm {w : Nat} (x y z : BitVec w) : x * (y * z) = y * (x * z) := by
  rw [← BitVec.mul_assoc, BitVec.mul_comm x y, BitVec.mul_assoc]

/-- What a literal is, for `omega`, before it is generalized. -/
theorem lit_facts (n : Nat) (z : Int) :
    (0 ≤ z → z < 2 ^ n → ((BitVec.ofInt n z).toNat : Int) = z) ∧
      (BitVec.ofInt n z).toInt = z.bmod (2 ^ n) := by
  refine ⟨fun h0 h1 => ?_, by simp⟩
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  rw [BitVec.toNat_ofInt, e, Int.emod_eq_of_lt h0 h1, Int.toNat_of_nonneg h0]

open Lean Meta Elab Tactic in
/-- Generalizes the bit-vectors of the literals (`BitVec.ofInt n z`) of the goal
and the hypotheses. -/
elab "bv_arith_gen_lits" : tactic => withMainContext do
  let mut exprs : Array Expr := #[← instantiateMVars (← getMainTarget)]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then exprs := exprs.push (← instantiateMVars d.type)
  let mut lits : Array Expr := #[]
  for e in exprs do
    lits := arithSubterms (·.isAppOfArity ``BitVec.ofInt 2) e lits
  for l in lits do
    let t ← Term.exprToSyntax l
    let n ← Term.exprToSyntax (l.getArg! 0)
    let z ← Term.exprToSyntax (l.getArg! 1)
    evalTactic (← `(tactic| have := BitvecMod.Arith.lit_facts $n $z))
    let x := mkIdent (← mkFreshUserName `bl)
    evalTactic (← `(tactic| generalize $t:term = $x:ident at *))

open Lean Meta Elab Tactic in
/-- Destructs the conjunctions, disjunctions and existentials of the hypotheses. -/
partial def arithSplitHyps (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars d.type)
    if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 || ty.isAppOfArity ``Or 2 then
      let subgoals ← g.cases d.fvarId
      return ← subgoals.toList.foldlM (init := []) fun acc sg =>
        return acc ++ (← arithSplitHyps sg.mvarId)
  return [g]

open Lean Meta Elab Tactic in
elab "bv_arith_split" : tactic => liftMetaTactic arithSplitHyps

open Lean Meta Elab Tactic in
/-- Adds, for the equalities of bit-vectors of the context, the equalities of
their bits at `i`. -/
elab "bv_arith_bit_hyps " i:ident : tactic => withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (t, _, _) := ty.eq? | continue
    unless t.isAppOfArity ``BitVec 1 do continue
    let h := mkIdent d.userName
    evalTactic (← `(tactic| have := congrArg (fun v => BitVec.getLsbD v $i) $h))

open Lean Meta Elab Tactic in
elab "bv_arith_ovf_eqs" : tactic => liftMetaTactic fun g => return [← ovfEqs g]

open Lean Meta Elab Tactic in
elab "bv_arith_bounds" : tactic => liftMetaTactic fun g => return [← arithOvfBounds g]

open Lean Meta Elab Tactic in
elab "bv_arith_bools" : tactic => liftMetaTactic arithSplitBools

/-! ## The helpers of the rules on literals in range -/

theorem to_z_ofInt {n : Nat} (hn : 0 < n) (s : Bool) {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ n) :
    Bitvec.to_z s (n : Int) z = iv s (BitVec.ofInt n z) := by
  unfold Bitvec.to_z
  cases s
  · have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
    simp only [iv, Bool.false_eq_true, ite_false, BitVec.toNat_ofInt, e, Int.emod_eq_of_lt h0 h1]
    omega
  · simp only [iv, ite_true, signed_extract_zero hn]

theorem to_z_true {n : Nat} (hn : 0 < n) (z : Int) :
    Bitvec.to_z true (n : Int) z = (BitVec.ofInt n z).toInt := by
  simp only [Bitvec.to_z, ite_true, signed_extract_zero hn]

theorem to_z_false (n z : Int) : Bitvec.to_z false n z = z := rfl

theorem natCast_sub_one_toNat (n : Nat) : ((n : Int) - 1).toNat = n - 1 := by omega

theorem toInt_eq_neg_iff {n : Nat} (hn : 0 < n) (x : BitVec n) :
    x.toInt = -2 ^ (n - 1) ↔ x = BitVec.intMin n := by
  rw [← BitVec.toInt_inj, BitVec.toInt_intMin_of_pos hn]

theorem min_for_true {n : Nat} (hn : 0 < n) : Bitvec.min_for true n = -2 ^ (n - 1) := by
  simp only [Bitvec.min_for, z_lsl_one, ite_true]; congr 2; omega

theorem max_for_true {n : Nat} (hn : 0 < n) : Bitvec.max_for true n = 2 ^ (n - 1) - 1 := by
  simp only [Bitvec.max_for, z_lsl_one, ite_true]; congr 2; omega

theorem min_for_false (n : Int) : Bitvec.min_for false n = 0 := rfl

theorem max_for_false (n : Nat) : Bitvec.max_for false n = 2 ^ n - 1 := by
  simp [Bitvec.max_for, z_lsl_one]

section
variable {n : Nat} (hn : 0 < n)
include hn

theorem overflows_add_ofInt (s : Bool) {l r : Int} (hl0 : 0 ≤ l) (hl1 : l < 2 ^ n) (hr0 : 0 ≤ r)
    (hr1 : r < 2 ^ n) :
    Bitvec.overflows_add s n l r =
      if s then (BitVec.ofInt n l).saddOverflow (BitVec.ofInt n r)
      else (BitVec.ofInt n l).uaddOverflow (BitVec.ofInt n r) := by
  simp only [Bitvec.overflows_add]
  rw [to_z_ofInt hn _ hl0 hl1, to_z_ofInt hn _ hr0 hr1]
  cases s
  · simp only [iv, min_for_false, max_for_false, BitVec.uaddOverflow, BitVec.toNat_ofInt]
    rw [Bool.eq_iff_iff]; simp [Int.emod_eq_of_lt hl0 hl1, Int.emod_eq_of_lt hr0 hr1]
    have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
    omega
  · have := BitVec.le_toInt (BitVec.ofInt n l); have := BitVec.toInt_lt (x := BitVec.ofInt n l)
    simp only [min_for_true hn, max_for_true hn, BitVec.saddOverflow, iv, ite_true]
    rw [Bool.eq_iff_iff]; simp; omega

theorem overflows_sub_ofInt (s : Bool) {l r : Int} (hl0 : 0 ≤ l) (hl1 : l < 2 ^ n) (hr0 : 0 ≤ r)
    (hr1 : r < 2 ^ n) :
    Bitvec.overflows_sub s n l r =
      if s then (BitVec.ofInt n l).ssubOverflow (BitVec.ofInt n r)
      else (BitVec.ofInt n l).usubOverflow (BitVec.ofInt n r) := by
  simp only [Bitvec.overflows_sub]
  rw [to_z_ofInt hn _ hl0 hl1, to_z_ofInt hn _ hr0 hr1]
  cases s
  · simp only [iv, min_for_false, max_for_false, BitVec.usubOverflow, BitVec.toNat_ofInt]
    rw [Bool.eq_iff_iff]; simp [Int.emod_eq_of_lt hl0 hl1, Int.emod_eq_of_lt hr0 hr1]
    push_cast at *; omega
  · have := BitVec.le_toInt (BitVec.ofInt n l); have := BitVec.toInt_lt (x := BitVec.ofInt n l)
    simp only [min_for_true hn, max_for_true hn, BitVec.ssubOverflow, iv, ite_true]
    rw [Bool.eq_iff_iff]; simp; omega

theorem overflows_mul_ofInt (s : Bool) {l r : Int} (hl0 : 0 ≤ l) (hl1 : l < 2 ^ n) (hr0 : 0 ≤ r)
    (hr1 : r < 2 ^ n) :
    Bitvec.overflows_mul s n l r =
      if s then (BitVec.ofInt n l).smulOverflow (BitVec.ofInt n r)
      else (BitVec.ofInt n l).umulOverflow (BitVec.ofInt n r) := by
  simp only [Bitvec.overflows_mul]
  rw [to_z_ofInt hn _ hl0 hl1, to_z_ofInt hn _ hr0 hr1]
  cases s
  · obtain ⟨l, rfl⟩ := Int.eq_ofNat_of_zero_le hl0
    obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hr0
    have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
    simp only [min_for_false, max_for_false, BitVec.umulOverflow, BitVec.toNat_ofInt, iv,
      Bool.false_eq_true, ite_false, e, Int.emod_eq_of_lt (Int.natCast_nonneg l) hl1,
      Int.emod_eq_of_lt (Int.natCast_nonneg r) hr1, Int.toNat_natCast]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    have : (0 : Int) ≤ l * r := Int.mul_nonneg (Int.natCast_nonneg l) (Int.natCast_nonneg r)
    have e2 : ((l * r : Nat) : Int) = (l : Int) * r := by push_cast; rfl
    rw [← e2] at *
    omega
  · simp only [min_for_true hn, max_for_true hn, BitVec.smulOverflow, iv, ite_true]
    rw [Bool.eq_iff_iff]; simp; omega

theorem is_int_min_ofInt {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ n) :
    Bitvec.is_int_min n z = decide (BitVec.ofInt n z = BitVec.intMin n) := by
  simp only [Bitvec.is_int_min]
  rw [to_z_ofInt hn _ h0 h1, min_for_true hn, ← BitVec.toInt_intMin_of_pos hn]
  simp only [iv, ite_true, BitVec.toInt_inj]

theorem fold_checked_ofInt {a b : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) (hb0 : 0 ≤ b)
    (hb1 : b < 2 ^ n) (c : CoreMod.Checked) (add : Bool) :
    Bitvec.fold_checked c n a b add =
      { signed := c.signed && !(if add then (BitVec.ofInt n a).saddOverflow (BitVec.ofInt n b)
          else (BitVec.ofInt n a).ssubOverflow (BitVec.ofInt n b)),
        unsigned := c.unsigned && !(if add then (BitVec.ofInt n a).uaddOverflow (BitVec.ofInt n b)
          else (BitVec.ofInt n a).usubOverflow (BitVec.ofInt n b)) } := by
  simp only [Bitvec.fold_checked]
  cases add <;> simp [Bitvec.checked_has, overflows_add_ofInt hn _ ha0 ha1 hb0 hb1,
    overflows_sub_ofInt hn _ ha0 ha1 hb0 hb1]

end

theorem ones_nat (n : Nat) : Bitvec.ones (n : Int) = 2 ^ n - 1 := by
  simp only [Bitvec.ones, z_lsl_one, Int.toNat_natCast]

theorem ofInt_ones (n : Nat) : BitVec.ofInt n (Bitvec.ones (n : Int)) = BitVec.allOnes n := by
  have e : ((2 ^ n - 1 : Nat) : Int) = 2 ^ n - 1 := by
    rw [Int.natCast_sub (Nat.one_le_two_pow)]; push_cast; rfl
  rw [ones_nat, ← e, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_allOnes,
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos n) Nat.one_pos)]

theorem ofInt_two_pow_sub_one (n : Nat) : BitVec.ofInt n (2 ^ n - 1) = BitVec.allOnes n := by
  rw [← ofInt_ones, ones_nat]

theorem is_ones_ofInt {n : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ n) :
    Bitvec.is_ones n z = decide (BitVec.ofInt n z = BitVec.allOnes n) := by
  have := two_pow_pos n
  rw [Bitvec.is_ones, ← ofInt_ones, decide_eq_decide,
    arith_ofInt_eq_ofInt_iff h0 h1 (by rw [ones_nat]; omega) (by rw [ones_nat]; omega)]

theorem bits_in_ofInt {n : Nat} {a b : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) (hb0 : 0 ≤ b)
    (hb1 : b < 2 ^ n) :
    Bitvec.bits_in a b = decide (BitVec.ofInt n a &&& BitVec.ofInt n b = BitVec.ofInt n a) := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hb0
  have hp : p < 2 ^ n := by exact_mod_cast ha1
  have hq : q < 2 ^ n := by exact_mod_cast hb1
  rw [Bitvec.bits_in, decide_eq_decide, ← BitVec.toNat_inj, BitVec.toNat_and,
    BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq]
  show ((p &&& q : Nat) : Int) = p ↔ _
  omega

theorem disjoint_ofInt {n : Nat} {a b : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) (hb0 : 0 ≤ b)
    (hb1 : b < 2 ^ n) :
    Bitvec.disjoint a b = decide (BitVec.ofInt n a &&& BitVec.ofInt n b = 0) := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hb0
  have hp : p < 2 ^ n := by exact_mod_cast ha1
  have hq : q < 2 ^ n := by exact_mod_cast hb1
  rw [Bitvec.disjoint, decide_eq_decide, ← BitVec.toNat_inj, BitVec.toNat_and,
    BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq]
  show ((p &&& q : Nat) : Int) = 0 ↔ _
  simp

theorem z_land_eq_left_iff {n : Nat} {a b : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) (hb0 : 0 ≤ b)
    (hb1 : b < 2 ^ n) :
    Prim.z_land a b = a ↔ BitVec.ofInt n a &&& BitVec.ofInt n b = BitVec.ofInt n a := by
  have := bits_in_ofInt (n := n) ha0 ha1 hb0 hb1
  simp only [Bitvec.bits_in, decide_eq_decide] at this
  exact this

theorem z_land_eq_zero_iff {n : Nat} {a b : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) (hb0 : 0 ≤ b)
    (hb1 : b < 2 ^ n) :
    Prim.z_land a b = 0 ↔ BitVec.ofInt n a &&& BitVec.ofInt n b = 0 := by
  have := disjoint_ofInt (n := n) ha0 ha1 hb0 hb1
  simp only [Bitvec.disjoint, decide_eq_decide] at this
  exact this

theorem udivides_eq {d z : Int} (hd0 : 0 ≤ d) (hz0 : 0 ≤ z) :
    Bitvec.udivides d z = decide (d.toNat ∣ z.toNat) := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hd0
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hz0
  simp only [Bitvec.udivides, Prim.divisible, Int.toNat_natCast, Int.natCast_dvd_natCast]

theorem divisible_eq {z d : Int} (hd0 : 0 ≤ d) (hz0 : 0 ≤ z) :
    Prim.divisible z d = decide (d.toNat ∣ z.toNat) := udivides_eq hd0 hz0

/-! ## Bit-vectors of any width -/

theorem exists_sigma_eq {m : Nat} {y : BitVec m} {P : (n : Nat) → BitVec n → Prop} :
    (∃ n x, (⟨m, y⟩ : (n : Nat) × BitVec n) = ⟨n, x⟩ ∧ P n x) ↔ P m y :=
  ⟨fun ⟨_, _, h, p⟩ => by cases h; exact p, fun p => ⟨_, _, rfl, p⟩⟩

theorem exists_sigma_eq' {m : Nat} {y : BitVec m} {P : (n : Nat) → BitVec n → Prop} :
    (∃ n x, (⟨n, x⟩ : (n : Nat) × BitVec n) = ⟨m, y⟩ ∧ P n x) ↔ P m y :=
  ⟨fun ⟨_, _, h, p⟩ => by cases h; exact p, fun p => ⟨_, _, rfl, p⟩⟩

/-! ## Natural widths -/

theorem exists_nat_of_pos {w : Int} (h : 0 < w) : ∃ n : Nat, w = ((n : Nat) : Int) :=
  ⟨w.toNat, (Int.toNat_of_nonneg (Int.le_of_lt h)).symm⟩

theorem exists_nat_of_nonneg {w : Int} (h : 0 ≤ w) : ∃ n : Nat, w = ((n : Nat) : Int) :=
  ⟨w.toNat, (Int.toNat_of_nonneg h).symm⟩

open Lean Meta Elab Tactic in
/-- An integer variable `w` with a hypothesis `0 < w` (the width of a sort of
bit-vectors), if any. -/
def posIntVar? : TacticM (Option (Expr × Expr)) := withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless (ty.isAppOfArity ``LT.lt 4 || ty.isAppOfArity ``LE.le 4) && (ty.getArg! 3).isFVar do continue
    unless ← isDefEq (ty.getArg! 0) (mkConst ``Int) do continue
    unless ← isDefEq (ty.getArg! 2) (toExpr (0 : Int)) do continue
    let pf ← if ty.isAppOfArity ``LT.lt 4 then mkAppM ``exists_nat_of_pos #[d.toExpr]
      else mkAppM ``exists_nat_of_nonneg #[d.toExpr]
    return some (ty.getArg! 3, pf)
  return none

open Lean Meta Elab Tactic in
/-- Replaces the widths `w` (integer variables with `0 < w`) by natural numbers
`n` (`w = ↑n`), and `(↑n).toNat` by `n`, in every hypothesis (also in the types
of the bit-vectors, of width `w.toNat`). -/
partial def natWidths : TacticM Unit := do
  let some (w, hw) ← posIntVar? | return
  let s ← saveState
  try
    withMainContext do
      let pf := hw
      let wi ← Term.exprToSyntax w
      let pfs ← Term.exprToSyntax pf
      evalTactic (← `(tactic| obtain ⟨$(mkIdent `kanon_n), $(mkIdent `kanon_hn)⟩ := $pfs))
      let _ := wi
      evalTactic (← `(tactic| subst $(mkIdent `kanon_hn)))
    withMainContext do
      let some d := (← getLCtx).findFromUserName? `kanon_n | throwError "natWidths"
      let n := d.toExpr
      let T ← mkAppM ``Int.toNat #[← mkAppOptM ``Nat.cast #[mkConst ``Int, none, n]]
      let g ← getMainGoal
      let hyps := (← getLCtx).foldl (init := #[]) fun acc d =>
        if d.isImplementationDetail then acc else acc.push d.fvarId
      let (_, _, g) ← g.generalizeHyp #[{ expr := T, xName? := `kanon_m, hName? := `kanon_hm }] hyps
      replaceMainGoal [g]
      evalTactic (← `(tactic| rw [Int.toNat_natCast] at $(mkIdent `kanon_hm):ident))
      evalTactic (← `(tactic| subst $(mkIdent `kanon_hm)))
      -- the variable keeps a fresh name
      let some d := (← getLCtx).findFromUserName? `kanon_n | return
      let g ← (← getMainGoal).rename d.fvarId (← mkFreshUserName `n)
      replaceMainGoal [g]
  catch _ =>
    s.restore
    return
  natWidths

open Lean Meta Elab Tactic in
elab "bv_nat_widths" : tactic => do
  let gs ← getGoals
  let mut out := []
  for g in gs do
    setGoals [g]
    natWidths
    out := out ++ (← getGoals)
  setGoals out

/-! ## The bound of `msb_of` -/

/-- The bound that `msb_of` gives the values of a term. -/
def MsbOk (x : Nat) (m : Int) : Prop := (x : Int) < 2 ^ (m + 1).toNat

theorem pow_le_pow_int {a b : Nat} (h : a ≤ b) : (2 : Int) ^ a ≤ 2 ^ b := by
  have := Nat.pow_le_pow_right (by decide : 0 < 2) h
  have e1 : ((2 ^ a : Nat) : Int) = (2 : Int) ^ a := by push_cast; rfl
  have e2 : ((2 ^ b : Nat) : Int) = (2 : Int) ^ b := by push_cast; rfl
  omega

theorem msbOk_mono {x : Nat} {m m' : Int} (h : MsbOk x m) (hm : m ≤ m') : MsbOk x m' := by
  unfold MsbOk at *
  have := pow_le_pow_int (a := (m + 1).toNat) (b := (m' + 1).toNat) (by omega)
  omega

theorem msbOk_le {x y : Nat} {m : Int} (h : MsbOk y m) (hm : x ≤ y) : MsbOk x m := by
  unfold MsbOk at *; omega

theorem msbOk_log2 {x : Nat} {z : Int} (hz : 0 < z) (hx : (x : Int) ≤ z) : MsbOk x (Prim.log2 z) := by
  unfold MsbOk Prim.log2
  have := Nat.lt_log2_self (n := z.toNat)
  have e : ((z.toNat.log2 : Nat) : Int) + 1 = ((z.toNat.log2 + 1 : Nat) : Int) := by push_cast; rfl
  rw [e, Int.toNat_natCast]
  have e2 : ((2 ^ (z.toNat.log2 + 1) : Nat) : Int) = (2 : Int) ^ (z.toNat.log2 + 1) := by
    push_cast; rfl
  omega

theorem msbOk_width {n : Nat} (x : BitVec n) : MsbOk x.toNat ((n : Int) - 1) := by
  unfold MsbOk
  rw [show ((n : Int) - 1 + 1).toNat = n by omega]
  have := x.isLt
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  omega

section
variable {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [Lang S] [Typed S]

/-- The values of a term of a sort of bit-vectors are below `2 ^ (msb_of v + 1)`. -/
theorem msb_bound (ρ : S.Env) : ∀ (k : Nat) (v : S.Term), S.size v < k → ∀ (n : Nat) (x : BitVec n),
    S.WT v → S.ty v = sort (.TBitVector n) → S.ev ρ v = some (bv n x) →
    MsbOk x.toNat (Bitvec.msb_of v) := by
  intro k
  induction k with
  | zero => intro v hs; omega
  | succ k ih =>
  intro v hs n x w ht e
  rw [Bitvec.msb_of.eq_1]
  refine getD_firstSome_cons ?_ (getD_firstSome_cons ?_ (getD_firstSome_cons ?_
    (getD_firstSome_cons ?_ (getD_firstSome_cons ?_ (getD_firstSome_cons ?_
    (getD_firstSome_cons ?_ (getD_firstSome_cons ?_ (getD_firstSome_nil ?_))))))))
  · intro r hr
    split at hr
    · rename_i z hp
      split at hr
      · cases hr
        rename_i hz
        obtain ⟨t, rfl⟩ := NodeEmbed.exists_of_proj _ hp
        rw [ty_mk] at ht; subst ht
        rw [WT_mk] at w
        simp only [Node.wt, bv_wf, Node.All] at w
        obtain ⟨⟨⟨m, hm, hmt⟩, hr⟩, -⟩ := w
        rw [sort_inj_iff, Srt.TBitVector.injEq] at hmt
        have hr := hr _ (.inl rfl)
        rw [ev_mk] at e
        simp only [Node.map, Node.eval] at e
        bv_widths
        simp only [ofBV_some, Option.some.injEq, Embed.inj_eq_iff, Sigma.mk.injEq, heq_eq_eq,
          true_and] at e
        subst e
        apply msbOk_log2 (by simpa using hz)
        have := lit_facts n z
        simp at hz
        omega
      · cases hr
    · cases hr
  · intro r hr
    split at hr
    · rename_i z hp
      split at hr
      · cases hr
        rw [Bitvec.size, ht, size_of_ty_TBitVector]
        exact msbOk_width x
      · cases hr
    · cases hr
  -- BitAnd
  · intro r hr
    split at hr
    · rename_i a b hp
      cases hr
      obtain ⟨t, rfl⟩ := NodeEmbed.exists_of_proj _ hp
      have hsz := Lang.size_proj _ _ hp
      simp only [Node.All] at hsz
      rw [ty_mk] at ht; subst ht
      rw [WT_mk] at w
      simp only [Node.wt, Node.All] at w
      obtain ⟨⟨⟨m, hm, hma⟩, hb, ht⟩, wa, wb⟩ := w
      rw [hma] at ht
      simp only [Embed.inj_eq_iff, Srt.TBitVector.injEq] at ht
      subst ht
      rw [ev_mk] at e
      simp only [Node.map, Node.eval] at e
      bv_widths
      simp only [ofBV, Option.map_eq_some_iff] at e
      obtain ⟨y, hy, e⟩ := e
      simp only [Embed.inj_eq_iff, Sigma.mk.injEq, heq_eq_eq, true_and] at e
      subst e
      cases ha : asBV n (S.ev ρ a) <;> cases hb' : asBV n (S.ev ρ b) <;>
        simp only [ha, hb', binOp_none_l, binOp_none_r, binOp_some, reduceCtorEq,
          Option.some.injEq] at hy
      subst hy
      rename_i xa xb
      rw [asBV_eq_some] at ha hb'
      have ia := ih a (by omega) n xa wa hma ha
      have ib := ih b (by omega) n xb wb (hb.trans hma) hb'
      simp only [Bitvec.zmin]
      rw [BitVec.toNat_and]
      split
      · exact msbOk_le ia Nat.and_le_left
      · exact msbOk_le ib Nat.and_le_right
    · cases hr
  -- Ite
  · intro r hr
    split at hr
    · rename_i g l r' hp
      cases hr
      obtain ⟨t, rfl⟩ := NodeEmbed.exists_of_proj _ hp
      have hsz := KanonBool.Lang.size_proj _ _ hp
      simp only [KanonBool.Node.All] at hsz
      rw [KanonBool.ty_mk] at ht; subst ht
      rw [KanonBool.WT_mk] at w
      simp only [KanonBool.Node.wt, KanonBool.Node.All] at w
      obtain ⟨⟨-, hr', ht⟩, -, wl, wr⟩ := w
      rw [KanonBool.ev_mk] at e
      simp only [KanonBool.Node.map, KanonBool.Node.eval, KanonBool.pite_eq_some] at e
      simp only [Bitvec.zmax]
      rcases e with ⟨-, el⟩ | ⟨-, -, er⟩
      · have il := ih l (by omega) n x wl ht.symm el
        split
        · exact il
        · rename_i hc; simp only [decide_eq_true_eq] at hc; exact msbOk_mono il (by omega)
      · have ir := ih r' (by omega) n x wr (hr'.trans ht.symm) er
        split
        · rename_i hc; simp only [decide_eq_true_eq] at hc; exact msbOk_mono ir (by omega)
        · exact ir
    · cases hr
  -- BvExtend false
  · intro r hr
    split at hr
    · rename_i k' u hp
      cases hr
      obtain ⟨t, rfl⟩ := NodeEmbed.exists_of_proj _ hp
      have hsz := Lang.size_proj _ _ hp
      simp only [Node.All] at hsz
      rw [ty_mk] at ht; subst ht
      rw [WT_mk] at w
      simp only [Node.wt, Node.All] at w
      obtain ⟨⟨m, hm, hmu, -, -⟩, wu⟩ := w
      rw [ev_mk] at e
      simp only [Node.map, Node.eval] at e
      obtain ⟨n', xu, hu, h⟩ := withW_eq_some.1 e
      have hv := Typed.ev_sort ρ u _ _ wu hmu hu
      simp only [Srt.val] at hv
      obtain ⟨-, y, hy⟩ := hv
      rw [Embed.inj_eq_iff] at hy
      cases hy
      rw [hu, asBV_bv] at h
      simp only [Option.map_some, ofBV_some, Option.some.injEq, Embed.inj_eq_iff] at h
      have hmu' : S.ty u = sort (.TBitVector ((m.toNat : Nat) : Int)) := by
        rw [Int.toNat_of_nonneg (by omega)]; exact hmu
      have iu := ih u (by omega) _ y wu hmu' hu
      revert h
      generalize m.toNat + k'.toNat = q
      intro h
      cases h
      simp only [Bool.false_eq_true, ite_false] at *
      refine msbOk_le iu ?_
      rw [BitVec.toNat_setWidth]
      exact Nat.mod_le _ _
    · cases hr
  -- Rem false _ #k
  · intro r hr
    split at hr
    · rename_i a b hp
      split at hr
      · rename_i k hk
        split at hr
        · cases hr
          rename_i hk1
          simp only [decide_eq_true_eq] at hk1
          obtain ⟨t, rfl⟩ := NodeEmbed.exists_of_proj _ hp
          obtain ⟨t', rfl⟩ := NodeEmbed.exists_of_proj _ hk
          rw [ty_mk] at ht; subst ht
          rw [WT_mk] at w
          simp only [Node.wt, Node.All] at w
          obtain ⟨⟨⟨m, hm, hma⟩, hb, ht⟩, wa, wb⟩ := w
          rw [hma] at ht
          simp only [Embed.inj_eq_iff, Srt.TBitVector.injEq] at ht
          subst ht
          rw [ty_mk] at hb
          rw [WT_mk] at wb
          simp only [Node.wt, bv_wf, Node.All] at wb
          obtain ⟨⟨-, hr⟩, -⟩ := wb
          have hr := hr _ (.inl (hb.trans hma))
          rw [ev_mk] at e
          simp only [Node.map, Node.eval, ev_mk] at e
          subst hb
          bv_widths
          simp only [ofBV, Option.map_eq_some_iff] at e
          obtain ⟨y, hy, e⟩ := e
          simp only [Embed.inj_eq_iff, Sigma.mk.injEq, heq_eq_eq, true_and] at e
          subst e
          simp only [asBV_bv, Option.map_some] at hy
          cases ha : asBV n (S.ev ρ a) <;>
            simp only [ha, binOp_none_l, binOp_some, reduceCtorEq, Option.some.injEq,
              Bool.false_eq_true, ite_false] at hy
          subst hy
          rename_i xa
          apply msbOk_log2 (by omega)
          have := lit_facts n k
          have hlt := BitVec.toNat_umod (x := xa) (y := BitVec.ofInt n k)
          have : (xa.umod (BitVec.ofInt n k)).toNat < (BitVec.ofInt n k).toNat :=
            hlt ▸ Nat.mod_lt _ (by omega)
          omega
        · cases hr
      · cases hr
    · cases hr
  -- Mod _ #k
  · intro r hr
    split at hr
    · rename_i a b hp
      split at hr
      · rename_i k hk
        split at hr
        · cases hr
          rename_i hk1
          obtain ⟨t, rfl⟩ := NodeEmbed.exists_of_proj _ hp
          obtain ⟨t', rfl⟩ := NodeEmbed.exists_of_proj _ hk
          simp only [Bitvec.size, ty_mk, ht, size_of_ty_TBitVector, Bool.and_eq_true,
            decide_eq_true_eq, z_lsl_one] at hk1
          rw [ty_mk] at ht; subst ht
          rw [WT_mk] at w
          simp only [Node.wt, Node.All] at w
          obtain ⟨⟨⟨m, hm, hma⟩, hb, ht⟩, wa, wb⟩ := w
          rw [hma] at ht
          simp only [Embed.inj_eq_iff, Srt.TBitVector.injEq] at ht
          subst ht
          rw [ty_mk] at hb
          rw [WT_mk] at wb
          simp only [Node.wt, bv_wf, Node.All] at wb
          obtain ⟨⟨-, hr⟩, -⟩ := wb
          have hr := hr _ (.inl (hb.trans hma))
          rw [ev_mk] at e
          simp only [Node.map, Node.eval, ev_mk] at e
          subst hb
          bv_widths
          simp only [ofBV, Option.map_eq_some_iff] at e
          obtain ⟨y, hy, e⟩ := e
          simp only [Embed.inj_eq_iff, Sigma.mk.injEq, heq_eq_eq, true_and] at e
          subst e
          simp only [asBV_bv, Option.map_some] at hy
          cases ha : asBV n (S.ev ρ a) <;>
            simp only [ha, binOp_none_l, binOp_none_r, binOp_some, reduceCtorEq, Option.some.injEq,
              Bool.false_eq_true, ite_false, ite_true] at hy
          subst hy
          rename_i xa
          have hl := lit_facts n k
          have tp := two_pow_pred n
          have hc := toInt_cond (BitVec.ofInt n k)
          have hn : (n : Int).toNat = n := Int.toNat_natCast n
          rw [show ((n : Int) - 1).toNat = n - 1 by omega] at hk1
          apply msbOk_log2 (by omega)
          have hs := BitVec.toInt_smod (x := xa) (y := BitVec.ofInt n k)
          have hkv : (BitVec.ofInt n k).toInt = k := by omega
          rw [hkv] at hs
          have h0 := Int.fmod_nonneg_of_pos xa.toInt (b := k) (by omega)
          have h1 := Int.fmod_lt_of_pos xa.toInt (b := k) (by omega)
          have := toInt_cond (xa.smod (BitVec.ofInt n k))
          have := toNat_lt_int (xa.smod (BitVec.ofInt n k))
          omega
        · cases hr
      · cases hr
    · cases hr
  -- Rem true #k _
  · intro r hr
    split at hr
    · rename_i b a hp
      split at hr
      · rename_i k hk
        split at hr
        · cases hr
          rename_i hk1
          obtain ⟨t, rfl⟩ := NodeEmbed.exists_of_proj _ hp
          obtain ⟨t', rfl⟩ := NodeEmbed.exists_of_proj _ hk
          simp only [Bitvec.size, ty_mk, ht, size_of_ty_TBitVector, Bool.and_eq_true,
            decide_eq_true_eq, z_lsl_one] at hk1
          rw [ty_mk] at ht; subst ht
          rw [WT_mk] at w
          simp only [Node.wt, Node.All] at w
          obtain ⟨⟨⟨m, hm, hmb⟩, ha, ht⟩, wb, wa⟩ := w
          have hma := ha.trans hmb
          have hb := hmb.trans hma.symm
          rw [hmb] at ht
          simp only [Embed.inj_eq_iff, Srt.TBitVector.injEq] at ht
          subst ht
          rw [ty_mk] at hb
          rw [WT_mk] at wb
          simp only [Node.wt, bv_wf, Node.All] at wb
          obtain ⟨⟨-, hr⟩, -⟩ := wb
          have hr := hr _ (.inl (hb.trans hma))
          rw [ev_mk] at e
          simp only [Node.map, Node.eval, ev_mk] at e
          subst hb
          bv_widths
          simp only [ofBV, Option.map_eq_some_iff] at e
          obtain ⟨y, hy, e⟩ := e
          simp only [Embed.inj_eq_iff, Sigma.mk.injEq, heq_eq_eq, true_and] at e
          subst e
          simp only [asBV_bv, Option.map_some] at hy
          cases ha : asBV n (S.ev ρ a) <;>
            simp only [ha, binOp_none_l, binOp_none_r, binOp_some, reduceCtorEq, Option.some.injEq,
              Bool.false_eq_true, ite_false, ite_true] at hy
          subst hy
          rename_i xa
          have hl := lit_facts n k
          have tp := two_pow_pred n
          have hc := toInt_cond (BitVec.ofInt n k)
          have hn : (n : Int).toNat = n := Int.toNat_natCast n
          rw [show ((n : Int) - 1).toNat = n - 1 by omega] at hk1
          apply msbOk_log2 (by omega)
          have hs := BitVec.toInt_srem (BitVec.ofInt n k) xa
          have hkv : (BitVec.ofInt n k).toInt = k := by omega
          rw [hkv] at hs
          have h0 := Int.tmod_nonneg xa.toInt (a := k) (by omega)
          have h1 := Int.natAbs_tmod k xa.toInt
          have h2 := Nat.mod_le k.natAbs xa.toInt.natAbs
          have := toInt_cond (BitVec.srem (BitVec.ofInt n k) xa)
          have := toNat_lt_int (BitVec.srem (BitVec.ofInt n k) xa)
          omega
        · cases hr
      · cases hr
    · cases hr
  · rw [Bitvec.size, ht, size_of_ty_TBitVector]
    exact msbOk_width x




/-- `msb_bound`, at any width and for the values of the term, before its value is known. -/
theorem msb_bound_int (ρ : S.Env) {v : S.Term} {m : Int} (w : S.WT v)
    (ht : S.ty v = sort (.TBitVector m)) :
    ∀ (n : Nat) (x : BitVec n), S.ev ρ v = some (bv n x) →
      (x.toNat : Int) < 2 ^ (Bitvec.msb_of v + 1).toNat := by
  intro n x e
  have hv := Typed.ev_sort ρ v _ _ w ht e
  simp only [Srt.val] at hv
  obtain ⟨hm, y, hy⟩ := hv
  rw [Embed.inj_eq_iff] at hy
  cases hy
  have ht' : S.ty v = sort (.TBitVector ((m.toNat : Nat) : Int)) := by
    rw [Int.toNat_of_nonneg (by omega)]; exact ht
  exact msb_bound ρ _ v (Nat.lt_succ_self _) _ y w ht' e

end

/-- Products of bit-vectors bounded by `msb_of`. -/
theorem mul_msb_ok {n : Nat} {x y : BitVec n} {p q : Int} (hx : (x.toNat : Int) < 2 ^ (p + 1).toNat)
    (hy : (y.toNat : Int) < 2 ^ (q + 1).toNat) :
    (p + q < (n : Int) - 1 → x.umulOverflow y = false) ∧
      (p + q < (n : Int) - 2 → x.smulOverflow y = false) := by
  have e : ∀ k : Nat, ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := fun k => by push_cast; rfl
  rw [← e] at hx hy
  have hx' : x.toNat < 2 ^ (p + 1).toNat := by omega
  have hy' : y.toNat < 2 ^ (q + 1).toNat := by omega
  by_cases h0 : x.toNat = 0 ∨ y.toNat = 0
  · have hz : x.toNat * y.toNat = 0 := by rcases h0 with h | h <;> simp [h]
    have hi : x.toInt * y.toInt = 0 := by
      rcases h0 with h | h
      · have : x = 0#n := BitVec.eq_of_toNat_eq (by simpa using h)
        subst this; simp
      · have : y = 0#n := BitVec.eq_of_toNat_eq (by simpa using h)
        subst this; simp
    have := Nat.two_pow_pos n
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · rw [umul_ok, hz]; exact Nat.two_pow_pos n
    · rw [smul_ok, hi]
      have h2 : (0 : Int) < 2 ^ (n - 1) := Int.pow_pos (by decide)
      constructor <;> omega
  · have hp : 0 ≤ p := by
      rcases Int.lt_or_le p 0 with hc | hc
      · have : (p + 1).toNat = 0 := by omega
        rw [this] at hx'; omega
      · exact hc
    have hq : 0 ≤ q := by
      rcases Int.lt_or_le q 0 with hc | hc
      · have : (q + 1).toNat = 0 := by omega
        rw [this] at hy'; omega
      · exact hc
    have hm : x.toNat * y.toNat < 2 ^ ((p + 1).toNat + (q + 1).toNat) := by
      rw [Nat.pow_add]; exact Nat.mul_lt_mul'' hx' hy'
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [umul_ok]
      exact Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega))
    · have hn1 : 2 ^ ((p + 1).toNat + (q + 1).toNat) ≤ 2 ^ (n - 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hxa : 2 ^ (p + 1).toNat ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      have hya : 2 ^ (q + 1).toNat ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      have tp := two_pow_pred n
      have cx := toInt_cond x
      have cy := toInt_cond y
      have hxi : x.toInt = x.toNat := by
        have := e n; have := e (n - 1); omega
      have hyi : y.toInt = y.toNat := by
        have := e n; have := e (n - 1); omega
      rw [smul_ok, hxi, hyi]
      have h3 : ((x.toNat * y.toNat : Nat) : Int) < 2 ^ (n - 1) := by
        rw [← e]; exact_mod_cast Nat.lt_of_lt_of_le hm hn1
      push_cast at h3
      have : (0 : Int) ≤ x.toNat * y.toNat := Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
      constructor <;> omega

theorem forall_sigma_eq {m : Nat} {y : BitVec m} {P : (n : Nat) → BitVec n → Prop} :
    (∀ n x, (⟨m, y⟩ : (n : Nat) × BitVec n) = ⟨n, x⟩ → P n x) ↔ P m y :=
  ⟨fun h => h _ _ rfl, fun h _ _ e => by cases e; exact h⟩

open Lean Meta Elab Tactic in
/-- Adds, for each term `v` whose `msb_of` occurs and whose sort is known, the
bound of its values (`msb_bound_int`), before they are split. -/
elab "bv_msb_facts" : tactic => withMainContext do
  let mut exprs : Array Expr := #[← instantiateMVars (← getMainTarget)]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then exprs := exprs.push (← instantiateMVars d.type)
  let mut vs : Array Expr := #[]
  for e in exprs do
    vs := arithSubterms (·.isAppOfArity ``BitvecMod.Bitvec.msb_of 5) e vs
  for m in vs do
    let v := m.appArg!
    let s ← saveState
    try
      let wty ← mkAppM ``Kanon.Sem.WT #[m.getArg! 0, v]
      let some w ← Kanon.Proof.findHyp wty | continue
      let some (ht, _, _) ← srtOf? (← mkAppM ``Kanon.Sem.ty #[m.getArg! 0, v]) | continue
      let envTy := mkApp (mkConst ``Kanon.Dom.Env) (← mkAppM ``Kanon.Sem.toDom #[m.getArg! 0])
      let mut ρ? := none
      for d in (← getLCtx) do
        if d.isImplementationDetail then continue
        if ← isDefEq d.type envTy then ρ? := some d.toExpr; break
      let some ρ := ρ? | continue
      let pf ← mkAppM ``msb_bound_int #[ρ, w, ht]
      let g ← getMainGoal
      let (_, g) ← (← g.assert `hmsb (← inferType pf) pf).intro1P
      replaceMainGoal [g]
    catch _ => s.restore

open Lean Meta Elab Tactic in
/-- Adds, for the pairs of `msb_of` bounds of the context (`msb_bound_int`), the
bounds of their products (`mul_msb_ok`). -/
elab "bv_msb_mul" : tactic => withMainContext do
  let mut hs : Array Expr := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``LT.lt 4 && ((ty.getArg! 3).find? (·.isConstOf ``Int.toNat)).isSome &&
        ((ty.getArg! 2).find? (·.isConstOf ``BitVec.toNat)).isSome then
      hs := hs.push d.toExpr
  for h1 in hs do
    for h2 in hs do
      if h1 == h2 then continue
      let s ← saveState
      try
        let pf ← mkAppM ``mul_msb_ok #[h1, h2]
        let g ← getMainGoal
        let (_, g) ← (← g.assert `hmul (← inferType pf) pf).intro1P
        replaceMainGoal [g]
      catch _ => s.restore

open Lean Meta Elab Tactic in
/-- Splits the conditionals of the goal that `split` does not (those whose
instance is not that of their condition, once the condition is unfolded): by
cases on their conditions. -/
partial def splitIfs (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some e := t.find? (fun e => e.isAppOfArity ``ite 5 && !e.hasLooseBVars) | return [g]
  let us := e.getAppFn.constLevels!
  let args := e.getAppArgs
  let (pos, neg) ← g.byCases args[1]!
  let mut out := []
  for (sg, lem, mk) in [(pos, ``ite_cond_eq_true, true), (neg, ``ite_cond_eq_false, false)] do
    let g' ← sg.mvarId.withContext do
      let h := mkFVar sg.fvarId
      let hp ← if mk then mkEqTrue h else mkEqFalse h
      let pf := mkAppN (mkConst lem us) (args.push hp)
      let tg ← instantiateMVars (← sg.mvarId.getType)
      let r ← sg.mvarId.rewrite tg pf
      sg.mvarId.replaceTargetEq r.eNew r.eqProof
    out := out ++ (← splitIfs g')
  return out

open Lean Meta Elab Tactic in
elab "bv_split_ifs" : tactic => do
  let gs ← getGoals
  let mut out := []
  for g in gs do
    setGoals [g]
    let s ← saveState
    try
      setGoals (← splitIfs g)
    catch _ => s.restore
    out := out ++ (← getGoals)
  setGoals out

/-! ## Small and ground bit-vectors -/

/-- The bit-vectors of width 1. -/
theorem bv1_cases (x : BitVec 1) : x = 0#1 ∨ x = 1#1 := by
  have := x.isLt
  rcases h : x.toNat with _ | _ | k
  · left; exact BitVec.eq_of_toNat_eq (by simp [h])
  · right; exact BitVec.eq_of_toNat_eq (by simp [h])
  · omega

open Lean Meta Elab Tactic in
/-- Splits the bit-vectors of width 1 of the context into `0` and `1`. -/
partial def bv1Split : TacticM Unit := withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← whnf (← instantiateMVars d.type)
    unless ty.isAppOfArity ``BitVec 1 do continue
    let w ← whnf ty.appArg!
    unless (← isDefEq w (mkNatLit 1)) do continue
    let x ← Term.exprToSyntax d.toExpr
    evalTactic (← `(tactic| rcases bv1_cases $x with h | h <;> subst h))
    let gs ← getGoals
    let mut out := []
    for g in gs do
      setGoals [g]
      bv1Split
      out := out ++ (← getGoals)
    setGoals out
    return

elab "bv1_split" : tactic => bv1Split

open Lean Meta Elab Tactic in
/-- Evaluates the ground overflow flags of the context (`decide`). -/
elab "bv_ground" : tactic => withMainContext do
  let mut exprs : Array Expr := #[← instantiateMVars (← getMainTarget)]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then exprs := exprs.push (← instantiateMVars d.type)
  let fs := [``BitVec.saddOverflow, ``BitVec.uaddOverflow, ``BitVec.ssubOverflow,
    ``BitVec.usubOverflow, ``BitVec.smulOverflow, ``BitVec.umulOverflow]
  let mut ts : Array Expr := #[]
  for e in exprs do
    ts := arithSubterms (fun t => fs.any (t.isAppOfArity · 3) && !t.hasFVar) e ts
  for t in ts do
    let tstx ← Term.exprToSyntax t
    let s ← saveState
    try evalTactic (← `(tactic| have : $tstx = true := by decide))
    catch _ =>
      s.restore
      try evalTactic (← `(tactic| have : $tstx = false := by decide))
      catch _ => s.restore

theorem toNat_one' {n : Nat} (hn : 0 < n) : (1#n).toNat = 1 := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))

/-! ## Overflow flags -/

section
variable {n : Nat}

theorem usubOverflow_self (x : BitVec n) : x.usubOverflow x = false := by
  simp [BitVec.usubOverflow]
theorem ssubOverflow_self (x : BitVec n) : x.ssubOverflow x = false := by
  rw [ssub_ok]; simp; have : (0 : Int) < 2 ^ (n - 1) := Int.pow_pos (by decide); omega
theorem usubOverflow_eq_ult (x y : BitVec n) : x.usubOverflow y = x.ult y := by
  simp [BitVec.usubOverflow, BitVec.ult]
theorem uaddOverflow_eq_ult_not (x y : BitVec n) : x.uaddOverflow y = (~~~x).ult y := by
  have := x.isLt; have := y.isLt
  rw [Bool.eq_iff_iff, arith_uadd_ovf, BitVec.ult_iff_lt, BitVec.lt_def, BitVec.toNat_not]
  omega
theorem one_uaddOverflow (h : 0 < n) (x : BitVec n) :
    (1#n).uaddOverflow x = decide (x = BitVec.allOnes n) := by
  have := x.isLt
  rw [Bool.eq_iff_iff, arith_uadd_ovf, toNat_one' h, decide_eq_true_eq, ← BitVec.toNat_inj,
    BitVec.toNat_allOnes]
  omega
theorem smulOverflow_dec (x y : BitVec n) : x.smulOverflow y =
    (decide (x.toInt * y.toInt < -2 ^ (n - 1)) || decide (x.toInt * y.toInt > 2 ^ (n - 1) - 1)) := by
  rw [Bool.eq_iff_iff, arith_smul_ovf]; simp; omega

theorem umulOverflow_lits {a b : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) (hb0 : 0 ≤ b)
    (hb1 : b < 2 ^ n) : (BitVec.ofInt n a).umulOverflow (BitVec.ofInt n b) =
      (decide (a * b < 0) || decide (a * b > 2 ^ n - 1)) := by
  have la := (lit_facts n a).1 ha0 ha1
  have lb := (lit_facts n b).1 hb0 hb1
  rw [Bool.eq_iff_iff, arith_umul_ovf]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  have e : (((BitVec.ofInt n a).toNat * (BitVec.ofInt n b).toNat : Nat) : Int) = a * b := by
    push_cast; rw [la, lb]
  have e2 : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  have : 0 ≤ a * b := Int.mul_nonneg ha0 hb0
  constructor
  · intro h; right
    have : ((2 ^ n : Nat) : Int) ≤ (((BitVec.ofInt n a).toNat * (BitVec.ofInt n b).toNat : Nat) : Int) :=
      Int.ofNat_le.2 h
    omega
  · rintro (h | h)
    · omega
    · have : ((2 ^ n : Nat) : Int) ≤ (((BitVec.ofInt n a).toNat * (BitVec.ofInt n b).toNat : Nat) : Int) := by omega
      exact_mod_cast this

theorem umulOverflow_udiv (x y : BitVec n) : x.umulOverflow (y.smtUDiv x) = false := by
  rw [umul_ok]
  by_cases hx : x.toNat = 0
  · rw [hx]; simp; exact Nat.two_pow_pos n
  · rw [smtUDiv_toNat hx]
    exact Nat.lt_of_le_of_lt (Nat.mul_div_le _ _) y.isLt

theorem one_lt_natCast_iff : (1 : Int) < (n : Int) ↔ 1 < n := by omega
theorem natCast_eq_two_iff : (n : Int) = 2 ↔ n = 2 := by omega

theorem toInt_one' (h : 1 < n) : (1#n).toInt = 1 := by
  have c := toInt_cond (1#n)
  rw [toNat_one' (by omega)] at c
  have := two_pow_pred n
  have h2 : (2 : Int) ^ 1 ≤ 2 ^ (n - 1) := pow_le_pow_int (by omega)
  omega
theorem one_uadd_one (h : 1 < n) : (1#n).uaddOverflow 1#n = false := by
  rw [uadd_ok, toNat_one' (by omega)]
  have := Nat.pow_le_pow_right (by decide : 0 < 2) h
  simp at this; omega
theorem one_sadd_one (h : 1 < n) : (1#n).saddOverflow 1#n = decide (n = 2) := by
  rw [Bool.eq_iff_iff, arith_sadd_ovf, toInt_one' h, decide_eq_true_eq]
  have := two_pow_pred n
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · have : n = 2 := by omega
    subst this; simp
  · have h2 : (2 : Int) ^ 2 ≤ 2 ^ (n - 1) := pow_le_pow_int (by omega)
    constructor
    · intro; omega
    · intro; omega

theorem toInt_ofInt_range (hn : 0 < n) {z : Int} (h0 : -2 ^ (n - 1) ≤ z) (h1 : z < 2 ^ (n - 1)) :
    (BitVec.ofInt n z).toInt = z := by
  have tp := two_pow_pred n
  have c := toInt_cond (BitVec.ofInt n z)
  have b := toNat_lt_int (BitVec.ofInt n z)
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  have hz : ((BitVec.ofInt n z).toNat : Int) = z % 2 ^ n := by
    rw [BitVec.toNat_ofInt, e, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
  rcases Int.lt_or_le z 0 with hz0 | hz0
  · have : z % 2 ^ n = z + 2 ^ n := by
      rw [show z = (z + 2 ^ n) + (-1) * 2 ^ n by omega, Int.add_mul_emod_self_right,
        Int.emod_eq_of_lt (by omega) (by omega)]
      omega
    omega
  · rw [Int.emod_eq_of_lt hz0 (by omega)] at hz; omega

theorem sadd_pos_slt (hn : 0 < n) (c w : BitVec n) (hc : c.toInt > 0) :
    (BitVec.ofInt n (2 ^ (n - 1) - 1 - c.toInt)).slt w = c.saddOverflow w := by
  have bc := toInt_bounds c; have bw := toInt_bounds w
  rw [Bool.eq_iff_iff, arith_sadd_ovf, BitVec.slt_iff_toInt_lt, toInt_ofInt_range hn (by omega) (by omega)]
  omega

theorem sadd_nonpos_slt (hn : 0 < n) (c w : BitVec n) (hc : ¬ c.toInt > 0) :
    w.slt (BitVec.ofInt n (-2 ^ (n - 1) - c.toInt)) = c.saddOverflow w := by
  have bc := toInt_bounds c; have bw := toInt_bounds w
  rw [Bool.eq_iff_iff, arith_sadd_ovf, BitVec.slt_iff_toInt_lt, toInt_ofInt_range hn (by omega) (by omega)]
  omega

theorem one_saddOverflow (h : 1 < n) (x : BitVec n) :
    (1#n).saddOverflow x = decide (x = BitVec.ofInt n (2 ^ (n - 1) - 1)) := by
  rw [Bool.eq_iff_iff, arith_sadd_ovf, toInt_one' h, decide_eq_true_eq]
  have tp := two_pow_pred n
  have h2 : (2 : Int) ^ 1 ≤ 2 ^ (n - 1) := pow_le_pow_int (by omega)
  have b := toInt_bounds x
  have hm : (BitVec.ofInt n (2 ^ (n - 1) - 1)).toInt = 2 ^ (n - 1) - 1 := by
    rw [BitVec.toInt_ofInt]
    rw [Int.bmod_def]
    have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    split <;> omega
  rw [← BitVec.toInt_inj, hm]
  omega


theorem pos_bounds {c M w : Int} (hc : 0 < c) :
    (c * w < -M ↔ w < -(M / c)) ∧ (M - 1 < c * w ↔ (M - 1) / c < w) := by
  have e1 : (-w) * c = -(c * w) := by rw [Int.neg_mul, Int.mul_comm]
  have e2 : w * c = c * w := Int.mul_comm _ _
  constructor
  · have := Int.ediv_lt_iff_lt_mul (a := M) (b := -w) hc
    constructor
    · intro h; have : M < -w * c := by omega
      omega
    · intro h; have : M / c < -w := by omega
      omega
  · have := Int.ediv_lt_iff_lt_mul (a := M - 1) (b := w) hc
    constructor
    · intro h; exact this.2 (by omega)
    · intro h; have := this.1 h; omega

theorem ediv_bounds {M c : Int} (hM : 0 ≤ M) (hc : 0 < c) : 0 ≤ M / c ∧ M / c ≤ M :=
  ⟨Int.ediv_nonneg hM (by omega), Int.ediv_le_self _ hM⟩

theorem smul_const_pos (hn : 1 < n) (x w : BitVec n) (hc : 0 < x.toInt) :
    x.smulOverflow w = (w.slt (BitVec.ofInt n ((-(2 : Int) ^ (n - 1)).tdiv x.toInt)) ||
      (BitVec.ofInt n (((2 : Int) ^ (n - 1) - 1).tdiv x.toInt)).slt w) := by
  have tp := two_pow_pred n
  have hM : (0 : Int) < 2 ^ (n - 1) := Int.pow_pos (by decide)
  have bx := toInt_bounds x; have bw := toInt_bounds w
  rw [Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg (by omega), Int.tdiv_eq_ediv_of_nonneg (by omega)]
  have b1 := ediv_bounds (M := 2 ^ (n - 1)) (by omega) hc
  have b2 := ediv_bounds (M := 2 ^ (n - 1) - 1) (by omega) hc
  have pb := pos_bounds (M := 2 ^ (n - 1)) (w := w.toInt) hc
  rw [Bool.eq_iff_iff, arith_smul_ovf, Bool.or_eq_true, BitVec.slt_iff_toInt_lt,
    BitVec.slt_iff_toInt_lt, toInt_ofInt_range (by omega) (by omega) (by omega),
    toInt_ofInt_range (by omega) (by omega) (by omega)]
  omega

theorem smul_const_neg (hn : 1 < n) (x w : BitVec n) (hc : x.toInt < -1) :
    x.smulOverflow w = (w.slt (BitVec.ofInt n (((2 : Int) ^ (n - 1) - 1).tdiv x.toInt)) ||
      (BitVec.ofInt n ((-(2 : Int) ^ (n - 1)).tdiv x.toInt)).slt w) := by
  have tp := two_pow_pred n
  have hM : (0 : Int) < 2 ^ (n - 1) := Int.pow_pos (by decide)
  have bx := toInt_bounds x; have bw := toInt_bounds w
  have hd : x.toInt = -(-x.toInt) := by omega
  generalize hdd : -x.toInt = d at hd
  have hd0 : 1 < d := by omega
  rw [hd, Int.tdiv_neg, Int.tdiv_neg, Int.neg_tdiv, Int.neg_neg,
    Int.tdiv_eq_ediv_of_nonneg (by omega), Int.tdiv_eq_ediv_of_nonneg (by omega)]
  have b1 := ediv_bounds (M := 2 ^ (n - 1)) (by omega) (show 0 < d by omega)
  have b2 := ediv_bounds (M := 2 ^ (n - 1) - 1) (by omega) (show 0 < d by omega)
  have q1 : 2 ^ (n - 1) / d < 2 ^ (n - 1) := Int.ediv_lt_of_lt_mul (by omega) (by
    have : 2 ^ (n - 1) * 2 ≤ 2 ^ (n - 1) * d := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega)
  have pb := pos_bounds (M := 2 ^ (n - 1)) (w := -w.toInt) (show 0 < d by omega)
  have e : x.toInt * w.toInt = -(d * w.toInt) := by rw [hd, Int.neg_mul]
  have e2 : d * -w.toInt = -(d * w.toInt) := Int.mul_neg _ _
  rw [Bool.eq_iff_iff, arith_smul_ovf, Bool.or_eq_true, BitVec.slt_iff_toInt_lt,
    BitVec.slt_iff_toInt_lt, toInt_ofInt_range (by omega) (by omega) (by omega),
    toInt_ofInt_range (by omega) (by omega) (by omega), e]
  omega

theorem smul_const_m1 (hn : 1 < n) (x w : BitVec n) (hc : x.toInt = -1) :
    x.smulOverflow w = decide (w = BitVec.ofInt n (-2 ^ (n - 1))) := by
  have tp := two_pow_pred n
  have hM : (0 : Int) < 2 ^ (n - 1) := Int.pow_pos (by decide)
  have bw := toInt_bounds w
  rw [Bool.eq_iff_iff, arith_smul_ovf, hc, decide_eq_true_eq, ← BitVec.toInt_inj,
    toInt_ofInt_range (by omega) (by omega) (by omega)]
  omega

theorem umul_const {z : Int} (h2 : 2 ≤ z) (h1 : z < 2 ^ n) (w : BitVec n) :
    (BitVec.ofInt n z).umulOverflow w = (BitVec.ofInt n (((2 : Int) ^ n - 1).tdiv z)).ult w := by
  have la := (lit_facts n z).1 (by omega) h1
  have bw := toNat_lt_int w
  have hp : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
  have b := ediv_bounds (M := 2 ^ n - 1) (by omega) (show 0 < z by omega)
  have lq := (lit_facts n ((2 ^ n - 1) / z)).1 b.1 (by omega)
  have pb := pos_bounds (M := 2 ^ n) (w := (w.toNat : Int)) (show 0 < z by omega)
  have e : (((BitVec.ofInt n z).toNat * w.toNat : Nat) : Int) = z * w.toNat := by push_cast; rw [la]
  have e2 : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  rw [Bool.eq_iff_iff, arith_umul_ovf, BitVec.ult_iff_lt, BitVec.lt_def]
  constructor
  · intro h; have := Int.ofNat_le.2 h; omega
  · intro h; have : ((2 ^ n : Nat) : Int) ≤ (((BitVec.ofInt n z).toNat * w.toNat : Nat) : Int) := by omega
    exact Int.ofNat_le.1 this
theorem smul_lit_pos (hn : 1 < n) (z : Int) (w : BitVec n) (hc : 0 < z.bmod (2 ^ n)) :
    (BitVec.ofInt n z).smulOverflow w =
      (w.slt (BitVec.ofInt n ((-(2 : Int) ^ (n - 1)).tdiv (z.bmod (2 ^ n)))) ||
        (BitVec.ofInt n (((2 : Int) ^ (n - 1) - 1).tdiv (z.bmod (2 ^ n)))).slt w) := by
  have := smul_const_pos hn (BitVec.ofInt n z) w (by rw [BitVec.toInt_ofInt]; exact_mod_cast hc)
  simpa [BitVec.toInt_ofInt] using this

theorem smul_lit_neg (hn : 1 < n) {z : Int} (w : BitVec n) (h0 : 0 ≤ z) (h1 : z < 2 ^ n)
    (hz : z ≠ 0) (hc : z.bmod (2 ^ n) ≤ 0) (hc1 : z.bmod (2 ^ n) ≠ -1) :
    (BitVec.ofInt n z).smulOverflow w =
      (w.slt (BitVec.ofInt n (((2 : Int) ^ (n - 1) - 1).tdiv (z.bmod (2 ^ n)))) ||
        (BitVec.ofInt n ((-(2 : Int) ^ (n - 1)).tdiv (z.bmod (2 ^ n)))).slt w) := by
  have la := (lit_facts n z).1 h0 h1
  have lb := (lit_facts n z).2
  have c := toInt_cond (BitVec.ofInt n z)
  have := smul_const_neg hn (BitVec.ofInt n z) w (by omega)
  simpa [BitVec.toInt_ofInt] using this

theorem smul_lit_m1 (hn : 1 < n) (z : Int) (w : BitVec n) (hc : z.bmod (2 ^ n) = -1) :
    (BitVec.ofInt n z).smulOverflow w = decide (w = BitVec.ofInt n (-2 ^ (n - 1))) :=
  smul_const_m1 hn _ w (by rw [BitVec.toInt_ofInt]; exact_mod_cast hc)

theorem one_umulOverflow (h : 0 < n) (x : BitVec n) : (1#n).umulOverflow x = false := by
  rw [umul_ok, toNat_one' h, Nat.one_mul]; exact x.isLt

theorem one_smulOverflow (h : 1 < n) (x : BitVec n) : (1#n).smulOverflow x = false := by
  rw [smul_ok, toInt_one' h, Int.one_mul]; exact toInt_bounds x

end

open Lean Meta Elab Tactic in
/-- Case splits on the propositions of the `decide`s of the goal and
hypotheses, closing the cases by `simp_all`. -/
partial def byDecide (fuel : Nat := 4) : TacticM Unit := do
  if fuel = 0 then return
  let some p ← withMainContext do
      let mut exprs : Array Expr := #[← instantiateMVars (← getMainTarget)]
      for d in (← getLCtx) do
        if !d.isImplementationDetail then exprs := exprs.push (← instantiateMVars d.type)
      for e in exprs do
        if let some t := e.find? (fun t => t.isAppOfArity ``Decidable.decide 2 && !t.hasLooseBVars) then
          return some (t.getArg! 0)
      return none
    | return
  let ps ← withMainContext (Term.exprToSyntax p)
  evalTactic (← `(tactic| by_cases $(mkIdent `kanon_hd) : $ps))
  let gs ← getGoals
  let mut out := []
  for g in gs do
    setGoals [g]
    let s ← saveState
    try
      evalTactic (← `(tactic| (simp_all; done)))
    catch _ =>
      s.restore
      byDecide (fuel - 1)
    out := out ++ (← getGoals)
  setGoals out

elab "bv_by_decide" : tactic => byDecide

open Lean Meta Elab Tactic in
/-- Case splits on the boolean comparisons and overflow flags of the goal
(`generalize` then `cases`), closing the cases by `simp_all`. -/
partial def boolAtoms (fuel : Nat := 4) : TacticM Unit := do
  if fuel = 0 then return
  let fs := [``BitVec.slt, ``BitVec.ult, ``BitVec.sle, ``BitVec.ule, ``BitVec.saddOverflow,
    ``BitVec.uaddOverflow, ``BitVec.ssubOverflow, ``BitVec.usubOverflow, ``BitVec.smulOverflow,
    ``BitVec.umulOverflow]
  let some t ← withMainContext do
      let e ← instantiateMVars (← getMainTarget)
      return e.find? (fun t => fs.any (t.isAppOfArity · 3) && !t.hasLooseBVars)
    | return
  let ts ← withMainContext (Term.exprToSyntax t)
  let b := mkIdent `kanon_b
  evalTactic (← `(tactic| generalize $ts:term = $b:ident at *))
  evalTactic (← `(tactic| cases $b:ident))
  let gs ← getGoals
  let mut out := []
  for g in gs do
    setGoals [g]
    let s ← saveState
    try
      evalTactic (← `(tactic| (simp_all; done)))
    catch _ =>
      s.restore
      boolAtoms (fuel - 1)
    out := out ++ (← getGoals)
  setGoals out

elab "bv_bool_atoms" : tactic => boolAtoms

/-! ## Bit-vectors of widths equal up to arithmetic -/

section
variable {D : Kanon.Dom} [KanonBool.Values D] [BitvecMod.Values D]
theorem asBV_bv_cast {a b : Nat} (h : b = a) (x : BitVec b) :
    asBV a (some (bv (D := D) b x)) = some (x.cast h) := by
  subst h; simp
theorem bv_eq_cast {a b : Nat} {x : BitVec a} {y : BitVec b} (h : a = b) (hxy : x.cast h = y) :
    bv (D := D) a x = bv b y := by
  subst h; subst hxy; rfl
end
theorem toNat_ofInt_natCast_of_le {m W : Nat} (h : m ≤ W) : (BitVec.ofInt W (m : Int)).toNat = m := by
  rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide) h))

end BitvecMod.Arith

namespace BitvecMod

open BitvecMod.Arith BitvecMod.LitOps

/-- The operations on literals at a sort, as the primitives at its width. -/
macro "bv_arith_unfold" : tactic => `(tactic| (
  try simp only [lit_add, lit_sub, lit_mul, lit_neg, lit_udiv, lit_sdiv, lit_and, lit_or, lit_xor,
    lit_not, lit_shl, lit_lshr, lit_ashr, lit_urem, lit_srem, lit_smod, lit_extract, lit_zext,
    lit_sext, lit_concat, Bitvec.lit_add_overflows, Bitvec.lit_sub_overflows,
    Bitvec.lit_mul_overflows, size_of_ty_TBitVector, size_of_ty_TLoc, Bitvec.size,
    Int.toNat_natCast] at *))

/-- The side conditions of the lemmas on literals: their ranges. -/
macro "bv_arith_disch" : tactic => `(tactic| first
  | assumption
  | omega
  | (simp only [LitOps.masked_nonneg, LitOps.masked_lt, LitOps.masked_lt_nat,
      LitOps.lit_add_nonneg, LitOps.lit_add_lt_nat, LitOps.lit_sub_nonneg, LitOps.lit_sub_lt_nat,
      LitOps.lit_mul_nonneg, LitOps.lit_mul_lt_nat, LitOps.lit_and_nonneg, LitOps.lit_and_lt_nat,
      LitOps.lit_or_nonneg, LitOps.lit_or_lt_nat, LitOps.lit_xor_nonneg, LitOps.lit_xor_lt_nat,
      LitOps.lit_neg_nonneg, LitOps.lit_neg_lt_nat, LitOps.lit_not_nonneg, LitOps.lit_not_lt_nat,
      LitOps.lit_shl_nonneg, LitOps.lit_shl_lt_nat, LitOps.lit_lshr_nonneg,
      LitOps.lit_lshr_lt_nat, LitOps.lit_ashr_nonneg, LitOps.lit_ashr_lt_nat,
      LitOps.lit_udiv_nonneg, LitOps.lit_udiv_lt_nat, Arith.emod_two_pow_nonneg,
      Arith.emod_two_pow_lt, Arith.two_pow_pos, Int.toNat_natCast]; done)
  | (refine Int.lt_of_le_of_lt ?_ (Arith.arith_natCast_lt_two_pow _); omega)
  | (apply Arith.arith_ite_lt <;> intro <;> first
      | omega
      | (refine Int.lt_of_le_of_lt ?_ (Arith.arith_natCast_lt_two_pow _); omega))
  | (apply Arith.arith_ite_nonneg <;> intro <;> omega))

/-- The operations on literals as those on bit-vectors, with their side
conditions. -/
macro "bv_arith_lit_ops" : tactic => `(tactic| (
  (try simp only [Int.toNat_natCast, Bitvec.zmin, BitVec.ushiftRight_eq',
    BitVec.shiftLeft_eq', BitVec.sshiftRight_eq'] at *)
  (try simp (disch := (bv_arith_disch; done)) only [LitOps.ofInt_lit_add, LitOps.ofInt_lit_sub,
    LitOps.ofInt_lit_mul, LitOps.ofInt_lit_neg, LitOps.ofInt_lit_not, LitOps.ofInt_lit_and,
    LitOps.ofInt_lit_or, LitOps.ofInt_lit_xor, LitOps.ofInt_lit_shl, LitOps.ofInt_lit_lshr,
    LitOps.ofInt_lit_ashr, LitOps.ofInt_lit_udiv, Arith.ofInt_emod_two_pow,
    Arith.emod_two_pow_of_lt, Arith.arith_toNat_ofInt, Arith.arith_toNat_ofInt_sub,
    Arith.arith_ofInt_eq_ofInt_iff, Arith.arith_ofInt_eq_zero_iff, Arith.arith_zero_eq_ofInt_iff,
    Arith.ofInt_ones, Arith.is_ones_ofInt, Arith.overflows_add_ofInt, Arith.overflows_sub_ofInt,
    Arith.overflows_mul_ofInt, Arith.is_int_min_ofInt, Arith.fold_checked_ofInt,
    Arith.udivides_eq, Arith.divisible_eq, Arith.to_z_true, Arith.to_z_false, Arith.signed_extract_zero,
    Arith.z_lsl_one, Arith.natCast_sub_one_toNat, Arith.toInt_eq_neg_iff, Int.toNat_natCast,
    decide_eq_true_eq, Arith.ofInt_two_pow_sub_one, BitVec.allOnes_and, BitVec.and_allOnes,
    BitVec.allOnes_or, BitVec.or_allOnes, Arith.sadd_ovf_fold, Arith.ssub_ovf_fold,
    Arith.smul_ovf_fold, Arith.ofInt_zero', Arith.zero_saddOverflow, Arith.saddOverflow_zero,
    Arith.zero_uaddOverflow, Arith.uaddOverflow_zero, Arith.ssubOverflow_zero,
    Arith.usubOverflow_zero, Arith.zero_smulOverflow, Arith.smulOverflow_zero,
    Arith.zero_umulOverflow, Arith.umulOverflow_zero, Arith.zero_saddOverflow',
    Arith.saddOverflow_zero', Arith.zero_uaddOverflow', Arith.uaddOverflow_zero',
    Arith.ssubOverflow_zero', Arith.usubOverflow_zero', Arith.zero_smulOverflow',
    Arith.smulOverflow_zero', Arith.zero_umulOverflow', Arith.umulOverflow_zero',
    BitVec.toNat_zero, BitVec.toInt_zero] at *)))

open Lean Meta Elab Tactic in
/-- The guards on masks (`bits_in`, `disjoint`) as facts on the bit-vectors of
the width of the goal. -/
elab "bv_arith_masks" : tactic => withMainContext do
  let some (t, _, _) := (← instantiateMVars (← getMainTarget)).eq? | throwError "no equality"
  unless t.isAppOfArity ``BitVec 1 do throwError "not bit-vectors"
  let n ← Term.exprToSyntax t.appArg!
  evalTactic (← `(tactic| simp (disch := (bv_arith_disch; done)) only
    [BitvecMod.Arith.bits_in_ofInt (n := $n), BitvecMod.Arith.disjoint_ofInt (n := $n),
     BitvecMod.Arith.z_land_eq_left_iff (n := $n), BitvecMod.Arith.z_land_eq_zero_iff (n := $n),
     decide_eq_true_eq] at *))

/-- Proves an equality of bit-vectors bit by bit, with the bits of the
equalities of the context. -/
macro "bv_arith_bits" : tactic => `(tactic| (
  (try bv_arith_masks)
  (try bv_arith_lit_ops)
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  bv_arith_bit_hyps i
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_not,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_append, ite_false, ite_true,
    BitVec.getLsbD_zero, BitVec.getLsbD_allOnes, BitVec.ushiftRight_eq', BitVec.shiftLeft_eq',
    BitVec.sshiftRight_eq', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_sshiftRight, Bool.and_true, Bool.true_and, decide_true] at *
  bv_arith_lit_ops
  (try simp (disch := omega) only [BitVec.getLsbD_of_ge, Bool.and_false, Bool.false_and] at *)
  first
    | (congr 1; omega)
    | grind [BitVec.getLsbD_of_ge]))

/-- The overflow facts of a case: the flags of the hypotheses as facts on integers, then
`omega`. -/
macro "bv_arith_ovf_core" : tactic => `(tactic| (
  (try simp_all)
  all_goals (repeat' (first | apply And.intro | intro))
  all_goals (try bv_arith_split)
  all_goals bv_arith_ovf_eqs
  all_goals (try simp (disch := omega) only [Arith.toNat_one'] at *)
  all_goals (try rw [Bool.eq_iff_iff])
  all_goals (try simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    gt_iff_lt, ge_iff_le] at *)
  all_goals (try simp only [Arith.sadd_ok, Arith.ssub_ok, Arith.smul_ok, Arith.uadd_ok,
    Arith.usub_ok, Arith.umul_ok, Arith.arith_sadd_ovf, Arith.arith_ssub_ovf,
    Arith.arith_smul_ovf, Arith.arith_uadd_ovf, Arith.arith_usub_ovf, Arith.arith_umul_ovf] at *)
  all_goals (try bv_arith_split)
  all_goals bv_arith_bounds
  all_goals first
    | omega
    | (constructor <;> intro <;> (try bv_arith_split) <;> omega)))

/-- Proves overflow facts: splits the flags, and reasons on integers (case by case, so that it
fails at the first case it cannot prove). -/
macro "bv_arith_ovf" : tactic => `(tactic| (
  (try bv_arith_gen_lits)
  bv_arith_bools
  all_goals bv_arith_ovf_core))

open Lean Meta in
/-- Splits the disjunctions of the hypotheses. -/
partial def arithOrSplit (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if (← instantiateMVars d.type).isAppOfArity ``Or 2 then
      let gs ← g.cases d.fvarId
      return ← gs.toList.foldlM (init := []) fun acc sg =>
        return acc ++ (← arithOrSplit sg.mvarId)
  return [g]

open Lean Elab Tactic in
elab "bv_arith_or_split" : tactic => liftMetaTactic arithOrSplit

/-- `bv_arith_ovf`, splitting the disjunctions of the context (which give the flags that
matter) rather than all the flags: two cases instead of up to sixteen when the guard is a
disjunction on the signed and unsigned checks. -/
macro "bv_arith_ovf_lazy" : tactic => `(tactic| (
  (try bv_arith_gen_lits)
  bv_arith_or_split
  all_goals bv_arith_ovf_core))

/-- Closes a factorization by a constant (`arith_factor_ok`). -/
macro "bv_arith_factor" : tactic => `(tactic| (
  (try simp only [Bool.false_and, Bool.false_or, Bool.true_and] at ⊢)
  first
    | (rw [Arith.arith_factor_ok ?_ ?_ ?_ ?_ ?_]
       all_goals (try simp only [Option.map_some])
       all_goals (try bv_arith_lit_ops)
       all_goals first | rfl | (simp_all; done) | omega)
    | (rw [Arith.arith_factor_ok' ?_ ?_ ?_ ?_ ?_]
       all_goals (try simp only [Option.map_some])
       all_goals (try bv_arith_lit_ops)
       all_goals first | rfl | (simp_all; done) | omega)))

set_option hygiene false in
/-- Closes the value goals left by `bv_arith_sem_core` (its hypothesis `e`). -/
macro "bv_arith_close" : tactic => `(tactic| (
  (try (repeat' (first
    | (simp only [BitvecMod.ckOp_some, BitvecMod.ckOp_none_l, BitvecMod.ckOp_none_r,
        BitvecMod.binOp_some, BitvecMod.binOp_none_l, BitvecMod.binOp_none_r,
        BitvecMod.negOp_some, BitvecMod.negOp_none, Option.some.injEq, reduceCtorEq,
        Option.map_none, Option.map_some, BitvecMod.binB_some, BitvecMod.binB_none_l,
        BitvecMod.binB_none_r, BitvecMod.ofB_none, BitvecMod.ofB_some] at e)
    | split at e)))
  all_goals (try subst e)
  all_goals (try bv_arith_lit_ops)
  all_goals first
    | (bv_arith_bools
       all_goals ((try bv_ground); first
         | (simp_all [Arith.usubOverflow_self, Arith.ssubOverflow_self, Arith.one_uadd_one,
             Arith.one_sadd_one, Arith.one_lt_natCast_iff, Arith.natCast_eq_two_iff]; done)
         | (simp_all [Arith.one_saddOverflow, Arith.one_uaddOverflow, Arith.one_lt_natCast_iff,
             Arith.ofInt_two_pow_sub_one, Arith.zero_saddOverflow, Arith.zero_uaddOverflow]
            bv_by_decide
            done)
         | (simp_all [Arith.usubOverflow_eq_ult, Arith.uaddOverflow_eq_ult_not]; done)
         | (simp_all [Arith.smulOverflow_dec, Arith.umulOverflow_lits]; done)
         | (simp_all [Arith.umulOverflow_udiv]; done)
         | (simp (disch := (first | assumption | omega)) only [Arith.sadd_pos_slt,
             Arith.sadd_nonpos_slt]; done)
         | ((try simp_all)
            (try simp only [Prim.tdiv, BitVec.ofInt_ofNat, Bool.true_eq_false, Bool.false_eq_true,
              false_or, or_false, true_or, or_true, not_false_eq_true, true_and] at *)
            (try simp (disch := (first | assumption | omega)) only [Arith.smul_const_pos,
              Arith.smul_const_neg, Arith.smul_const_m1, Arith.umul_const, Arith.one_umulOverflow,
              Arith.one_smulOverflow, Arith.smul_lit_pos, Arith.smul_lit_neg, Arith.smul_lit_m1])
            first
              | done
              | (simp_all; done)
              | (simp_all; bv_by_decide; done)
              | ((try simp only [Bool.or_eq_true, Bool.or_eq_false_iff] at *); bv_bool_atoms; done))))
    | skip
  all_goals first
    | (bv_arith_factor; done)
    | (bv_msb_mul
       bv_arith_bools
       all_goals (simp_all; done))
    | skip
  all_goals (try (repeat' split))
  all_goals (try bv_arith_lit_ops)
  all_goals first
    | (simp_all [BitVec.mul_assoc, Arith.smulOverflow_neg_swap, Arith.umul_assoc_ok,
        Arith.smul_assoc_ok, Arith.arith_umul_add_ok, BitVec.mul_add]; done)
    | (bv_arith_bools
       all_goals (simp_all [BitVec.mul_assoc, Arith.smulOverflow_neg_swap,
        Arith.umul_assoc_ok, Arith.smul_assoc_ok, Arith.arith_umul_add_ok, BitVec.mul_add]; done))
    | (bv_arith_bools
       all_goals ((simp_all [Arith.arith_smulOverflow_neg_swap', Arith.arith_umul_assoc_ok₂,
        Arith.arith_umul_assoc_ok₃, Arith.arith_umul_assoc_ok₄, Arith.arith_smul_assoc_ok₂,
        Arith.arith_smul_assoc_ok₃, Arith.arith_smul_assoc_ok₄] <;>
        simp_all [BitVec.mul_assoc, BitVec.mul_comm, Arith.arith_mul_left_comm]); done))
    | skip
  all_goals (try simp_all [Arith.ssubOverflow_zero_left])
  all_goals (try bv_arith_lit_ops)
  all_goals (try simp_all)
  all_goals first
    | done
    | omega
    | (bv_arith_bools
       all_goals (
         (try bv1_split)
         all_goals (try simp_all)
         all_goals (try bv_ground)
         all_goals (simp_all (config := { decide := true }); done)))
    | (simp only [KanonBool.pnot, KanonBool.peq, KanonBool.pand, KanonBool.por, ofBV, asB_vbool,
        Option.map_some, Kanon.Embed.inj_eq_iff, decide_true, decide_false, Bool.not_true,
        Bool.not_false, Option.some.injEq, Bool.true_eq_false, Bool.false_eq_true, ite_true,
        ite_false, BitVec.xor_self, BitVec.and_self, BitVec.or_self, BitVec.xor_zero,
        BitVec.zero_xor, BitVec.and_zero, BitVec.zero_and, BitVec.or_zero, BitVec.zero_or] at *
       first | done | (simp_all; done))
    | (grind [BitVec.neg_eq_not_add]; done)
    | (bv_arith_bools
       all_goals (simp_all [Arith.arith_saddOverflow_comm, Arith.arith_uaddOverflow_comm,
        Arith.arith_smulOverflow_comm, Arith.arith_umulOverflow_comm, BitVec.add_comm,
        BitVec.mul_comm]; done))
    | (simp_all [BitVec.add_assoc, BitVec.add_comm, Arith.arith_add_left_comm,
        BitVec.mul_assoc, BitVec.mul_comm, Arith.arith_mul_left_comm]; done)
    | (bv_arith_bits; done)
    | (bv_arith_ovf_lazy; done)
    | (bv_arith_ovf; done)))

/-- The typing half of a refinement. -/
macro "bv_arith_wt" : tactic => `(tactic| (
  intro w
  kanon_lits
  kanon_wt_simp
  (try kanon_split)
  (try subst_vars)
  kanon_wt_simp
  (try bv_tys)
  (try bv_nat_widths)
  bv_arith_unfold
  (try simp only [or_false, false_or, forall_eq', forall_eq, Int.toNat_natCast] at *)
  (try simp only [Kanon.Embed.inj_eq_iff, Srt.TBitVector.injEq, Arith.arith_exists_concat_width,
    Arith.arith_exists_concat_width', Arith.arith_exists_extend_width] at ⊢)
  all_goals (repeat' apply And.intro)
  all_goals first
    | done
    | assumption
    | (simp_all; done)
    | (bv_arith_disch; done)
    | (kanon_exists; done)
    | (simp_all [LitOps.masked_nonneg, LitOps.masked_lt_nat, Arith.two_pow_pos,
        Arith.arith_one_lt_two_pow]; done)
    | grind))

set_option hygiene false in
/-- The value half of a refinement, reduced to the values of the atoms. -/
macro "bv_arith_sem_core" : tactic => `(tactic| (
  intro ρ v w w' e
  kanon_lits
  kanon_wt_simp
  (try kanon_split)
  (try subst_vars)
  kanon_wt_simp
  (try bv_tys)
  (try bv_msb_facts)
  (try simp only [kanon_ev] at e ⊢)
  kanon_cases
  all_goals (try simp only [kanon_val] at *)
  all_goals (try simp only [kanon_val, Option.some.injEq, reduceCtorEq, false_and, and_false,
    ite_true, ite_false, Bool.not_true, Bool.not_false, Option.ite_none_left_eq_some,
    Option.ite_none_right_eq_some] at e ⊢)
  all_goals (try subst e)
  all_goals (try (kanon_split; subst_vars))
  all_goals (try bv_tys)
  all_goals (try bv_widths)
  all_goals (try bv_nat_widths)
  all_goals (try kanon_or_cases)
  all_goals (try simp only [Kanon.Embed.inj_eq_iff, Arith.exists_sigma_eq,
    Arith.exists_sigma_eq', Arith.forall_sigma_eq, Option.some.injEq, reduceCtorEq,
    false_implies, forall_const, implies_true] at *)
  all_goals (try simp only [Sigma.mk.injEq] at *)
  all_goals (try (kanon_split; subst_vars))
  all_goals (try simp only [heq_eq_eq] at *)
  all_goals (try simp only [kanon_val, Option.some.injEq, reduceCtorEq, false_and, and_false,
    ite_true, ite_false, Bool.not_true, Bool.not_false, Sigma.mk.injEq, Int.toNat_natCast] at e ⊢)
  all_goals (try (kanon_split; subst_vars))
  all_goals (try simp only [kanon_val, Option.some.injEq, reduceCtorEq, false_and, and_false,
    ite_true, ite_false, Bool.not_true, Bool.not_false, Option.map_some, Option.map_none] at *)
  all_goals (try (kanon_split; subst_vars))
  all_goals (try simp only [KanonBool.pite, KanonBool.pnot, KanonBool.pand, KanonBool.por,
    KanonBool.peq, Kanon.Embed.inj_eq_iff, Option.some.injEq, reduceCtorEq, Bool.true_eq_false,
    Bool.false_eq_true, ite_true, ite_false, asBV_none, asB_none,
    asBV_bv, asB_vbool] at e ⊢)
  all_goals bv_arith_unfold
  all_goals (try simp only [or_false, false_or, forall_eq', forall_eq, Int.toNat_natCast,
    true_and, and_true, not_false_eq_true, implies_true] at *)
  all_goals (try simp only [ofBV, Option.map_some, Option.map_none, Option.some.injEq,
    reduceCtorEq] at e ⊢)
  all_goals (try subst e)
  all_goals (try simp only [Kanon.Embed.inj_eq_iff, Sigma.mk.injEq, Arith.exists_sigma_eq,
    Arith.exists_sigma_eq', Arith.forall_sigma_eq] at *)
  all_goals (try (kanon_split; subst_vars))
  all_goals (try simp only [heq_eq_eq] at *)))

/-- Proves an arm of the arithmetic functions. -/
macro "bv_arith" : tactic => `(tactic| (
  (try intro _)
  intros
  kanon_rule_lift
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
    bv_arith_sem_core
    all_goals bv_arith_close)))

end BitvecMod
