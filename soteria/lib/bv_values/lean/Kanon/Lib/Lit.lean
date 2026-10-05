import Kanon.Lib.Den
import Kanon.Model.Bitvec.is_bv
import Kanon.Model.Bitvec.is_pow2
import Kanon.Model.Bitvec.msb_of
import Kanon.Model.Bool.of_bool

/-!
# Literals

Facts about the literals and the operations on them (the primitives `lit_add`,
...): bit-vector literals are integers, and the operations reduce their result
modulo `2 ^ width`.
-/

namespace Kanon.Lib

open CoreMod

open Classical

/-! ## Constants in range -/

theorem toNat_ofInt_of_lt {n : Nat} {k : Int} (h0 : 0 ≤ k) (h1 : k < 2 ^ n) :
    (BitVec.ofInt n k).toNat = k.toNat := by
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt h0 (by push_cast; exact h1)]
theorem emod_two_pow_of_lt {n : Nat} {k : Int} (h0 : 0 ≤ k) (h1 : k < 2 ^ n) :
    k % 2 ^ n = k := Int.emod_eq_of_lt h0 h1

theorem ofInt_eq_zero_iff {n : Nat} {k : Int} (h0 : 0 ≤ k) (h1 : k < 2 ^ n) :
    BitVec.ofInt n k = 0#n ↔ k = 0 := by
  rw [← BitVec.toNat_inj, toNat_ofInt_of_lt h0 h1]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  omega

theorem smtUDiv_toNat {n : Nat} {a b : BitVec n} (hb : b.toNat ≠ 0) :
    (a.smtUDiv b).toNat = a.toNat / b.toNat := by
  simp [BitVec.smtUDiv_eq, ← BitVec.toNat_inj, hb]

theorem msb_of_lit (z : Int) (T : Ty) :
    Bitvec.msb_of (.mk (.BitVec z) T) = if 0 < z then log2 z else size_of_ty T - 1 := by
  rw [Bitvec.msb_of]
  by_cases h : 0 < z
  · simp [firstSome, h, HOrElse.hOrElse, OrElse.orElse, Option.orElse]
  · by_cases h' : z = 0
    · subst h'; simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse]
    · simp [firstSome, h, h', HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-! ## Integer helpers -/

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

theorem is_pow2_eq {z : Int} (h : Bitvec.is_pow2 z = true) : z = 2 ^ (log2 z).toNat ∧ 0 ≤ log2 z := by
  unfold Bitvec.is_pow2 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h0, h1⟩ := h
  simp only [popcount] at h1
  have h1' : popcountNat z.toNat = 1 := by exact_mod_cast h1
  obtain ⟨j, hj⟩ := popcountNat_eq_one h1'
  have e1 : ((2 ^ j : Nat) : Int) = (2 : Int) ^ j := by push_cast; rfl
  simp only [log2, hj, Nat.log2_two_pow, Int.toNat_natCast]
  omega

theorem is_pow2_exists {z : Int} (h : Bitvec.is_pow2 z = true) : ∃ k : Nat, z = 2 ^ k :=
  ⟨_, (is_pow2_eq h).1⟩

@[simp] theorem log2_two_pow (k : Nat) : log2 ((2 : Int) ^ k) = k := by
  rw [show (2 : Int) ^ k = ((2 ^ k : Nat) : Int) by push_cast; rfl, log2, Int.toNat_natCast,
    Nat.log2_two_pow]

theorem lt_two_pow_log2 {z w : Int} (hz : 0 < z) (h : log2 z < w) : z < 2 ^ w.toNat := by
  have hl := Nat.lt_log2_self (n := z.toNat)
  have hle : 2 ^ (Nat.log2 z.toNat + 1) ≤ 2 ^ w.toNat :=
    Nat.pow_le_pow_right (by omega) (by simp only [log2] at h; omega)
  have : ((z.toNat : Nat) : Int) < ((2 ^ w.toNat : Nat) : Int) := by exact_mod_cast (by omega)
  push_cast at this; omega

theorem is_bv_iff {t : Ty} : Bitvec.is_bv t = true ↔ ∃ n, t = .TBitVector n := by
  cases t <;> simp [Bitvec.is_bv, firstSome]

theorem WT_mk_masked {n z : Int} : (mk_masked n z).WT ↔ 0 < n := by
  refine ⟨fun w => ?_, mk_masked_WT⟩
  obtain ⟨k, hk, h, -⟩ := WT_bitVec.1 w
  simp at h; omega

/-! ## Boolean literals -/

@[simp] theorem of_bool_WT (b : Bool) : (Bool.of_bool b).WT := by cases b <;> simp [Bool.of_bool]
@[simp] theorem of_bool_ty (b : Bool) : (Bool.of_bool b).ty = .TBool := by cases b <;> rfl
theorem of_bool_eq (b : Bool) : Bool.of_bool b = .mk (.Bool b) .TBool := by
  cases b <;> rfl

@[simp] theorem denB_of_bool {FS ρ} (b : Bool) : denB FS ρ (Bool.of_bool b) = some b := by
  cases b <;> rfl
@[simp] theorem eval_of_bool {FS ρ} (b : Bool) : eval FS ρ (Bool.of_bool b) = some (.bool b) := by
  cases b <;> simp [Bool.of_bool]


/-! ## `Nonzero` -/

theorem nonzero_bitVec {z : Int} {t : Ty} (hz : z ≠ 0) (w : (Term.mk (.BitVec z) t).WT) :
    Nonzero (.mk (.BitVec z) t) := by
  intro FS ρ n x h
  obtain ⟨k, hk, ht, h0, h1⟩ := WT_bitVec.1 w
  rw [eval_bitVec' w ht] at h
  simp only [Option.some.injEq, Val.bv.injEq, heq_eq_eq] at h
  obtain ⟨rfl, rfl⟩ := h
  intro e
  have := congrArg BitVec.toNat e
  simp only [Int.toNat_natCast] at this
  rw [toNat_ofInt_of_lt h0 h1] at this
  simp at this
  omega

theorem nonzero_mk_masked {n z : Int} (hn : 0 < n) (hz : z % 2 ^ n.toNat ≠ 0) :
    Nonzero (mk_masked n z) := by
  intro FS ρ m x h
  rw [eval_mk_masked hn] at h
  simp only [Option.some.injEq, Val.bv.injEq, heq_eq_eq] at h
  obtain ⟨rfl, rfl⟩ := h
  intro e
  have h2 : (0 : Int) < 2 ^ n.toNat := Int.pow_pos (by decide)
  have h3 := Int.emod_nonneg z (Int.ne_of_gt h2)
  have h4 : (BitVec.ofInt n.toNat z).toNat = 0 := by rw [e]; rfl
  rw [BitVec.toNat_ofInt] at h4
  have e5 : ((2 ^ n.toNat : Nat) : Int) = 2 ^ n.toNat := by push_cast; rfl
  rw [e5] at h4
  omega

theorem ne_zero_of_nonzero_bitVec {FS : FloatSem} {z : Int} {N : Nat} {t : Ty} (ht : t = .TBitVector N)
    (hN : 0 < N) (h0 : 0 ≤ z) (h1 : z < 2 ^ N) (hs : Nonzero (.mk (.BitVec z) t)) : z ≠ 0 := by
  intro hz
  subst hz
  have w : (Term.mk (.BitVec 0) t).WT := WT_bitVec.2 ⟨N, hN, ht, h0, h1⟩
  exact hs FS ⟨fun _ => none⟩ N 0#N (by rw [eval_bitVec' w ht]; simp) rfl

/-- The divisor `mk_masked (Bitvec.size x) z` of the rule `Bitvec.div.zext`, which divides the extension of
`x` by the literal `z`, is not zero. -/
theorem nonzero_zext_masked {FS : FloatSem} {signed : Bool} {by_ z : Int} {x : Term} {t5 t7 : Ty}
    (kw : (sem FS).WT (Bitvec.div.spec signed (.mk (.Op1 (.BvExtend false by_) x) t5)
      (.mk (.BitVec z) t7)))
    (hs : Nonzero (.mk (.BitVec z) t7)) (hg : Bitvec.msb_of (.mk (.BitVec z) t7) < Bitvec.size x) :
    Nonzero (mk_masked (Bitvec.size x) z) := by
  simp only [sem, Bitvec.div.spec, Term.WT, Op2.WT, Op1.WT] at kw
  kanon_split
  rename_i N _ _ W hN hW ht hx h0 h1 _ _
  have hz := ne_zero_of_nonzero_bitVec (FS := FS) ht hN h0 h1 hs
  rw [msb_of_lit, size_eq, hx, size_of_ty_bitVector] at hg
  have hpos : 0 < z := by omega
  simp only [hpos, ite_true] at hg
  have hlt : z < 2 ^ W.toNat := lt_two_pow_log2 hpos hg
  rw [size_eq, hx, size_of_ty_bitVector]
  refine nonzero_mk_masked hW ?_
  rw [Int.emod_eq_of_lt h0 hlt]
  exact hz

end Kanon.Lib
