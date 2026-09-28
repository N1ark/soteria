import Bvr.Lib.Float
import Bvr.Lib.Tactic

/-! The values of a bit-vector term are below `2 ^ (msb_of v + 1)`. -/

namespace Bvr.Lib

open Classical

variable {FS : FloatSem}

theorem pow_le_of_le {a b : Int} (h : a ≤ b) : 2 ^ a.toNat ≤ 2 ^ b.toNat :=
  Nat.pow_le_pow_right (by omega) (by omega)

/-- [msb_of] bounds the value of a bit-vector. -/
theorem den_msb_aux {ρ} (s : Nat) : ∀ v : Term, sizeOf v < s → v.WT → ∀ {n : Nat},
    v.ty = .bitVector n → ∀ (x : BitVec n), den FS ρ n v = some x → ∀ k : Int, msb_of v ≤ k →
    x.toNat < 2 ^ (k + 1).toNat := by
  induction s with
  | zero => intro v h; omega
  | succ s ih =>
    intro v hs w n hT x e k hk
    have dflt : size v - 1 ≤ k → x.toNat < 2 ^ (k + 1).toNat := by
      intro h
      simp only [size_eq, hT, size_of_ty_bitVector] at h
      exact Nat.lt_of_lt_of_le x.isLt
        (by have := pow_le_of_le (a := n) (b := k + 1) (by omega); simpa using this)
    rw [msb_of.eq_def] at hk
    rcases v with ⟨kd, T⟩
    simp only [Term.ty_mk] at hT; subst hT
    cases kd
    case bitVec z =>
      obtain ⟨_, h1, h2⟩ := WT_bitVec_bv.1 w
      simp only [den, Option.some.injEq] at e; subst e
      rw [toNat_ofInt_of_lt h1 (by simpa using h2)]
      by_cases hz : 0 < z
      · simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse, hz] at hk
        have := lt_two_pow_log2 hz (w := k + 1) (by omega)
        have h' : (z.toNat : Int) < ((2 ^ (k + 1).toNat : Nat) : Int) := by push_cast; omega
        exact_mod_cast h'
      · obtain rfl : z = 0 := by omega
        exact Nat.two_pow_pos _
    case binop op a b =>
      cases op
      case bitAnd =>
        simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse, zmin] at hk
        have ⟨w1, wa, wb⟩ := WT_binop.1 w
        simp only [Binop.WT, Ty.sort_eq] at w1
        obtain ⟨⟨_, _, ha⟩, hb, ht⟩ := w1
        simp only [den] at e
        cases ea : den FS ρ n a <;> cases eb : den FS ρ n b <;> rw [ea, eb] at e <;> simp at e
        subst e; rw [BitVec.toNat_and]
        split at hk
        · exact Nat.lt_of_le_of_lt Nat.and_le_left
            (ih a (by simp at hs; omega) wa (by simp_all) _ ea k hk)
        · exact Nat.lt_of_le_of_lt Nat.and_le_right
            (ih b (by simp at hs; omega) wb (by simp_all) _ eb k hk)
      all_goals
        simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hk
        exact dflt hk
    case triop op g l r =>
      cases op
      case ite =>
        simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse, zmax] at hk
        obtain ⟨_, h1, h2, wg, wl, wr⟩ := WT_ite.1 w
        simp only [den] at e
        split at hk <;>
        split at e <;> first
          | (simp at e; done)
          | exact ih _ (by simp at hs; omega) (by assumption) (by simp_all) _ e k (by omega)
      all_goals
        simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hk
        exact dflt hk
    case unop op u =>
      cases op
      case bvExtend sg k' =>
        cases sg
        · simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hk
          have ⟨w1, wu⟩ := WT_unop.1 w
          simp only [Unop.WT, Ty.sort_eq] at w1
          obtain ⟨m, hm, hu, _, _⟩ := w1
          obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hm)
          simp only [den, hu, Int.toNat_natCast, Bool.false_eq_true, ite_false] at e
          cases eu : den FS ρ m u <;> rw [eu] at e <;> simp at e
          subst e; rw [BitVec.toNat_setWidth]
          exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (ih u (by simp at hs; omega) wu hu _ eu k hk)
        · simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hk
          exact dflt hk
      all_goals
        simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hk
        exact dflt hk
    all_goals
      simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hk
      exact dflt hk

theorem den_msb {ρ v n x} (w : v.WT) (hT : v.ty = .bitVector (n : Int))
    (e : den FS ρ n v = some x) : x.toNat < 2 ^ (msb_of v + 1).toNat :=
  den_msb_aux _ v (Nat.lt_succ_self _) w hT x e _ (Int.le_refl _)

end Bvr.Lib
