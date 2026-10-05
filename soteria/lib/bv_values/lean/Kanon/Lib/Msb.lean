import Kanon.Lib.Float
import Kanon.Lib.Tactic

/-! The values of a bit-vector term are below `2 ^ (msb_of v + 1)`. -/

namespace Kanon.Lib

open Classical

variable {FS : FloatSem}

theorem srem_le_of_msb {n : Nat} (x y : BitVec n) (hx : x.msb = false) : (x.srem y).toNat ≤ x.toNat := by
  rw [BitVec.toNat_srem, hx]; cases y.msb <;> exact Nat.mod_le _ _

theorem smod_lt_of_msb {n : Nat} (x y : BitVec n) (hy : y.msb = false) (hy0 : 0 < y.toNat) :
    (x.smod y).toNat < y.toNat := by
  have hu : ((-x).umod y).toNat < y.toNat := BitVec.umod_lt _ hy0
  rw [BitVec.toNat_smod, hy]
  cases x.msb
  · exact BitVec.umod_lt _ hy0
  · simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.zero_mod]
    split
    · omega
    · rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 (by omega))]; omega

theorem lt_pow_of_lt {m : Nat} {z K : Int} (hz : 1 < z) (hm : (m : Int) < z)
    (hK : log2 (z - 1) ≤ K) : m < 2 ^ (K + 1).toNat := by
  have := lt_two_pow_log2 (z := z - 1) (w := K + 1) (by omega) (by omega)
  have h' : (m : Int) < ((2 ^ (K + 1).toNat : Nat) : Int) := by push_cast; omega
  exact_mod_cast h'

/-- [msb_of] bounds the value of a bit-vector. -/
theorem den_msb_aux {ρ} (s : Nat) : ∀ v : Term, sizeOf v < s → v.WT → ∀ {n : Nat},
    v.ty = .TBitVector n → ∀ (x : BitVec n), den FS ρ n v = some x → ∀ k : Int, msb_of v ≤ k →
    x.toNat < 2 ^ (k + 1).toNat := by
  induction s with
  | zero => intro v h; omega
  | succ s ih =>
    intro v hs w n hT x e k hk
    have dflt : size v - 1 ≤ k → x.toNat < 2 ^ (k + 1).toNat := by
      intro h
      simp only [size_eq, hT, size_of_ty_bitVector] at h
      exact Nat.lt_of_lt_of_le x.isLt
        (Nat.pow_le_pow_right (by omega) (by omega))
    rw [msb_of.eq_def] at hk
    rcases v with ⟨kd, T⟩
    simp only [Term.ty_mk] at hT; subst hT
    have dflt' : (n : Int) - 1 ≤ k → x.toNat < 2 ^ (k + 1).toNat := fun h =>
      Nat.lt_of_lt_of_le x.isLt
        (Nat.pow_le_pow_right (by omega) (by omega))
    cases kd
    case BitVec z =>
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
    case Op2 op a b =>
      cases op
      case BitAnd =>
        simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse, zmin] at hk
        have ⟨w1, wa, wb⟩ := WT_op2.1 w
        simp only [Op2.WT] at w1
        obtain ⟨⟨_, _, ha⟩, hb, ht⟩ := w1
        simp only [den] at e
        cases ea : den FS ρ n a <;> cases eb : den FS ρ n b <;> rw [ea, eb] at e <;> simp at e
        subst e; rw [BitVec.toNat_and]
        split at hk
        · exact Nat.lt_of_le_of_lt Nat.and_le_left
            (ih a (by simp at hs; omega) wa (by simp_all) _ ea k hk)
        · exact Nat.lt_of_le_of_lt Nat.and_le_right
            (ih b (by simp at hs; omega) wb (by simp_all) _ eb k hk)
      case Rem sg =>
        have ⟨w1, wa, wb⟩ := WT_op2.1 w
        simp only [Op2.WT] at w1
        obtain ⟨⟨_, _, ha⟩, hb, ht⟩ := w1
        simp only [den] at e
        cases ea : den FS ρ n a <;> cases eb : den FS ρ n b <;> rw [ea, eb] at e <;>
          simp [binOp] at e
        subst e
        rename_i xa xb
        rcases a with ⟨ka, Ta⟩
        rcases b with ⟨kb, Tb⟩
        simp only [Term.ty_mk] at ha hb ht
        subst ht; subst hb
        cases sg
        · cases kb
          case BitVec z =>
            by_cases hz : 1 < z
            · simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse, hz] at hk
              obtain ⟨_, h1, h2⟩ := WT_bitVec_bv.1 wb
              simp only [den, Option.some.injEq] at eb; subst eb
              have hy := toNat_ofInt_of_lt (n := n) h1 (by simpa using h2)
              have hlt : (xa.umod (BitVec.ofInt n z)).toNat < _ :=
                BitVec.umod_lt _ (show 0 < (BitVec.ofInt n z).toNat by omega)
              rw [hy] at hlt
              simp only [Bool.false_eq_true, ite_false]
              have hlt' : ((xa.umod (BitVec.ofInt n z)).toNat : Int) < z := by omega
              exact lt_pow_of_lt hz hlt' hk
            · simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse, hz] at hk
              exact dflt' hk
          all_goals
            simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hk
            exact dflt' hk
        · cases ka
          case BitVec z =>
            by_cases hz : 0 < z ∧ z < (2 : Int) ^ (n - 1)
            · simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse, z_lsl, hz] at hk
              obtain ⟨_, h1, h2⟩ := WT_bitVec_bv.1 wa
              simp only [den, Option.some.injEq] at ea; subst ea
              have hx := toNat_ofInt_of_lt (n := n) h1 (by simpa using h2)
              have hp : (2 : Int) ^ (n - 1) = ((2 ^ (n - 1) : Nat) : Int) := by push_cast; rfl
              have hm : (BitVec.ofInt n z).msb = false := by rw [BitVec.msb_eq_decide, hx]; simp; omega
              have hle := srem_le_of_msb _ xb hm
              rw [hx] at hle
              simp only [ite_true]
              have := lt_two_pow_log2 (z := z) (w := k + 1) hz.1 (by omega)
              have h' : (((BitVec.ofInt n z).srem xb).toNat : Int) <
                  ((2 ^ (k + 1).toNat : Nat) : Int) := by push_cast; omega
              exact_mod_cast h'
            · simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse, z_lsl, hz] at hk
              exact dflt' hk
          all_goals
            simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hk
            exact dflt' hk
      case Mod =>
        have ⟨w1, wa, wb⟩ := WT_op2.1 w
        simp only [Op2.WT] at w1
        obtain ⟨⟨_, _, ha⟩, hb, ht⟩ := w1
        simp only [den] at e
        cases ea : den FS ρ n a <;> cases eb : den FS ρ n b <;> rw [ea, eb] at e <;>
          simp [binOp] at e
        subst e
        rename_i xa xb
        rcases b with ⟨kb, Tb⟩
        simp only [Term.ty_mk] at hb
        rw [← ht] at hb; subst hb
        cases kb
        case BitVec z =>
          by_cases hz : 1 < z ∧ z < (2 : Int) ^ (n - 1)
          · simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse, z_lsl, hz] at hk
            obtain ⟨_, h1, h2⟩ := WT_bitVec_bv.1 wb
            simp only [den, Option.some.injEq] at eb; subst eb
            have hy := toNat_ofInt_of_lt (n := n) h1 (by simpa using h2)
            have hp : (2 : Int) ^ (n - 1) = ((2 ^ (n - 1) : Nat) : Int) := by push_cast; rfl
            have hm : (BitVec.ofInt n z).msb = false := by rw [BitVec.msb_eq_decide, hy]; simp; omega
            have hlt := smod_lt_of_msb xa _ hm (by rw [hy]; omega)
            rw [hy] at hlt
            exact lt_pow_of_lt hz.1 (by omega) hk
          · simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse, z_lsl, hz] at hk
            exact dflt' hk
        all_goals
          simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hk
          exact dflt' hk
      all_goals
        simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hk
        exact dflt hk
    case Op3 op g l r =>
      cases op
      case Ite =>
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
    case Op1 op u =>
      cases op
      case BvExtend sg k' =>
        cases sg
        · simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hk
          have ⟨w1, wu⟩ := WT_op1.1 w
          simp only [Op1.WT] at w1
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

theorem den_msb {ρ v n x} (w : v.WT) (hT : v.ty = .TBitVector (n : Int))
    (e : den FS ρ n v = some x) : x.toNat < 2 ^ (msb_of v + 1).toNat :=
  den_msb_aux _ v (Nat.lt_succ_self _) w hT x e _ (Int.le_refl _)

end Kanon.Lib
