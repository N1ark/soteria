import BitvecMod.Proofs.CompareBound
import BitvecMod.Statements.Bitvec.lt_zero
import BitvecMod.Statements.Bool.and_
import BitvecMod.Statements.Bool.eq
import BitvecMod.Statements.Bool.ite
import BitvecMod.Statements.Bool.not_
import BitvecMod.Statements.Bool.or_
import BitvecMod.Statements.Bool.sure_neq

/-!
# The proofs of the comparisons and of the bool rules on bit-vectors

The arms that `kanon_auto` does not prove, by `cmp_rule` (`CompareLib.lean`) or by
hand. Literals of the same sort are equal exactly when their integers are, as
these are in the range of their width (`sure_neq`).
-/

noncomputable section

namespace BitvecMod

open Classical Kanon

section
variable {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [Lang S] [Typed S]

/-- The value of a literal, of the width of its sort. -/
theorem ev_lit {ρ : S.Env} {z : Int} {t : S.Ty} {loc : Bool}
    (w : S.WT (mk (if loc then .LocLit z else .BitVec z) t)) :
    ∃ k : Nat, 0 < k ∧ t = sort (if loc then .TLoc k else .TBitVector k) ∧ 0 ≤ z ∧ z < 2 ^ k ∧
      S.ev ρ (mk (if loc then .LocLit z else .BitVec z) t) = some (bv k (BitVec.ofInt k z)) := by
  rw [WT_mk] at w
  cases loc <;>
  · simp only [Bool.false_eq_true, ite_false, ite_true, Node.wt, bv_wf] at w
    obtain ⟨⟨⟨n, hn, rfl⟩, hz⟩, -⟩ := w
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hn)
    obtain ⟨h0, h1⟩ := hz k (by simp)
    refine ⟨k, by omega, by simp, h0, by simpa using h1, ?_⟩
    simp only [Bool.false_eq_true, ite_false, ite_true, ev_mk, Node.map, Node.eval, ofBV_some]
    rw [width_eq ρ rfl (by simp) hn]
    simp

/-- Literals of the same sort with different integers have different values. -/
theorem lit_sure_neq {loc : Bool} {a b : Int} {ta tb : S.Ty} (h : a ≠ b)
    (wa : S.WT (mk (if loc then .LocLit a else .BitVec a) ta))
    (wb : S.WT (mk (if loc then .LocLit b else .BitVec b) tb)) (hty : ta = tb) (ρ : S.Env) (u : S.Val)
    (ea : S.ev ρ (mk (if loc then .LocLit a else .BitVec a) ta) = some u)
    (eb : S.ev ρ (mk (if loc then .LocLit b else .BitVec b) tb) = some u) : False := by
  obtain ⟨k, -, rfl, ha0, ha1, ea'⟩ := ev_lit (ρ := ρ) wa
  obtain ⟨k', -, hk, hb0, hb1, eb'⟩ := ev_lit (ρ := ρ) wb
  subst hty
  have hk' : k' = k := by cases loc <;> simp at hk <;> omega
  subst hk'
  rw [ea] at ea'; rw [eb] at eb'
  have := ea'.symm.trans eb'
  simp only [Option.some.injEq, bv, Embed.inj_eq_iff, Sigma.mk.injEq, heq_eq_eq, true_and] at this
  have := congrArg BitVec.toNat this
  rw [BitvecMod.toNat_ofInt_of_lt ha0 (by exact_mod_cast ha1),
    BitvecMod.toNat_ofInt_of_lt hb0 (by exact_mod_cast hb1)] at this
  omega

end

@[kanon_arm] theorem Bool.sure_neq.c1.proof : Bool.sure_neq.c1.Stmt := by
  intro S _ _ _ _ _ _ a b r h
  simp only [Bool.sure_neq.c1] at h
  split at h
  · rename_i x y ha hb
    cases h
    intro hr wa wb hty ρ u ea eb
    obtain ⟨t, rfl⟩ := Kanon.NodeEmbed.exists_of_proj _ ha
    obtain ⟨t', rfl⟩ := Kanon.NodeEmbed.exists_of_proj _ hb
    simp only [ty_mk] at hty
    exact lit_sure_neq (loc := false) (by simpa using hr) wa wb hty ρ u ea eb
  · cases h

@[kanon_arm] theorem Bool.sure_neq.c2.proof : Bool.sure_neq.c2.Stmt := by
  intro S _ _ _ _ _ _ a b r h
  simp only [Bool.sure_neq.c2] at h
  split at h
  · rename_i x y ha hb
    cases h
    intro hr wa wb hty ρ u ea eb
    obtain ⟨t, rfl⟩ := Kanon.NodeEmbed.exists_of_proj _ ha
    obtain ⟨t', rfl⟩ := Kanon.NodeEmbed.exists_of_proj _ hb
    simp only [ty_mk] at hty
    exact lit_sure_neq (loc := true) (by simpa using hr) wa wb hty ρ u ea eb
  · cases h

/-- A sign test on a term refines the sign test of a term of the same value. -/
theorem lt_zero_congr_ev {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [Lang S] {a b : S.Term} {ρ : S.Env}
    (h : S.ev ρ a = S.ev ρ b) (hty : S.ty a = S.ty b) :
    S.ev ρ (Bitvec.lt_zero.spec a) = S.ev ρ (Bitvec.lt_zero.spec b) := by
  simp only [Bitvec.lt_zero.spec, Bitvec.size, hty, ev_mk, Node.map, Node.eval, h]

@[kanon_arm] theorem Bitvec.lt_zero.r_ite.main.proof : Bitvec.lt_zero.r_ite.main.Stmt := by
  intro S _ _ _ _ _ _ O hO g l r t
  dsimp only
  split
  · rename_i h
    have hl := hO.bitvec_lt_zero l
    have hr := hO.bitvec_lt_zero r
    rw [← of_decide_eq_true h] at hr
    refine Kanon.Sem.Refines.of_WT fun w => ?_
    have w0 := w
    simp only [Bitvec.lt_zero.spec, WT_mk, Node.wt, Node.All] at w0
    obtain ⟨⟨⟨n, hn, hite⟩, -, -⟩, wite, wz⟩ := w0
    have wite' := wite
    rw [KanonBool.WT_mk] at wite'
    obtain ⟨⟨hg, hrl, rfl⟩, wg, wl, wr⟩ := wite'
    simp only [KanonBool.ty_mk] at hite
    have wsl : S.WT (Bitvec.lt_zero.spec l) := by
      simp only [Bitvec.lt_zero.spec, WT_mk, Node.wt, Node.All, KanonBool.ty_mk] at w ⊢
      simp only [Bitvec.size, KanonBool.ty_mk] at w ⊢
      exact ⟨w.1, wl, w.2.2⟩
    have wsr : S.WT (Bitvec.lt_zero.spec r) := by
      simp only [Bitvec.lt_zero.spec, WT_mk, Node.wt, Node.All, KanonBool.ty_mk] at w ⊢
      simp only [Bitvec.size, KanonBool.ty_mk, hrl] at w ⊢
      exact ⟨w.1, wr, w.2.2⟩
    refine Kanon.Sem.Refines.intro (fun _ => ⟨(hl.syn wsl).1, ?_⟩) (fun ρ v _ _ e => ?_)
    · rw [(hl.syn wsl).2]; simp [Bitvec.lt_zero.spec]
    · have ev_ite : S.ev ρ (KanonBool.mk (.Ite g l r) (S.ty l)) =
          KanonBool.pite KanonBool.Values.vbool.inj (S.ev ρ g) (S.ev ρ l) (S.ev ρ r) := by
        rw [KanonBool.ev_mk]; rfl
      unfold KanonBool.pite at ev_ite
      split at ev_ite
      · have := lt_zero_congr_ev (ρ := ρ) ev_ite (by simp)
        rw [this] at e
        exact hl.ev wsl ρ v e
      · split at ev_ite
        · have := lt_zero_congr_ev (ρ := ρ) ev_ite (by simp [hrl])
          rw [this] at e
          exact hr.ev wsr ρ v e
        · simp only [Bitvec.lt_zero.spec, ev_mk, Node.map, Node.eval, ev_ite, withW_none] at e
          cases e
  · exact Kanon.Sem.Refines.refl

/-! The equalities of two adjacent extracts of a term, merged into one
(`Bool.and_.r_eq_extracts`). -/

/-- An extract of an extract. -/
theorem cmp_extract_extract {n k m s t : Nat} (X : BitVec n) (h : t + k ≤ m) :
    (X.extractLsb' s m).extractLsb' t k = X.extractLsb' (s + t) k := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb']
  have : t + i < m := by omega
  simp [this, Nat.add_assoc]

/-- Two adjacent extracts of `x`, concatenated: the extract of their union, with the
width of its sort `c`. -/
theorem cmp_extracts_pos {n k m c s p : Nat} {X : BitVec n} {a : BitVec k} {b : BitVec m}
    (hc : k + m = c) (ha : a = X.extractLsb' p k) (hb : b = X.extractLsb' s m) (hp : p = s + m) :
    k + m = c ∧ a ++ b ≍ X.extractLsb' s c := by
  subst hc hp ha hb
  exact ⟨rfl, heq_of_eq (BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' rfl)⟩

/-- A concatenation is not an extract when its low part is not. -/
theorem cmp_extracts_neg_b {n k m c s : Nat} {X : BitVec n} {a : BitVec k} {b : BitVec m}
    (hb : ¬b = X.extractLsb' s m) :
    ¬(k + m = c ∧ a ++ b ≍ X.extractLsb' s c) := by
  rintro ⟨rfl, h⟩
  apply hb
  have := congrArg (·.extractLsb' 0 m) (eq_of_heq h)
  simp only [BitVec.extractLsb'_append_eq_right] at this
  rw [this, cmp_extract_extract _ (by omega), Nat.add_zero]

/-- A concatenation is not an extract when its high part is not. -/
theorem cmp_extracts_neg_a {n k m c s p : Nat} {X : BitVec n} {a : BitVec k} {b : BitVec m}
    (ha : ¬a = X.extractLsb' p k) (hp : p = s + m) :
    ¬(k + m = c ∧ a ++ b ≍ X.extractLsb' s c) := by
  rintro ⟨rfl, h⟩
  apply ha
  have := congrArg (·.extractLsb' m k) (eq_of_heq h)
  simp only [BitVec.extractLsb'_append_eq_left] at this
  rw [this, cmp_extract_extract _ (by omega), hp]

@[kanon_arm] theorem Bool.and_.r_eq_extracts.main.proof : Bool.and_.r_eq_extracts.main.Stmt := by
  cmp_lift
  all_goals kanon_on_refines (
    refine Kanon.Sem.Refines.intro ?_ ?_
    · cmp_wt
      all_goals refine ⟨⟨_, ?_, _, ?_, rfl, rfl, rfl⟩, ?_⟩ <;> omega
    · cmp_sem_pre
      all_goals first
        | exact cmp_extracts_pos (by omega) (by assumption) (by assumption) (by omega)
        | exact cmp_extracts_neg_b (by assumption)
        | exact cmp_extracts_neg_a (by assumption) (by omega))

/-! The other arms of the bool rules and of `Bitvec.lt_zero`, by `cmp_rule`
(`CompareLib.lean`) or a closer of their own. -/

@[kanon_arm] theorem Bitvec.lt_zero.r_concat.main.proof : Bitvec.lt_zero.r_concat.main.Stmt := by cmp_msb_rule

@[kanon_arm] theorem Bitvec.lt_zero.r_not.main.proof : Bitvec.lt_zero.r_not.main.Stmt := by cmp_auto

@[kanon_arm] theorem Bitvec.lt_zero.r_of_bool.main.proof : Bitvec.lt_zero.r_of_bool.main.Stmt := by cmp_auto

@[kanon_arm] theorem Bitvec.lt_zero.r_sext.main.proof : Bitvec.lt_zero.r_sext.main.Stmt := by cmp_msb_rule

@[kanon_arm] theorem Bitvec.lt_zero.r_srem.main.proof : Bitvec.lt_zero.r_srem.main.Stmt := by cmp_msb_rule

@[kanon_arm] theorem Bitvec.lt_zero.r_zext.main.proof : Bitvec.lt_zero.r_zext.main.Stmt := by cmp_msb_rule

@[kanon_arm] theorem Bool.and_.r_lower_bounds.leq_leq.proof : Bool.and_.r_lower_bounds.leq_leq.Stmt := by bnd_arm

@[kanon_arm] theorem Bool.and_.r_lower_bounds.leq_lt.proof : Bool.and_.r_lower_bounds.leq_lt.Stmt := by bnd_arm

@[kanon_arm] theorem Bool.and_.r_lower_bounds.lt_leq.proof : Bool.and_.r_lower_bounds.lt_leq.Stmt := by bnd_arm

@[kanon_arm] theorem Bool.and_.r_lower_bounds.lt_lt.proof : Bool.and_.r_lower_bounds.lt_lt.Stmt := by bnd_arm

@[kanon_arm] theorem Bool.and_.r_upper_bounds.leq_leq.proof : Bool.and_.r_upper_bounds.leq_leq.Stmt := by bnd_arm

@[kanon_arm] theorem Bool.and_.r_upper_bounds.leq_lt.proof : Bool.and_.r_upper_bounds.leq_lt.Stmt := by bnd_arm

@[kanon_arm] theorem Bool.and_.r_upper_bounds.lt_leq.proof : Bool.and_.r_upper_bounds.lt_leq.Stmt := by bnd_arm

@[kanon_arm] theorem Bool.and_.r_upper_bounds.lt_lt.proof : Bool.and_.r_upper_bounds.lt_lt.Stmt := by bnd_arm

@[kanon_arm] theorem Bool.eq.r_add_add.main.proof : Bool.eq.r_add_add.main.Stmt := by cmp_auto

@[kanon_arm] theorem Bool.eq.r_add_const.main.proof : Bool.eq.r_add_const.main.Stmt := by cmp_auto

@[kanon_arm] theorem Bool.eq.r_and_mask.main.proof : Bool.eq.r_and_mask.main.Stmt := by
  cmp_lift
  cmp_halves
  all_goals exact Cmp.and_mask_ne (by assumption) (by assumption) (by assumption) _

@[kanon_arm] theorem Bool.eq.r_bvs.bitVec_bitVec.proof : Bool.eq.r_bvs.bitVec_bitVec.Stmt := by cmp_auto

@[kanon_arm] theorem Bool.eq.r_bvs.locLit_locLit.proof : Bool.eq.r_bvs.locLit_locLit.Stmt := by cmp_auto

@[kanon_arm] theorem Bool.eq.r_concat_concat.main.proof : Bool.eq.r_concat_concat.main.Stmt := by cmp_auto

@[kanon_arm] theorem Bool.eq.r_concat_const.main.proof : Bool.eq.r_concat_const.main.Stmt := by cmp_auto

@[kanon_arm] theorem Bool.eq.r_ite_concat.main.proof : Bool.eq.r_ite_concat.main.Stmt := by cmp_auto

@[kanon_arm] theorem Bool.eq.r_mul_cancel.main.proof : Bool.eq.r_mul_cancel.main.Stmt := by
  cmp_lift
  cmp_halves
  all_goals first
    | exact Cmp.mul_cancel_odd' (by assumption) (by assumption) (by assumption)
    | (apply Cmp.mul_cancel_ovf (by assumption) (by assumption) (by assumption)
       simp_all)

@[kanon_arm] theorem Bool.eq.r_neg.main.proof : Bool.eq.r_neg.main.Stmt := by cmp_auto

@[kanon_arm] theorem Bool.eq.r_not.main.proof : Bool.eq.r_not.main.Stmt := by cmp_auto

@[kanon_arm] theorem Bool.eq.r_of_bool_const.main.proof : Bool.eq.r_of_bool_const.main.Stmt := by cmp_auto

@[kanon_arm] theorem Bool.eq.r_of_bools.main.proof : Bool.eq.r_of_bools.main.Stmt := by cmp_auto

@[kanon_arm] theorem Bool.eq.r_or_zero.main.proof : Bool.eq.r_or_zero.main.Stmt := by cmp_auto

@[kanon_arm] theorem Bool.eq.r_self_add.main.proof : Bool.eq.r_self_add.main.Stmt := by cmp_auto

@[kanon_arm] theorem Bool.eq.r_sub_const1.main.proof : Bool.eq.r_sub_const1.main.Stmt := by cmp_auto

@[kanon_arm] theorem Bool.eq.r_sub_const2.main.proof : Bool.eq.r_sub_const2.main.Stmt := by cmp_auto

@[kanon_arm] theorem Bool.eq.r_zext_const.main.proof : Bool.eq.r_zext_const.main.Stmt := by cmp_auto

@[kanon_arm] theorem Bool.ite.r_bv_of_bool.main.proof : Bool.ite.r_bv_of_bool.main.Stmt := by cmp_auto

@[kanon_arm] theorem Bool.not_.r_eq_bit.main.proof : Bool.not_.r_eq_bit.main.Stmt := by cmp_auto

@[kanon_arm] theorem Bool.not_.r_leq.main.proof : Bool.not_.r_leq.main.Stmt := by cmp_auto

@[kanon_arm] theorem Bool.not_.r_lt.main.proof : Bool.not_.r_lt.main.Stmt := by cmp_auto

@[kanon_arm] theorem Bool.or_.r_complementary.leq_leq.proof : Bool.or_.r_complementary.leq_leq.Stmt := by bnd_arm

@[kanon_arm] theorem Bool.or_.r_complementary.leq_lt.proof : Bool.or_.r_complementary.leq_lt.Stmt := by bnd_arm

@[kanon_arm] theorem Bool.or_.r_complementary.lt_leq.proof : Bool.or_.r_complementary.lt_leq.Stmt := by bnd_arm

@[kanon_arm] theorem Bool.or_.r_complementary.lt_lt.proof : Bool.or_.r_complementary.lt_lt.Stmt := by bnd_arm

@[kanon_arm] theorem Bool.or_.r_lower_bounds.leq_leq.proof : Bool.or_.r_lower_bounds.leq_leq.Stmt := by bnd_arm

@[kanon_arm] theorem Bool.or_.r_lower_bounds.leq_lt.proof : Bool.or_.r_lower_bounds.leq_lt.Stmt := by bnd_arm

@[kanon_arm] theorem Bool.or_.r_lower_bounds.lt_leq.proof : Bool.or_.r_lower_bounds.lt_leq.Stmt := by bnd_arm

@[kanon_arm] theorem Bool.or_.r_lower_bounds.lt_lt.proof : Bool.or_.r_lower_bounds.lt_lt.Stmt := by bnd_arm

@[kanon_arm] theorem Bool.or_.r_lower_eq.leq.proof : Bool.or_.r_lower_eq.leq.Stmt := by bnd_arm

@[kanon_arm] theorem Bool.or_.r_lower_eq.lt.proof : Bool.or_.r_lower_eq.lt.Stmt := by bnd_arm

@[kanon_arm] theorem Bool.or_.r_lt_leq.main.proof : Bool.or_.r_lt_leq.main.Stmt := by cmp_auto

@[kanon_arm] theorem Bool.or_.r_lt_lt.main.proof : Bool.or_.r_lt_lt.main.Stmt := by cmp_auto

@[kanon_arm] theorem Bool.or_.r_upper_bounds.leq_leq.proof : Bool.or_.r_upper_bounds.leq_leq.Stmt := by bnd_arm

@[kanon_arm] theorem Bool.or_.r_upper_bounds.leq_lt.proof : Bool.or_.r_upper_bounds.leq_lt.Stmt := by bnd_arm

@[kanon_arm] theorem Bool.or_.r_upper_bounds.lt_leq.proof : Bool.or_.r_upper_bounds.lt_leq.Stmt := by bnd_arm

@[kanon_arm] theorem Bool.or_.r_upper_bounds.lt_lt.proof : Bool.or_.r_upper_bounds.lt_lt.Stmt := by bnd_arm

@[kanon_arm] theorem Bool.or_.r_upper_eq.leq.proof : Bool.or_.r_upper_eq.leq.Stmt := by bnd_arm

@[kanon_arm] theorem Bool.or_.r_upper_eq.lt.proof : Bool.or_.r_upper_eq.lt.Stmt := by bnd_arm

end BitvecMod
