import Bvr.Lemmas

/-! Bitwise operations, extraction, extension, concatenation, shifts and conversions. -/

namespace Bvr

open Classical

theorem bv_of_bool.r_true_.proof : bv_of_bool.r_true_.Stmt := by
  sorry

theorem bv_of_bool.r_false_.proof : bv_of_bool.r_false_.Stmt := by
  sorry

theorem bv_of_bool.r_default.proof : bv_of_bool.r_default.Stmt := by
  sorry

theorem bv_to_bool.r_lit.proof : bv_to_bool.r_lit.Stmt := by
  sorry

theorem bv_to_bool.r_of_bool.proof : bv_to_bool.r_of_bool.Stmt := by
  sorry

theorem bv_to_bool.r_default.proof : bv_to_bool.r_default.Stmt := by
  sorry

theorem bv_not_bool.r_lit.proof : bv_not_bool.r_lit.Stmt := by
  sorry

theorem bv_not_bool.r_of_bool.proof : bv_not_bool.r_of_bool.Stmt := by
  sorry

theorem bv_not_bool.r_default.proof : bv_not_bool.r_default.Stmt := by
  sorry

theorem bv_not.r_lit.proof : bv_not.r_lit.Stmt := by
  intro FS O hO v res h
  simp only [bv_not.r_lit] at h
  split at h <;> simp at h
  subst h
  rename_i z T
  have key : (Term.mk (.unop .bvNot (.mk (.bitVec z) T)) T).WT →
      ∃ n : Nat, 0 < n ∧ T = .bitVector n ∧ 0 ≤ z ∧ z < 2 ^ n := by
    intro w
    have ⟨w1, w2⟩ := WT_unop.1 w
    obtain ⟨n, hn, hT, h1, h2⟩ := WT_bitVec.1 w2
    simp [Unop.WT] at w1
    rcases hT with rfl | rfl
    · exact ⟨n, hn, rfl, h1, h2⟩
    · simp at w1
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨n, hn, rfl, _, _⟩ := key (by simpa [bv_not.spec] using w)
    exact ⟨mk_masked_WT (by simp [size_of_ty]; omega), by simp [bv_not.spec, size_of_ty]⟩
  · simp only [bv_not.spec, ty_eq, Term.ty_mk] at w e
    obtain ⟨n, hn, rfl, _, _⟩ := key w
    rw [eval_unop w, eval_bitVec' (WT_unop.1 w).2 (Or.inl rfl)] at e
    simp only [size_of_ty]
    rw [eval_mk_masked (by omega)]
    simp [evUnop] at e; subst e
    simp [BitVec.ofInt_zlognot]

theorem bv_not.r_ite.proof : bv_not.r_ite.Stmt := by
  intro FS O hO v r h
  simp only [bv_not.r_ite] at h
  split at h <;> simp at h
  subst h
  rename_i b l r0 T
  have hl : ∀ t, Refines FS (.mk (.unop .bvNot l) t) (O.bv_not l) := fun t =>
    Refines.trans (Refines.unop Refines.refl (fun w => by
      have := (WT_unop.1 w).1; simp [Unop.WT] at this ⊢; grind)) (hO.bv_not l)
  have hr : ∀ t, Refines FS (.mk (.unop .bvNot r0) t) (O.bv_not r0) := fun t =>
    Refines.trans (Refines.unop Refines.refl (fun w => by
      have := (WT_unop.1 w).1; simp [Unop.WT] at this ⊢; grind)) (hO.bv_not r0)
  refine Refines.trans Refines.unop_ite ?_
  refine Refines.trans ?_ (hO.b_ite _ _ _)
  refine Refines.ite Refines.refl (hl _) (hr _) (fun w => ?_)
  have ⟨h1, _, wa, _⟩ := WT_triop.1 w
  have := ((hl _).syn wa).2
  simp_all [b_ite.spec]

theorem bv_not.r_default.proof : bv_not.r_default.Stmt := by
  intro FS O hO v r h
  simp [bv_not.r_default] at h; subst h
  exact Refines.refl

theorem bv_and.r_lits.proof : bv_and.r_lits.Stmt := by
  sorry

theorem bv_and.r_zero_l.proof : bv_and.r_zero_l.Stmt := by
  sorry

theorem bv_and.r_zero_r.proof : bv_and.r_zero_r.Stmt := by
  sorry

theorem bv_and.r_ones_l.proof : bv_and.r_ones_l.Stmt := by
  sorry

theorem bv_and.r_ones_r.proof : bv_and.r_ones_r.Stmt := by
  sorry

theorem bv_and.r_lshr_mask.proof : bv_and.r_lshr_mask.Stmt := by
  sorry

theorem bv_and.r_ite_r.proof : bv_and.r_ite_r.Stmt := by
  sorry

theorem bv_and.r_ite_l.proof : bv_and.r_ite_l.Stmt := by
  sorry

theorem bv_and.r_masks.proof : bv_and.r_masks.Stmt := by
  sorry

theorem bv_and.r_mask_or_mask.proof : bv_and.r_mask_or_mask.Stmt := by
  sorry

theorem bv_and.r_mask_or.proof : bv_and.r_mask_or.Stmt := by
  sorry

theorem bv_and.r_right_mask.proof : bv_and.r_right_mask.Stmt := by
  sorry

theorem bv_and.r_of_bool_r.proof : bv_and.r_of_bool_r.Stmt := by
  sorry

theorem bv_and.r_of_bool_l.proof : bv_and.r_of_bool_l.Stmt := by
  sorry

theorem bv_and.r_of_bools.proof : bv_and.r_of_bools.Stmt := by
  sorry

theorem bv_and.r_ites.proof : bv_and.r_ites.Stmt := by
  sorry

theorem bv_and.r_default.proof : bv_and.r_default.Stmt := by
  sorry

theorem bv_or.r_lits.proof : bv_or.r_lits.Stmt := by
  sorry

theorem bv_or.r_zero_l.proof : bv_or.r_zero_l.Stmt := by
  sorry

theorem bv_or.r_zero_r.proof : bv_or.r_zero_r.Stmt := by
  sorry

theorem bv_or.r_same.proof : bv_or.r_same.Stmt := by
  sorry

theorem bv_or.r_mask_and.proof : bv_or.r_mask_and.Stmt := by
  sorry

theorem bv_or.r_masks.proof : bv_or.r_masks.Stmt := by
  sorry

theorem bv_or.r_extend_shl.proof : bv_or.r_extend_shl.Stmt := by
  sorry

theorem bv_or.r_of_bools.proof : bv_or.r_of_bools.Stmt := by
  sorry

theorem bv_or.r_default.proof : bv_or.r_default.Stmt := by
  sorry

theorem bv_xor.r_lits.proof : bv_xor.r_lits.Stmt := by
  sorry

theorem bv_xor.r_zero_l.proof : bv_xor.r_zero_l.Stmt := by
  sorry

theorem bv_xor.r_zero_r.proof : bv_xor.r_zero_r.Stmt := by
  sorry

theorem bv_xor.r_of_bools.proof : bv_xor.r_of_bools.Stmt := by
  sorry

theorem bv_xor.r_default.proof : bv_xor.r_default.Stmt := by
  sorry

theorem bv_extract.r_lit.proof : bv_extract.r_lit.Stmt := by
  sorry

theorem bv_extract.r_full.proof : bv_extract.r_full.Stmt := by
  sorry

theorem bv_extract.r_and_.proof : bv_extract.r_and_.Stmt := by
  sorry

theorem bv_extract.r_or_.proof : bv_extract.r_or_.Stmt := by
  sorry

theorem bv_extract.r_xor.proof : bv_extract.r_xor.Stmt := by
  sorry

theorem bv_extract.r_shl.proof : bv_extract.r_shl.Stmt := by
  sorry

theorem bv_extract.r_lshr.proof : bv_extract.r_lshr.Stmt := by
  sorry

theorem bv_extract.r_ite.proof : bv_extract.r_ite.Stmt := by
  sorry

theorem bv_extract.r_zext_high.proof : bv_extract.r_zext_high.Stmt := by
  sorry

theorem bv_extract.r_sext_bit.proof : bv_extract.r_sext_bit.Stmt := by
  sorry

theorem bv_extract.r_ext_low.proof : bv_extract.r_ext_low.Stmt := by
  sorry

theorem bv_extract.r_ext_orig.proof : bv_extract.r_ext_orig.Stmt := by
  sorry

theorem bv_extract.r_extract.proof : bv_extract.r_extract.Stmt := by
  sorry

theorem bv_extract.r_concat.proof : bv_extract.r_concat.Stmt := by
  sorry

theorem bv_extract.r_add_low.proof : bv_extract.r_add_low.Stmt := by
  sorry

theorem bv_extract.r_add_const.proof : bv_extract.r_add_const.Stmt := by
  sorry

theorem bv_extract.r_mul_pow2.proof : bv_extract.r_mul_pow2.Stmt := by
  sorry

theorem bv_extract.r_mul_low.proof : bv_extract.r_mul_low.Stmt := by
  sorry

theorem bv_extract.r_urem.proof : bv_extract.r_urem.Stmt := by
  sorry

theorem bv_extract.r_default.proof : bv_extract.r_default.Stmt := by
  sorry

theorem bv_extend.r_lit.proof : bv_extend.r_lit.Stmt := by
  sorry

theorem bv_extend.r_extend.proof : bv_extend.r_extend.Stmt := by
  sorry

theorem bv_extend.r_ite.proof : bv_extend.r_ite.Stmt := by
  sorry

theorem bv_extend.r_of_bool.proof : bv_extend.r_of_bool.Stmt := by
  sorry

theorem bv_extend.r_default.proof : bv_extend.r_default.Stmt := by
  sorry

theorem bv_concat.r_lits.proof : bv_concat.r_lits.Stmt := by
  sorry

theorem bv_concat.r_extracts.proof : bv_concat.r_extracts.Stmt := by
  sorry

theorem bv_concat.r_extract_extracts.proof : bv_concat.r_extract_extracts.Stmt := by
  sorry

theorem bv_concat.r_assoc_l.proof : bv_concat.r_assoc_l.Stmt := by
  sorry

theorem bv_concat.r_assoc_r.proof : bv_concat.r_assoc_r.Stmt := by
  sorry

theorem bv_concat.r_ites.proof : bv_concat.r_ites.Stmt := by
  sorry

theorem bv_concat.r_default.proof : bv_concat.r_default.Stmt := by
  sorry

theorem bv_shl.r_lits.proof : bv_shl.r_lits.Stmt := by
  sorry

theorem bv_shl.r_zero.proof : bv_shl.r_zero.Stmt := by
  sorry

theorem bv_shl.r_big.proof : bv_shl.r_big.Stmt := by
  sorry

theorem bv_shl.r_shl.proof : bv_shl.r_shl.Stmt := by
  sorry

theorem bv_shl.r_lshr.proof : bv_shl.r_lshr.Stmt := by
  sorry

theorem bv_shl.r_and_mask.proof : bv_shl.r_and_mask.Stmt := by
  sorry

theorem bv_shl.r_or_mask.proof : bv_shl.r_or_mask.Stmt := by
  sorry

theorem bv_shl.r_default.proof : bv_shl.r_default.Stmt := by
  sorry

theorem bv_lshr.r_lits.proof : bv_lshr.r_lits.Stmt := by
  sorry

theorem bv_lshr.r_zero.proof : bv_lshr.r_zero.Stmt := by
  sorry

theorem bv_lshr.r_big.proof : bv_lshr.r_big.Stmt := by
  sorry

theorem bv_lshr.r_lshr.proof : bv_lshr.r_lshr.Stmt := by
  sorry

theorem bv_lshr.r_and_mask.proof : bv_lshr.r_and_mask.Stmt := by
  sorry

theorem bv_lshr.r_or_mask.proof : bv_lshr.r_or_mask.Stmt := by
  sorry

theorem bv_lshr.r_default.proof : bv_lshr.r_default.Stmt := by
  sorry

theorem bv_ashr.r_lits.proof : bv_ashr.r_lits.Stmt := by
  sorry

theorem bv_ashr.r_zero.proof : bv_ashr.r_zero.Stmt := by
  sorry

theorem bv_ashr.r_big.proof : bv_ashr.r_big.Stmt := by
  sorry

theorem bv_ashr.r_ashr.proof : bv_ashr.r_ashr.Stmt := by
  sorry

theorem bv_ashr.r_default.proof : bv_ashr.r_default.Stmt := by
  sorry

theorem bv_of_float.r_lit.proof : bv_of_float.r_lit.Stmt := by
  sorry

theorem bv_of_float.r_default.proof : bv_of_float.r_default.Stmt := by
  sorry

theorem bv_to_float.r_lit.proof : bv_to_float.r_lit.Stmt := by
  sorry

theorem bv_to_float.r_default.proof : bv_to_float.r_default.Stmt := by
  sorry

theorem bv_to_float_raw.r_lit.proof : bv_to_float_raw.r_lit.Stmt := by
  sorry

theorem bv_to_float_raw.r_default.proof : bv_to_float_raw.r_default.Stmt := by
  sorry

end Bvr
