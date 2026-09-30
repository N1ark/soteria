import Bvr.Lib.Resize

/-! Extraction, extension, concatenation, conversions, floats and pointers,
proved per alternative. -/

namespace Bvr

open Classical Lib

theorem bv_extract.r_add_low.a1.proof : bv_extract.r_add_low.a1.Stmt := by
  bvr_rule_sem
  all_goals bvr_zlits
  all_goals bvr_split; subst_vars; exact (BitVec.extractLsb'_add (by omega)).symm

theorem bv_extract.r_mul_low.a1.proof : bv_extract.r_mul_low.a1.Stmt := by
  bvr_rule_sem
  all_goals bvr_zlits
  all_goals bvr_split; subst_vars; exact (BitVec.extractLsb'_mul (by omega)).symm

theorem bv_extract.r_add_const.a1.proof : bv_extract.r_add_const.a1.Stmt := by
  bvr_rule_sem
  all_goals bvr_zlits
  all_goals bvr_split; subst_vars; exact (extractLsb'_add_lsb _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm

theorem bv_extract.r_mul_pow2.a1.proof : bv_extract.r_mul_pow2.a1.Stmt := by
  bvr_rule_sem
  all_goals bvr_zlits
  all_goals bvr_split; subst_vars; obtain ⟨k, rfl⟩ := is_pow2_exists ‹_›
  all_goals simp only [log2_two_pow] at *; exact (extractLsb'_mul_pow2 _ ‹_› ‹_› ‹_›).symm

theorem bv_extract.r_urem.a1.proof : bv_extract.r_urem.a1.Stmt := by
  bvr_rule_sem
  all_goals bvr_zlits
  all_goals subst_vars; obtain ⟨k, rfl⟩ := is_pow2_exists ‹_›
  all_goals simp only [log2_two_pow] at *
  all_goals exact extractLsb'_umod_pow2 _ (by omega) (by omega) (by omega) (by omega)

theorem float_abs.r_abs.a1.proof : float_abs.r_abs.a1.Stmt := by
  intro FS O hO a T
  exact Refines.funop_idem fun v => by
    rcases v with _ | ⟨_ | _ | _ | ⟨p, x⟩ | _ | _⟩ <;> simp [evUnop, FBits.abs_abs]

theorem float_neg.r_neg.a1.proof : float_neg.r_neg.a1.Stmt := by
  intro FS O hO a T
  exact Refines.funop_invol (by simp) fun v r => by
    rcases v with _ | ⟨_ | _ | _ | ⟨p, x⟩ | _ | _⟩ <;> simp [evUnop, FBits.neg_neg]

theorem float_cast.r_lit.a1.proof : float_cast.r_lit.a1.Stmt := by
  intro FS O hO rm fp f T
  refine Refines.lit_of_unop (fun w => ?_) (fun hf => (hO.orc.convert rm fp f hf).2.2)
  have := hO.orc.convert rm fp f (Float.WF_of_WT (WT_unop.1 w).2)
  exact ⟨by rw [this.1], this.2.1⟩

theorem float_fma.r_lits.a1.proof : float_fma.r_lits.a1.Stmt := by
  intro FS O hO fa Ta fb Tb fc Tc
  have key : (float_fma.spec (.mk (.Float fa) Ta) (.mk (.Float fb) Tb) (.mk (.Float fc) Tc)).WT →
      Ta = .TFloat fa.prec ∧ fa.WF ∧ fb.WF ∧ fc.WF ∧ fa.prec = fb.prec ∧ fa.prec = fc.prec := by
    intro w
    obtain ⟨w0, w1, w2, w3⟩ := WT_triop.1 w
    obtain ⟨h1, h2⟩ := WT_float.1 w1
    obtain ⟨h3, h4⟩ := WT_float.1 w2
    obtain ⟨h5, h6⟩ := WT_float.1 w3
    simp only [Triop.WT, Term.ty_mk, Ty.sort_eq] at w0
    subst h1 h3 h5
    simp only [Ty.TFloat.injEq] at w0
    exact ⟨rfl, h2, h4, h6, w0.2.1.symm, w0.2.2.1.symm⟩
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨hT, h1, h2, h3, hp, hp'⟩ := key w
    have := hO.orc.fma fa fb fc h1 h2 h3 hp hp'
    exact ⟨WT_float.2 ⟨by simp [hT, this.1], this.2.1⟩, rfl⟩
  · obtain ⟨hT, h1, h2, h3, hp, hp'⟩ := key w
    have := hO.orc.fma fa fb fc h1 h2 h3 hp hp'
    obtain ⟨_, w1, w2, w3⟩ := WT_triop.1 w
    rw [float_fma.spec, eval_fma w, eval_float w1, eval_float w2, eval_float w3, this.2.2] at e
    rw [eval_float w']; exact e

theorem float_fmod.r_lits.a1.proof : float_fmod.r_lits.a1.Stmt := by
  intro FS O hO f1 T1 f2 T2
  have key : (float_fmod.spec (.mk (.Float f1) T1) (.mk (.Float f2) T2)).WT →
      T1 = .TFloat f1.prec ∧ T2 = .TFloat f2.prec ∧ f1.WF ∧ f2.WF ∧ f1.prec = f2.prec := by
    intro w
    obtain ⟨_, _, wr, _⟩ := WT_triop.1 w
    obtain ⟨w0, w1, w2⟩ := WT_binop.1 wr
    obtain ⟨h1, h2⟩ := WT_float.1 w1
    obtain ⟨h3, h4⟩ := WT_float.1 w2
    simp only [Binop.WT, Term.ty_mk, Ty.sort_eq] at w0
    subst h1 h3
    simp only [Ty.TFloat.injEq] at w0
    exact ⟨rfl, rfl, h2, h4, w0.2.1.symm⟩
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨hT, _, h1, h2, hp⟩ := key w
    have := hO.orc.fmod f1 f2 ⟨fun _ => none, fun _ _ => none⟩ h1 h2 hp
    exact ⟨WT_float.2 ⟨by simp [hT, this.1], this.2.1⟩, by simp [float_fmod.spec, raw_fmod_of_rem]⟩
  · obtain ⟨hT, hT', h1, h2, hp⟩ := key w
    have := hO.orc.fmod f1 f2 ρ h1 h2 hp
    subst hT hT'
    rw [eval_float w']
    simp only [float_fmod.spec, Float.term, ty_eq, Term.ty_mk] at e this
    rw [this.2.2] at e; exact e

theorem bv_of_float.r_lit.a1.proof : bv_of_float.r_lit.a1.Stmt := by
  intro FS O hO rm s n f T
  rcases ez : O.orc.f_to_int rm s n f with _ | z
  · simp [firstSome]; exact Refines.refl
  · simp [firstSome]
    refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
    · have := (WT_unop.1 w).1; simp [Unop.WT] at this
      exact ⟨mk_masked_WT this.1, by simp [bv_of_float.spec]⟩
    · have ⟨w1, w2⟩ := WT_unop.1 w
      simp [Unop.WT] at w1
      rw [bv_of_float.spec, eval_unop w, eval_float w2] at e
      rw [eval_mk_masked w1.1, ← hO.orc.to_int rm s n f z (Float.WF_of_WT w2) w1.1 ez]
      exact e

theorem bv_to_float.r_lit.a1.proof : bv_to_float.r_lit.a1.Stmt := by
  intro FS O hO rm s p z T
  have key : (bv_to_float.spec rm s p (.mk (.BitVec z) T)).WT →
      ∃ n : Int, 0 < n ∧ T = .TBitVector n ∧ 0 ≤ z ∧ z < 2 ^ n.toNat := by
    intro w
    have ⟨w1, w2⟩ := WT_unop.1 w
    simp [Unop.WT] at w1
    obtain ⟨n, hn, rfl⟩ := w1
    exact ⟨n, hn, rfl, (WT_bitVec_bv.1 w2).2⟩
  rcases ez : O.orc.f_of_int rm s p (size (.mk (.BitVec z) T))
    (to_z false (bv_of_lit (.mk (.BitVec z) T))) with _ | f
  · simp [firstSome]; exact Refines.refl
  · simp [firstSome]
    refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
    all_goals obtain ⟨n, hn, rfl, h0, h1⟩ := key w
    all_goals rw [to_z_bv_of_lit (WT_unop.1 w).2] at ez
    all_goals obtain ⟨hp, hf, he⟩ := hO.orc.of_int rm s p n z f hn h0 h1 ez
    · refine ⟨?_, by simp [bv_to_float.spec]⟩
      simp only [Term.WT, hp]; exact ⟨trivial, by simpa [Float.WF, hp] using hf⟩
    · rw [bv_to_float.spec, eval_unop w, eval_bitVec' (WT_unop.1 w).2 (.inl rfl), he] at e
      rw [eval_eq_ev w']; simp only [ev]; exact e

theorem bv_to_float_raw.r_lit.a1.proof : bv_to_float_raw.r_lit.a1.Stmt := by
  intro FS O hO z T
  simp only [bv_to_float_raw.spec, size_eq, Term.ty_mk]
  generalize fp_of_size (size_of_ty T) = p
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  all_goals have ⟨w1, w2⟩ := WT_unop.1 w
  all_goals simp only [Unop.WT, Ty.sort_eq, Term.ty_mk] at w1
  all_goals rw [to_z_bv_of_lit w2] at *
  all_goals have := emod_two_pow_lt z p.size
  all_goals have := emod_two_pow_nonneg z p.size
  all_goals have e1 : ((2 ^ p.size : Nat) : Int) = (2 : Int) ^ p.size := by push_cast; rfl
  · refine ⟨⟨rfl, ?_⟩, rfl⟩
    simp only [f_of_bits]; omega
  · rw [eval_unop w, eval_bitVec' w2 (.inl w1.1)] at e
    simp [evUnop] at e
    rw [eval_eq_ev w']; simp only [ev]; rw [← e]
    simp [Float.sem, Float.val, f_of_bits]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofInt, Nat.mod_eq_of_lt (by omega)]; simp

theorem float_eq.r_same.a1.proof : float_eq.r_same.a1.Stmt := by
  intro FS O hO v1 v2 h
  simp only [equal, decide_eq_true_eq] at h; subst h
  refine Refines.trans ?_ (Refines.b_not hO (hO.float_is_floatclass .NaN v1))
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨hp, _, _, w1, _⟩ := (WT_fcmp (Or.inl rfl)).1 w
    refine ⟨WT_unop.2 ⟨by simp [Unop.WT, float_is_floatclass.spec],
      WT_unop.2 ⟨by simpa [Unop.WT] using hp, w1⟩⟩, rfl⟩
  · have ⟨_, w1⟩ := WT_unop.1 w'
    rw [float_eq.spec, eval_binop w] at e
    rw [b_not.spec, eval_unop w', float_is_floatclass.spec, eval_unop w1]
    simp only [evBinop, fBin_eq_some] at e
    obtain ⟨p, x, y, h1, h2, h3⟩ := e
    rw [h1] at h2; cases h2
    rw [h1]; simp at h3; simp [evUnop, ← h3, FBits.isClass]

theorem float_eq.r_lit.a1.proof : float_eq.r_lit.a1.Stmt := by
  intro FS O hO v2 f T
  exact Refines.feq_lit hO (hO.sem_eq _ _)

end Bvr
