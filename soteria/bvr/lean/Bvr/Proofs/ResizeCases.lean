import Bvr.Lib.Resize

/-! Extraction, extension, concatenation, conversions, floats and pointers,
proved per alternative. -/

namespace Bvr

open Classical Lib EqL

theorem bv_concat.r_assoc_l.a1.proof : bv_concat.r_assoc_l.a1.Stmt := by
  bvr_rule_r

theorem bv_concat.r_assoc_r.a1.proof : bv_concat.r_assoc_r.a1.Stmt := by
  bvr_rule_r

theorem bv_concat.r_default.a1.proof : bv_concat.r_default.a1.Stmt := by
  bvr_rule_r

theorem bv_concat.r_extract_extracts.a1.proof : bv_concat.r_extract_extracts.a1.Stmt := by
  bvr_rule_r

theorem bv_concat.r_extracts.a1.proof : bv_concat.r_extracts.a1.Stmt := by
  bvr_rule_r

theorem bv_concat.r_ites.a1.proof : bv_concat.r_ites.a1.Stmt := by
  bvr_rule_r

theorem bv_concat.r_lits.a1.proof : bv_concat.r_lits.a1.Stmt := by
  bvr_rule_r

theorem bv_extend.r_default.a1.proof : bv_extend.r_default.a1.Stmt := by
  bvr_rule_r

theorem bv_extend.r_extend.a1.proof : bv_extend.r_extend.a1.Stmt := by
  bvr_rule_r

theorem bv_extend.r_ite.a1.proof : bv_extend.r_ite.a1.Stmt := by
  bvr_rule_r

theorem bv_extend.r_lit.a1.proof : bv_extend.r_lit.a1.Stmt := by
  bvr_rule_r

theorem bv_extend.r_of_bool.a1.proof : bv_extend.r_of_bool.a1.Stmt := by
  bvr_rule_r

theorem bv_extract.r_and_.a1.proof : bv_extract.r_and_.a1.Stmt := by
  bvr_rule_r

theorem bv_extract.r_concat.a1.proof : bv_extract.r_concat.a1.Stmt := by
  bvr_rule_r

theorem bv_extract.r_default.a1.proof : bv_extract.r_default.a1.Stmt := by
  bvr_rule_r

theorem bv_extract.r_ext_low.a1.proof : bv_extract.r_ext_low.a1.Stmt := by
  bvr_rule_r

theorem bv_extract.r_ext_orig.a1.proof : bv_extract.r_ext_orig.a1.Stmt := by
  bvr_rule_r

theorem bv_extract.r_extract.a1.proof : bv_extract.r_extract.a1.Stmt := by
  bvr_rule_r

theorem bv_extract.r_full.a1.proof : bv_extract.r_full.a1.Stmt := by
  bvr_rule_r

theorem bv_extract.r_ite.a1.proof : bv_extract.r_ite.a1.Stmt := by
  bvr_rule_r

theorem bv_extract.r_lit.a1.proof : bv_extract.r_lit.a1.Stmt := by
  bvr_rule_r

theorem bv_extract.r_lshr.a1.proof : bv_extract.r_lshr.a1.Stmt := by
  bvr_rule_r

theorem bv_extract.r_or_.a1.proof : bv_extract.r_or_.a1.Stmt := by
  bvr_rule_r

theorem bv_extract.r_sext_bit.a1.proof : bv_extract.r_sext_bit.a1.Stmt := by
  bvr_rule_r

theorem bv_extract.r_shl.a1.proof : bv_extract.r_shl.a1.Stmt := by
  bvr_rule_r

theorem bv_extract.r_xor.a1.proof : bv_extract.r_xor.a1.Stmt := by
  bvr_rule_r

theorem bv_extract.r_zext_high.a1.proof : bv_extract.r_zext_high.a1.Stmt := by
  bvr_rule_r

theorem bv_not_bool.r_default.a1.proof : bv_not_bool.r_default.a1.Stmt := by
  bvr_rule_r

theorem bv_not_bool.r_of_bool.a1.proof : bv_not_bool.r_of_bool.a1.Stmt := by
  bvr_rule_r

theorem bv_of_bool.r_default.a1.proof : bv_of_bool.r_default.a1.Stmt := by
  bvr_rule_r

theorem bv_of_bool.r_false_.a1.proof : bv_of_bool.r_false_.a1.Stmt := by
  bvr_rule_r

theorem bv_of_bool.r_true_.a1.proof : bv_of_bool.r_true_.a1.Stmt := by
  bvr_rule_r

theorem bv_to_bool.r_default.a1.proof : bv_to_bool.r_default.a1.Stmt := by
  bvr_rule_r

theorem bv_to_bool.r_of_bool.a1.proof : bv_to_bool.r_of_bool.a1.Stmt := by
  bvr_rule_r

theorem bv_to_bool.r_lit.a1.proof : bv_to_bool.r_lit.a1.Stmt := by
  bvr_rule_sem_r
  all_goals subst_vars; simp (disch := assumption) only [ofInt_eq_zero_of_lt] at *; simp_all

theorem bv_not_bool.r_lit.a1.proof : bv_not_bool.r_lit.a1.Stmt := by
  bvr_rule_sem_r
  all_goals subst_vars; simp (disch := assumption) only [ofInt_eq_zero_of_lt] at *; simp_all

theorem bv_extract.r_add_low.a1.proof : bv_extract.r_add_low.a1.Stmt := by
  bvr_rule_sem_r
  all_goals bvr_split; subst_vars; exact (BitVec.extractLsb'_add (by omega)).symm

theorem bv_extract.r_mul_low.a1.proof : bv_extract.r_mul_low.a1.Stmt := by
  bvr_rule_sem_r
  all_goals bvr_split; subst_vars; exact (BitVec.extractLsb'_mul (by omega)).symm

theorem bv_extract.r_add_const.a1.proof : bv_extract.r_add_const.a1.Stmt := by
  bvr_rule_sem_r
  all_goals bvr_split; subst_vars; exact (extractLsb'_add_lsb _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm

theorem bv_extract.r_mul_pow2.a1.proof : bv_extract.r_mul_pow2.a1.Stmt := by
  bvr_rule_sem_r
  all_goals bvr_split; subst_vars; obtain ⟨k, rfl⟩ := is_pow2_eq ‹_›
  all_goals simp only [log2_two_pow] at *; exact (extractLsb'_mul_pow2 _ ‹_› ‹_› ‹_›).symm

theorem bv_extract.r_urem.a1.proof : bv_extract.r_urem.a1.Stmt := by
  bvr_rule_sem_r
  all_goals subst_vars; obtain ⟨k, rfl⟩ := is_pow2_eq ‹_›
  all_goals simp only [log2_two_pow] at *
  all_goals exact extractLsb'_umod_pow2 _ (by omega) (by omega) (by omega) (by omega)

theorem bv_of_float.r_default.a1.proof : bv_of_float.r_default.a1.Stmt := by
  bvr_rule

theorem bv_to_float.r_default.a1.proof : bv_to_float.r_default.a1.Stmt := by
  bvr_rule

theorem bv_to_float_raw.r_default.a1.proof : bv_to_float_raw.r_default.a1.Stmt := by
  bvr_rule

theorem float_abs.r_default.a1.proof : float_abs.r_default.a1.Stmt := by
  bvr_rule

theorem float_add.r_default.a1.proof : float_add.r_default.a1.Stmt := by
  bvr_rule

theorem float_cast.r_default.a1.proof : float_cast.r_default.a1.Stmt := by
  bvr_rule

theorem float_div.r_default.a1.proof : float_div.r_default.a1.Stmt := by
  bvr_rule

theorem float_eq.r_default.a1.proof : float_eq.r_default.a1.Stmt := by
  bvr_rule

theorem float_fma.r_default.a1.proof : float_fma.r_default.a1.Stmt := by
  bvr_rule

theorem float_fmod.r_default.a1.proof : float_fmod.r_default.a1.Stmt := by
  bvr_rule

theorem float_is_floatclass.r_default.a1.proof : float_is_floatclass.r_default.a1.Stmt := by
  bvr_rule

theorem float_is_negative.r_default.a1.proof : float_is_negative.r_default.a1.Stmt := by
  bvr_rule

theorem float_is_positive.r_default.a1.proof : float_is_positive.r_default.a1.Stmt := by
  bvr_rule

theorem float_leq.r_default.a1.proof : float_leq.r_default.a1.Stmt := by
  bvr_rule

theorem float_lt.r_default.a1.proof : float_lt.r_default.a1.Stmt := by
  bvr_rule

theorem float_max.r_default.a1.proof : float_max.r_default.a1.Stmt := by
  bvr_rule

theorem float_min.r_default.a1.proof : float_min.r_default.a1.Stmt := by
  bvr_rule

theorem float_mul.r_default.a1.proof : float_mul.r_default.a1.Stmt := by
  bvr_rule

theorem float_neg.r_default.a1.proof : float_neg.r_default.a1.Stmt := by
  bvr_rule

theorem float_rem.r_default.a1.proof : float_rem.r_default.a1.Stmt := by
  bvr_rule

theorem float_round.r_default.a1.proof : float_round.r_default.a1.Stmt := by
  bvr_rule

theorem float_sqrt.r_default.a1.proof : float_sqrt.r_default.a1.Stmt := by
  bvr_rule

theorem float_sub.r_default.a1.proof : float_sub.r_default.a1.Stmt := by
  bvr_rule

theorem ptr_loc.r_default.a1.proof : ptr_loc.r_default.a1.Stmt := by
  bvr_rule

theorem ptr_ofs.r_default.a1.proof : ptr_ofs.r_default.a1.Stmt := by
  bvr_rule

theorem float_fmod_of_rem.r_main.a1.proof : float_fmod_of_rem.r_main.a1.Stmt := by
  bvr_rule

theorem ptr_loc.r_ptr.a1.proof : ptr_loc.r_ptr.a1.Stmt := by
  intro FS O hO l o T
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨n, hn, rfl, hl, ho, wl, wo⟩ := WT_ptr.1 (WT_unop.1 w).2
    simp [ptr_loc.spec, hl, wl, size_of_ty]
  · rw [ptr_loc.spec, eval_unop w] at e
    cases hp : eval FS ρ (Term.mk (Kind.ptr l o) T) with
    | none => simp [hp] at e
    | some pv =>
      obtain ⟨n, x, y, h1, h2, rfl⟩ := (eval_ptr_eq_some (WT_unop.1 w).2).1 hp
      rw [hp] at e; simp [evUnop] at e; subst e; exact h1

theorem ptr_ofs.r_ptr.a1.proof : ptr_ofs.r_ptr.a1.Stmt := by
  intro FS O hO l o T
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨n, hn, rfl, hl, ho, wl, wo⟩ := WT_ptr.1 (WT_unop.1 w).2
    simp [ptr_ofs.spec, ho, wo, size_of_ty]
  · rw [ptr_ofs.spec, eval_unop w] at e
    cases hp : eval FS ρ (Term.mk (Kind.ptr l o) T) with
    | none => simp [hp] at e
    | some pv =>
      obtain ⟨n, x, y, h1, h2, rfl⟩ := (eval_ptr_eq_some (WT_unop.1 w).2).1 hp
      rw [hp] at e; simp [evUnop] at e; subst e; exact h2

theorem float_is_floatclass.r_lit.a1.proof : float_is_floatclass.r_lit.a1.Stmt := by
  intro FS O hO fc f T
  exact Refines.test_of_unop (fun w => ((WT_ftest (by simp)).1 w).2.1)
    (by simp [evUnop, FloatLit.sem, f_is_class])

theorem float_is_negative.r_lit.a1.proof : float_is_negative.r_lit.a1.Stmt := by
  intro FS O hO f T
  exact Refines.test_of_unop (fun w => ((WT_ftest (by simp)).1 w).2.1)
    (by simp [evUnop, FloatLit.sem, f_is_negative])

theorem float_is_positive.r_lit.a1.proof : float_is_positive.r_lit.a1.Stmt := by
  intro FS O hO f T
  exact Refines.test_of_unop (fun w => ((WT_ftest (by simp)).1 w).2.1)
    (by simp [evUnop, FloatLit.sem, f_is_positive])

theorem float_eq.r_lits.a1.proof : float_eq.r_lits.a1.Stmt := by
  intro FS O hO f1 T1 f2 T2
  exact Refines.fcmp_lits (by simp) fun hp => by
    simp [evBinop, fBin, FloatLit.sem, f_eq, FloatLit.cmp, hp]

theorem float_lt.r_lits.a1.proof : float_lt.r_lits.a1.Stmt := by
  intro FS O hO f1 T1 f2 T2
  exact Refines.fcmp_lits (by simp) fun hp => by
    simp [evBinop, fBin, FloatLit.sem, f_lt, FloatLit.cmp, hp]

theorem float_leq.r_lits.a1.proof : float_leq.r_lits.a1.Stmt := by
  intro FS O hO f1 T1 f2 T2
  exact Refines.fcmp_lits (by simp) fun hp => by
    simp [evBinop, fBin, FloatLit.sem, f_le, FloatLit.cmp, hp]

theorem float_add.r_lits.a1.proof : float_add.r_lits.a1.Stmt := by
  intro FS O hO f1 T1 f2 T2; exact Refines.float_bin_lits hO (by simp)

theorem float_sub.r_lits.a1.proof : float_sub.r_lits.a1.Stmt := by
  intro FS O hO f1 T1 f2 T2; exact Refines.float_bin_lits hO (by simp)

theorem float_mul.r_lits.a1.proof : float_mul.r_lits.a1.Stmt := by
  intro FS O hO f1 T1 f2 T2; exact Refines.float_bin_lits hO (by simp)

theorem float_div.r_lits.a1.proof : float_div.r_lits.a1.Stmt := by
  intro FS O hO f1 T1 f2 T2; exact Refines.float_bin_lits hO (by simp)

theorem float_rem.r_lits.a1.proof : float_rem.r_lits.a1.Stmt := by
  intro FS O hO f1 T1 f2 T2; exact Refines.float_bin_lits hO (by simp)

theorem float_min.r_lits.a1.proof : float_min.r_lits.a1.Stmt := by
  intro FS O hO f1 T1 f2 T2; exact Refines.float_bin_lits hO (by simp)

theorem float_max.r_lits.a1.proof : float_max.r_lits.a1.Stmt := by
  intro FS O hO f1 T1 f2 T2; exact Refines.float_bin_lits hO (by simp)

theorem float_abs.r_lit.a1.proof : float_abs.r_lit.a1.Stmt := by
  intro FS O hO f T; exact Refines.funop_bits (by simp) (fun _ _ => rfl)

theorem float_neg.r_lit.a1.proof : float_neg.r_lit.a1.Stmt := by
  intro FS O hO f T; exact Refines.funop_bits (by simp) (fun _ _ => rfl)

theorem float_sqrt.r_lit.a1.proof : float_sqrt.r_lit.a1.Stmt := by
  intro FS O hO f T; exact Refines.funop_lit (by simp) (hO.orc.sqrt f)

theorem float_round.r_lit.a1.proof : float_round.r_lit.a1.Stmt := by
  intro FS O hO rm f T; exact Refines.funop_lit (by simp) (hO.orc.round rm f)

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
  have := hO.orc.convert rm fp f (FloatLit.WF_of_WT (WT_unop.1 w).2)
  exact ⟨by rw [this.1], this.2.1⟩

theorem float_fma.r_lits.a1.proof : float_fma.r_lits.a1.Stmt := by
  intro FS O hO fa Ta fb Tb fc Tc
  have key : (float_fma.spec (.mk (.float fa) Ta) (.mk (.float fb) Tb) (.mk (.float fc) Tc)).WT →
      Ta = .float fa.prec ∧ fa.WF ∧ fb.WF ∧ fc.WF ∧ fa.prec = fb.prec ∧ fa.prec = fc.prec := by
    intro w
    obtain ⟨w0, w1, w2, w3⟩ := WT_triop.1 w
    obtain ⟨h1, h2⟩ := WT_float.1 w1
    obtain ⟨h3, h4⟩ := WT_float.1 w2
    obtain ⟨h5, h6⟩ := WT_float.1 w3
    simp only [Triop.WT, Term.ty_mk, Ty.sort_eq] at w0
    subst h1 h3 h5
    simp only [Ty.float.injEq] at w0
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
  have key : (float_fmod.spec (.mk (.float f1) T1) (.mk (.float f2) T2)).WT →
      T1 = .float f1.prec ∧ T2 = .float f2.prec ∧ f1.WF ∧ f2.WF ∧ f1.prec = f2.prec := by
    intro w
    obtain ⟨_, _, wr, _⟩ := WT_triop.1 w
    obtain ⟨w0, w1, w2⟩ := WT_binop.1 wr
    obtain ⟨h1, h2⟩ := WT_float.1 w1
    obtain ⟨h3, h4⟩ := WT_float.1 w2
    simp only [Binop.WT, Term.ty_mk, Ty.sort_eq] at w0
    subst h1 h3
    simp only [Ty.float.injEq] at w0
    exact ⟨rfl, rfl, h2, h4, w0.2.1.symm⟩
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨hT, _, h1, h2, hp⟩ := key w
    have := hO.orc.fmod f1 f2 ⟨fun _ => none, fun _ _ => none⟩ h1 h2 hp
    exact ⟨WT_float.2 ⟨by simp [hT, this.1], this.2.1⟩, by simp [float_fmod.spec, raw_fmod_of_rem]⟩
  · obtain ⟨hT, hT', h1, h2, hp⟩ := key w
    have := hO.orc.fmod f1 f2 ρ h1 h2 hp
    subst hT hT'
    rw [eval_float w']
    simp only [float_fmod.spec, FloatLit.term, ty_eq, Term.ty_mk] at e this
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
      rw [eval_mk_masked w1.1, ← hO.orc.to_int rm s n f z (FloatLit.WF_of_WT w2) w1.1 ez]
      exact e

theorem bv_to_float.r_lit.a1.proof : bv_to_float.r_lit.a1.Stmt := by
  intro FS O hO rm s p z T
  have key : (bv_to_float.spec rm s p (.mk (.bitVec z) T)).WT →
      ∃ n : Int, 0 < n ∧ T = .bitVector n ∧ 0 ≤ z ∧ z < 2 ^ n.toNat := by
    intro w
    have ⟨w1, w2⟩ := WT_unop.1 w
    simp [Unop.WT] at w1
    obtain ⟨n, hn, rfl⟩ := w1
    exact ⟨n, hn, rfl, (WT_bitVec_bv.1 w2).2⟩
  rcases ez : O.orc.f_of_int rm s p (size (.mk (.bitVec z) T))
    (to_z false (bv_of_lit (.mk (.bitVec z) T))) with _ | f
  · simp [firstSome]; exact Refines.refl
  · simp [firstSome]
    refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
    all_goals obtain ⟨n, hn, rfl, h0, h1⟩ := key w
    all_goals rw [to_z_bv_of_lit (WT_unop.1 w).2] at ez
    all_goals obtain ⟨hp, hf, he⟩ := hO.orc.of_int rm s p n z f hn h0 h1 ez
    · refine ⟨?_, by simp [bv_to_float.spec]⟩
      simp only [Term.WT, hp]; exact ⟨trivial, by simpa [FloatLit.WF, hp] using hf⟩
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
    simp [FloatLit.sem, FloatLit.val, f_of_bits]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofInt, Nat.mod_eq_of_lt (by omega)]; simp

theorem float_eq.r_same.a1.proof : float_eq.r_same.a1.Stmt := by
  intro FS O hO v1 v2 h
  simp only [equal, decide_eq_true_eq] at h; subst h
  refine Refines.trans ?_ (Refines.b_not hO (hO.float_is_floatclass .nan v1))
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨hp, _, _, w1, _⟩ := (WT_fcmp (Or.inl rfl)).1 w
    refine ⟨WT_unop.2 ⟨by simp [Unop.WT, float_is_floatclass.spec],
      WT_unop.2 ⟨by simpa [Unop.WT] using hp, w1⟩⟩, rfl⟩
  · have ⟨_, w1⟩ := WT_unop.1 w'
    rw [float_eq.spec, eval_binop w] at e
    rw [b_not.spec, eval_unop w', float_is_floatclass.spec, eval_unop w1]
    simp only [evBinop, EqL.fBin_eq_some] at e
    obtain ⟨p, x, y, h1, h2, h3⟩ := e
    rw [h1] at h2; cases h2
    rw [h1]; simp at h3; simp [evUnop, ← h3, FBits.isClass]

theorem float_eq.r_lit_l.a1.proof : float_eq.r_lit_l.a1.Stmt := by
  intro FS O hO v2 f T
  exact Refines.feq_lit hO (hO.sem_eq _ _)

theorem float_eq.r_lit_r.a1.proof : float_eq.r_lit_r.a1.Stmt := by
  intro FS O hO v1 f T
  exact Refines.trans (Refines.comm (by simp [Binop.Comm]) (fun _ => rfl))
    (Refines.feq_lit hO (Refines.trans (Refines.comm (by simp [Binop.Comm]) (fun _ => rfl))
      (hO.sem_eq _ _)))

end Bvr
