import Kanon.Lib.Resize

/-! Extraction, extension, concatenation, conversions, floats and pointers,
proved per alternative. -/

namespace Kanon

open Classical Lib

@[kanon_arm] theorem float_abs.r_abs.main.proof : float_abs.r_abs.main.Stmt := by
  intro FS O hO a T
  exact Refines.funop_idem fun v => by
    rcases v with _ | ⟨_ | _ | _ | ⟨p, x⟩ | _ | _⟩ <;> simp [evOp1, FBits.abs_abs]

@[kanon_arm] theorem float_neg.r_neg.main.proof : float_neg.r_neg.main.Stmt := by
  intro FS O hO a T
  exact Refines.funop_invol (by simp) fun v r => by
    rcases v with _ | ⟨_ | _ | _ | ⟨p, x⟩ | _ | _⟩ <;> simp [evOp1, FBits.neg_neg]

@[kanon_arm] theorem float_cast.r_lit.main.proof : float_cast.r_lit.main.Stmt := by
  intro FS O hO rm fp f T
  refine Refines.lit_of_unop_prec (fun w => ?_) (fun hf => (hO.orc.convert rm fp f hf).2.2)
  have := hO.orc.convert rm fp f (Float.WF_of_WT (WT_op1.1 w).2)
  exact ⟨by rw [this.1], this.2.1⟩

@[kanon_arm] theorem float_fma.r_lits.main.proof : float_fma.r_lits.main.Stmt := by
  intro FS O hO fa Ta fb Tb fc Tc
  have key : (float_fma.spec (.mk (.Float fa) Ta) (.mk (.Float fb) Tb) (.mk (.Float fc) Tc)).WT →
      Ta = .TFloat fa.prec ∧ fa.WF ∧ fb.WF ∧ fc.WF ∧ fa.prec = fb.prec ∧ fa.prec = fc.prec := by
    intro w
    obtain ⟨w0, w1, w2, w3⟩ := WT_op3.1 w
    obtain ⟨h1, h2⟩ := WT_float.1 w1
    obtain ⟨h3, h4⟩ := WT_float.1 w2
    obtain ⟨h5, h6⟩ := WT_float.1 w3
    simp only [Op3.WT, Term.ty_mk] at w0
    subst h1 h3 h5
    simp only [Ty.TFloat.injEq] at w0
    exact ⟨rfl, h2, h4, h6, w0.2.1.symm, w0.2.2.1.symm⟩
  refine Sem.Refines.intro_eval (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨hT, h1, h2, h3, hp, hp'⟩ := key w
    have := hO.orc.fma fa fb fc h1 h2 h3 hp hp'
    exact ⟨WT_float.2 ⟨by simp [this.1], this.2.1⟩, by simp [hT, this.1, float_fma.spec]⟩
  · obtain ⟨hT, h1, h2, h3, hp, hp'⟩ := key w
    have := hO.orc.fma fa fb fc h1 h2 h3 hp hp'
    obtain ⟨_, w1, w2, w3⟩ := WT_op3.1 w
    rw [← eval] at e ⊢
    rw [float_fma.spec, eval_fma w, eval_float w1, eval_float w2, eval_float w3, this.2.2] at e
    rw [eval_float w']; exact e

@[kanon_arm] theorem float_fmod.r_lits.main.proof : float_fmod.r_lits.main.Stmt := by
  intro FS O hO f1 T1 f2 T2
  have key : (float_fmod.spec (.mk (.Float f1) T1) (.mk (.Float f2) T2)).WT →
      T1 = .TFloat f1.prec ∧ T2 = .TFloat f2.prec ∧ f1.WF ∧ f2.WF ∧ f1.prec = f2.prec := by
    intro w
    obtain ⟨_, _, wr, _⟩ := WT_op3.1 w
    obtain ⟨w0, w1, w2⟩ := WT_op2.1 wr
    obtain ⟨h1, h2⟩ := WT_float.1 w1
    obtain ⟨h3, h4⟩ := WT_float.1 w2
    simp only [Op2.WT, Term.ty_mk] at w0
    subst h1 h3
    simp only [Ty.TFloat.injEq] at w0
    exact ⟨rfl, rfl, h2, h4, w0.2.1.symm⟩
  refine Sem.Refines.intro_eval (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨hT, _, h1, h2, hp⟩ := key w
    have := hO.orc.fmod f1 f2 ⟨fun _ => none⟩ h1 h2 hp
    exact ⟨WT_float.2 ⟨by simp [this.1], this.2.1⟩,
      by simp [hT, this.1, float_fmod.spec, raw_fmod_of_rem]⟩
  · obtain ⟨hT, hT', h1, h2, hp⟩ := key w
    have := hO.orc.fmod f1 f2 ρ h1 h2 hp
    subst hT hT'
    rw [← eval] at e ⊢
    rw [eval_float w']
    simp only [float_fmod.spec, Float.term, ty_eq, Term.ty_mk] at e this
    rw [this.2.2] at e; exact e

@[kanon_arm] theorem bv_of_float.r_lit.main.proof : bv_of_float.r_lit.main.Stmt := by
  intro FS O hO rm s n f T
  rcases ez : O.orc.f_to_int rm s n f with _ | z
  · simp [firstSome]; exact Sem.Refines.refl
  · simp [firstSome]
    refine Sem.Refines.intro_eval (fun w => ?_) (fun ρ v w w' e => ?_)
    · have := (WT_op1.1 w).1; simp [Op1.WT] at this
      exact ⟨mk_masked_WT this.1, by simp [bv_of_float.spec]⟩
    · have ⟨w1, w2⟩ := WT_op1.1 w
      simp [Op1.WT] at w1
      rw [← eval] at e ⊢
      rw [bv_of_float.spec, eval_op1 w, eval_float w2] at e
      rw [eval_mk_masked w1.1, ← hO.orc.to_int rm s n f z (Float.WF_of_WT w2) w1.1 ez]
      exact e

@[kanon_arm] theorem bv_to_float.r_lit.main.proof : bv_to_float.r_lit.main.Stmt := by
  intro FS O hO rm s p z T
  have key : (bv_to_float.spec rm s p (.mk (.BitVec z) T)).WT →
      ∃ n : Int, 0 < n ∧ T = .TBitVector n ∧ 0 ≤ z ∧ z < 2 ^ n.toNat := by
    intro w
    have ⟨w1, w2⟩ := WT_op1.1 w
    simp [Op1.WT] at w1
    obtain ⟨n, hn, rfl⟩ := w1
    exact ⟨n, hn, rfl, (WT_bitVec_bv.1 w2).2⟩
  simp only [size_eq, Term.ty_mk]
  rcases ez : O.orc.f_of_int rm s p (size_of_ty T) z with _ | f
  · simp [firstSome]; exact Sem.Refines.refl
  · simp [firstSome]
    refine Sem.Refines.intro_eval (fun w => ?_) (fun ρ v w w' e => ?_)
    all_goals obtain ⟨n, hn, rfl, h0, h1⟩ := key w
    all_goals obtain ⟨hp, hf, he⟩ := hO.orc.of_int rm s p n z f hn h0 h1 ez
    · refine ⟨?_, by simp [bv_to_float.spec, hp]⟩
      simp only [Term.WT, hp]; exact ⟨trivial, by simpa [Float.WF, hp] using hf⟩
    · rw [← eval] at e ⊢
      rw [bv_to_float.spec, eval_op1 w, eval_bitVec' (WT_op1.1 w).2 rfl, he] at e
      rw [eval_eq_ev w']; simp only [ev]; exact e

@[kanon_arm] theorem bv_to_float_raw.r_lit.main.proof : bv_to_float_raw.r_lit.main.Stmt := by
  intro FS O hO z T
  simp only [bv_to_float_raw.spec, size_eq, Term.ty_mk]
  generalize fp_of_size (size_of_ty T) = p
  refine Sem.Refines.intro_eval (fun w => ?_) (fun ρ v w w' e => ?_)
  all_goals have ⟨w1, w2⟩ := WT_op1.1 w
  all_goals simp only [Op1.WT, Term.ty_mk, fp_size] at w1
  all_goals have := emod_two_pow_lt z p.size
  all_goals have := emod_two_pow_nonneg z p.size
  all_goals have e1 : ((2 ^ p.size : Nat) : Int) = (2 : Int) ^ p.size := by push_cast; rfl
  · refine ⟨⟨rfl, ?_⟩, rfl⟩
    simp only [f_of_bits]; omega
  · rw [← eval] at e ⊢
    rw [eval_op1 w, eval_bitVec' w2 w1.1] at e
    simp [evOp1] at e
    rw [eval_eq_ev w']; simp only [ev]; rw [← e]
    simp [Float.sem, Float.val, f_of_bits]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofInt, Nat.mod_eq_of_lt (by omega)]; simp

@[kanon_arm] theorem float_eq.r_same.main.proof : float_eq.r_same.main.Stmt := by
  intro FS O hO v1 v2 h
  simp only [decide_eq_true_eq] at h; subst h
  refine Sem.Refines.trans ?_ (Refines.b_not hO (hO.float_is_floatclass .NaN v1))
  refine Sem.Refines.intro_eval (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨hp, _, _, w1, _⟩ := (WT_fcmp (Or.inl rfl)).1 w
    refine ⟨WT_op1.2 ⟨by simp [Op1.WT, float_is_floatclass.spec],
      WT_op1.2 ⟨by simpa [Op1.WT] using hp, w1⟩⟩, rfl⟩
  · have ⟨_, w1⟩ := WT_op1.1 w'
    rw [← eval] at e ⊢
    rw [float_eq.spec, eval_op2 w] at e
    rw [b_not.spec, eval_op1 w', float_is_floatclass.spec, eval_op1 w1]
    simp only [evOp2, fBin_eq_some] at e
    obtain ⟨p, x, y, h1, h2, h3⟩ := e
    rw [h1] at h2; cases h2
    rw [h1]; simp at h3; simp [evOp1, ← h3, FBits.isClass]

@[kanon_arm] theorem float_eq.r_lit.main.proof : float_eq.r_lit.main.Stmt := by
  intro FS O hO v2 f T
  exact Refines.feq_lit hO (hO.sem_eq _ _)

@[kanon_arm] theorem bv_to_bool.r_lit.main.proof : bv_to_bool.r_lit.main.Stmt := by
  kanon_rule_sem
  all_goals first
    | exact (‹∀ m : Int, ¬ _ = Ty.TBitVector m› _ ‹Ty.TBitVector _ = _›.symm).elim
    | (obtain ⟨h0, h1⟩ := ‹(0 : Int) ≤ _ ∧ _ < _›
       try subst_vars
       try simp only [Int.toNat_natCast] at *
       simp only [ofInt_eq_zero_iff h0 h1] at *
       simp_all)

@[kanon_arm] theorem bv_not_bool.r_lit.main.proof : bv_not_bool.r_lit.main.Stmt := by
  kanon_rule_sem
  all_goals first
    | exact (‹∀ m : Int, ¬ _ = Ty.TBitVector m› _ ‹Ty.TBitVector _ = _›.symm).elim
    | (obtain ⟨h0, h1⟩ := ‹(0 : Int) ≤ _ ∧ _ < _›
       try subst_vars
       try simp only [Int.toNat_natCast] at *
       simp only [ofInt_eq_zero_iff h0 h1] at *
       simp_all)

@[kanon_arm] theorem float_eq.r_default.main.proof : float_eq.r_default.main.Stmt := by
  intro FS O hO v1 v2
  simp only [float_eq.spec, mk_commut_binop]
  split
  · exact Sem.Refines.refl
  · exact Refines.comm (by simp [Op2.Comm]) fun _ => rfl

end Kanon
