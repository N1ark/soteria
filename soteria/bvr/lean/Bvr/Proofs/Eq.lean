import Bvr.Proofs.EqLemmas

/-! Equality (`sem_eq`), floats and pointers. -/

namespace Bvr

open Classical EqL

theorem sem_eq.r_same.proof : sem_eq.r_same.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_same, equal] at h
  by_cases hv : v1 = v2 <;> simp [hv] at h
  subst h hv
  refine Refines.eq_const (fun _ _ _ => by simp) (fun ρ x y _ _ _ hx hy => ?_)
  rw [hx] at hy; cases hy; simp

theorem sem_eq.r_bools.proof : sem_eq.r_bools.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_bools] at h
  split at h <;> simp at h
  subst h
  refine Refines.eq_const (fun _ _ _ => by simp) (fun ρ x y _ w1 w2 hx hy => ?_)
  rw [eval_bool (WT_bool.1 w1)] at hx; rw [eval_bool (WT_bool.1 w2)] at hy
  cases hx; cases hy; simp

theorem sem_eq.r_ptrs.proof : sem_eq.r_ptrs.Stmt := by
  sorry

theorem sem_eq.r_bvs.proof : sem_eq.r_bvs.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_bvs] at h
  split at h <;> simp at h
  subst h
  refine Refines.eq_const (fun _ _ _ => by simp) (fun ρ x y hT w1 w2 hx hy => ?_)
  obtain ⟨n, hn, hT1, a1, a2, e1⟩ := eval_bitVec_range (FS := FS) (ρ := ρ) w1
  obtain ⟨m, hm, hT2, b1, b2, e2⟩ := eval_bitVec_range (FS := FS) (ρ := ρ) w2
  rw [e1] at hx; rw [e2] at hy; cases hx; cases hy
  simp only [Term.ty_mk] at hT; subst hT
  have : n = m := by rcases hT1 with h | h <;> rcases hT2 with h' | h' <;> simp_all <;> omega
  subst this
  simp [BitVec.ofInt_inj a1 a2 b1 b2]

theorem sem_eq.r_floats.proof : sem_eq.r_floats.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_floats, f_bits_equal] at h
  split at h <;> simp at h
  subst h
  refine Refines.eq_const (fun _ _ _ => by simp) (fun ρ x y hT w1 w2 hx hy => ?_)
  rw [eval_float w1] at hx; rw [eval_float w2] at hy; cases hx; cases hy
  rename_i f1 T1 f2 T2
  have h1 := FloatLit.WF_of_WT w1
  have h2 := FloatLit.WF_of_WT w2
  simp only [eval_of_bool, Option.some.injEq, Val.bool.injEq]
  congr 1
  apply propext
  constructor
  · rintro rfl; rfl
  · intro e
    obtain ⟨p1, b1⟩ := f1; obtain ⟨p2, b2⟩ := f2
    simp only [FloatLit.sem, Val.float.injEq] at e
    obtain ⟨rfl, e⟩ := e
    exact FloatLit.eq_of_val rfl h1 h2 (by rw [eq_of_heq e])

theorem sem_eq.r_neg_r.proof : sem_eq.r_neg_r.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_neg_r] at h
  split at h <;> simp at h
  subst h
  refine Refines.trans ?_ (Refines.sem_eq hO (hO.bv_neg false _) Refines.refl)
  exact Refines.eq_unop_move (f := fun x => -x) (Or.inl ⟨_, rfl⟩) (Or.inl ⟨_, rfl⟩)
    (fun v r e => by
      rcases v with _ | ⟨_ | ⟨n, x⟩ | _ | _ | _ | _⟩ <;> simp [evUnop] at e
      exact ⟨_, _, rfl, e.2.symm⟩)
    (fun n x => by simp [evUnop]) (fun n a b => by grind)

theorem sem_eq.r_neg_l.proof : sem_eq.r_neg_l.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_neg_l] at h
  split at h <;> simp at h
  subst h
  refine Refines.trans Refines.eq_symm ?_
  refine Refines.trans ?_ (Refines.sem_eq hO Refines.refl (hO.bv_neg false _))
  refine Refines.trans ?_ Refines.eq_symm
  exact Refines.eq_unop_move (f := fun x => -x) (Or.inl ⟨_, rfl⟩) (Or.inl ⟨_, rfl⟩)
    (fun v r e => by
      rcases v with _ | ⟨_ | ⟨n, x⟩ | _ | _ | _ | _⟩ <;> simp [evUnop] at e
      exact ⟨_, _, rfl, e.2.symm⟩)
    (fun n x => by simp [evUnop]) (fun n a b => by grind)

theorem sem_eq.r_not_r.proof : sem_eq.r_not_r.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_not_r] at h
  split at h <;> simp at h
  subst h
  refine Refines.trans ?_ (Refines.sem_eq hO (hO.bv_not _) Refines.refl)
  exact Refines.eq_unop_move (f := fun x => ~~~x) (Or.inr rfl) (Or.inr rfl)
    (fun v r e => by
      rcases v with _ | ⟨_ | ⟨n, x⟩ | _ | _ | _ | _⟩ <;> simp [evUnop] at e
      exact ⟨_, _, rfl, e.symm⟩)
    (fun n x => by simp [evUnop]) (fun n a b => by grind)

theorem sem_eq.r_not_l.proof : sem_eq.r_not_l.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_not_l] at h
  split at h <;> simp at h
  subst h
  refine Refines.trans Refines.eq_symm ?_
  refine Refines.trans ?_ (Refines.sem_eq hO Refines.refl (hO.bv_not _))
  refine Refines.trans ?_ Refines.eq_symm
  exact Refines.eq_unop_move (f := fun x => ~~~x) (Or.inr rfl) (Or.inr rfl)
    (fun v r e => by
      rcases v with _ | ⟨_ | ⟨n, x⟩ | _ | _ | _ | _⟩ <;> simp [evUnop] at e
      exact ⟨_, _, rfl, e.symm⟩)
    (fun n x => by simp [evUnop]) (fun n a b => by grind)

theorem sem_eq.r_add_const_r.proof : sem_eq.r_add_const_r.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_add_const_r] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> subst h
  · refine Refines.trans ?_ (Refines.sem_eq hO (hO.bv_sub unchecked _ _) Refines.refl)
    exact Refines.eq_bin_move (Or.inl ⟨_, rfl⟩) (Or.inr (Or.inl ⟨_, rfl⟩)) (fun _ _ _ e => evBinop_add_some e) (fun _ _ _ => evBinop_sub_unchecked) _ _ _
      (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (fun _ _ a x y ha hp hq => ⟨_, _, _, ha, hp, hq, by grind⟩)
  · refine Refines.trans ?_ (Refines.sem_eq hO (hO.bv_sub unchecked _ _) Refines.refl)
    exact Refines.eq_bin_move (Or.inl ⟨_, rfl⟩) (Or.inr (Or.inl ⟨_, rfl⟩)) (fun _ _ _ e => evBinop_add_some e) (fun _ _ _ => evBinop_sub_unchecked) _ _ _
      (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) (fun _ _ a x y ha hp hq => ⟨_, _, _, ha, hq, hp, by grind⟩)

theorem sem_eq.r_add_const_l.proof : sem_eq.r_add_const_l.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_add_const_l] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> subst h
  · refine Refines.trans Refines.eq_symm ?_
    refine Refines.trans ?_ (Refines.sem_eq hO (hO.bv_sub unchecked _ _) Refines.refl)
    exact Refines.eq_bin_move (Or.inl ⟨_, rfl⟩) (Or.inr (Or.inl ⟨_, rfl⟩)) (fun _ _ _ e => evBinop_add_some e) (fun _ _ _ => evBinop_sub_unchecked) _ _ _
      (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (fun _ _ a x y ha hp hq => ⟨_, _, _, ha, hp, hq, by grind⟩)
  · refine Refines.trans Refines.eq_symm ?_
    refine Refines.trans ?_ (Refines.sem_eq hO (hO.bv_sub unchecked _ _) Refines.refl)
    exact Refines.eq_bin_move (Or.inl ⟨_, rfl⟩) (Or.inr (Or.inl ⟨_, rfl⟩)) (fun _ _ _ e => evBinop_add_some e) (fun _ _ _ => evBinop_sub_unchecked) _ _ _
      (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) (fun _ _ a x y ha hp hq => ⟨_, _, _, ha, hq, hp, by grind⟩)

theorem sem_eq.r_sub_const_r1.proof : sem_eq.r_sub_const_r1.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_sub_const_r1] at h
  split at h <;> simp at h
  subst h
  refine Refines.trans ?_ (Refines.sem_eq hO (hO.bv_add unchecked _ _) Refines.refl)
  exact Refines.eq_bin_move (Or.inr (Or.inl ⟨_, rfl⟩)) (Or.inl ⟨_, rfl⟩) (fun _ _ _ e => evBinop_sub_some e) (fun _ _ _ => evBinop_add_unchecked) _ _ _
      (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) (fun _ _ a x y ha hp hq => ⟨_, _, _, ha, hq, hp, by grind⟩)

theorem sem_eq.r_sub_const_r2.proof : sem_eq.r_sub_const_r2.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_sub_const_r2] at h
  split at h <;> simp at h
  subst h
  refine Refines.trans ?_ (Refines.sem_eq hO (hO.bv_sub unchecked _ _) Refines.refl)
  exact Refines.eq_bin_move (Or.inr (Or.inl ⟨_, rfl⟩)) (Or.inr (Or.inl ⟨_, rfl⟩)) (fun _ _ _ e => evBinop_sub_some e) (fun _ _ _ => evBinop_sub_unchecked) _ _ _
      (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr rfl)) (fun _ _ a x y ha hp hq => ⟨_, _, _, hp, ha, hq, by grind⟩)

theorem sem_eq.r_sub_const_l1.proof : sem_eq.r_sub_const_l1.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_sub_const_l1] at h
  split at h <;> simp at h
  subst h
  refine Refines.trans Refines.eq_symm ?_
  refine Refines.trans ?_ (Refines.sem_eq hO (hO.bv_add unchecked _ _) Refines.refl)
  exact Refines.eq_bin_move (Or.inr (Or.inl ⟨_, rfl⟩)) (Or.inl ⟨_, rfl⟩) (fun _ _ _ e => evBinop_sub_some e) (fun _ _ _ => evBinop_add_unchecked) _ _ _
      (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) (fun _ _ a x y ha hp hq => ⟨_, _, _, ha, hq, hp, by grind⟩)

theorem sem_eq.r_sub_const_l2.proof : sem_eq.r_sub_const_l2.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_sub_const_l2] at h
  split at h <;> simp at h
  subst h
  refine Refines.trans Refines.eq_symm ?_
  refine Refines.trans ?_ (Refines.sem_eq hO (hO.bv_sub unchecked _ _) Refines.refl)
  exact Refines.eq_bin_move (Or.inr (Or.inl ⟨_, rfl⟩)) (Or.inr (Or.inl ⟨_, rfl⟩)) (fun _ _ _ e => evBinop_sub_some e) (fun _ _ _ => evBinop_sub_unchecked) _ _ _
      (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr rfl)) (fun _ _ a x y ha hp hq => ⟨_, _, _, hp, ha, hq, by grind⟩)

theorem sem_eq.r_self_add_r.proof : sem_eq.r_self_add_r.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_self_add_r, equal] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> obtain ⟨rfl, rfl⟩ := h
  all_goals
    refine Refines.eq_const (fun _ _ _ => by simp) (fun ρ X Y hT w1 w2 hx hy => ?_)
    rw [eval_binop w2] at hy
    obtain ⟨n, a, b, e1, e2, rfl⟩ := evBinop_add_some hy
    have ⟨_, w3, w4⟩ := WT_binop.1 w2
  · rw [hx] at e1; cases e1
    obtain ⟨hb, h1, h2, _⟩ := eval_lit_bv w4 e2
    subst hb
    simp [self_eq_add_lit_iff a h1 h2]
  · rw [hx] at e2; cases e2
    obtain ⟨hb, h1, h2, _⟩ := eval_lit_bv w3 e1
    subst hb
    simp [self_eq_lit_add_iff b h1 h2]

theorem sem_eq.r_self_add_l.proof : sem_eq.r_self_add_l.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_self_add_l, equal] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> obtain ⟨rfl, rfl⟩ := h
  all_goals
    refine Refines.trans Refines.eq_symm ?_
    refine Refines.eq_const (fun _ _ _ => by simp) (fun ρ X Y hT w1 w2 hx hy => ?_)
    rw [eval_binop w2] at hy
    obtain ⟨n, a, b, e1, e2, rfl⟩ := evBinop_add_some hy
    have ⟨_, w3, w4⟩ := WT_binop.1 w2
  · rw [hx] at e1; cases e1
    obtain ⟨hb, h1, h2, _⟩ := eval_lit_bv w4 e2
    subst hb
    simp [self_eq_add_lit_iff a h1 h2]
  · rw [hx] at e2; cases e2
    obtain ⟨hb, h1, h2, _⟩ := eval_lit_bv w3 e1
    subst hb
    simp [self_eq_lit_add_iff b h1 h2]

theorem sem_eq.r_add_add.proof : sem_eq.r_add_add.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_add_add] at h
  have fin : ∀ x y l r, Refines FS (sem_eq.spec x (bv_add.spec unchecked y (bv_sub.spec unchecked l r)))
      (O.sem_eq x (O.bv_add unchecked y (O.bv_sub unchecked l r))) := fun x y l r =>
    Refines.sem_eq hO Refines.refl
      (Refines.trans (Refines.binop Refines.refl (hO.bv_sub _ _ _) (fun _ => rfl)) (hO.bv_add _ _ _))
  rcases orElse_eq_some4 h with h | h | h | h
  all_goals split at h <;> simp at h; subst h; split
  all_goals refine Refines.trans ?_ (fin _ _ _ _)
  · exact Refines.eq_add_add _ _ _ _ (by simp) (by simp) (by simp) (by simp)
      (fun _ _ a1 b1 a2 b2 h1 h2 h3 h4 => ⟨_, _, _, _, h4, h2, h1, h3, by grind⟩)
  · exact Refines.eq_add_add _ _ _ _ (by simp) (by simp) (by simp) (by simp)
      (fun _ _ a1 b1 a2 b2 h1 h2 h3 h4 => ⟨_, _, _, _, h2, h4, h3, h1, by grind⟩)
  · exact Refines.eq_add_add _ _ _ _ (by simp) (by simp) (by simp) (by simp)
      (fun _ _ a1 b1 a2 b2 h1 h2 h3 h4 => ⟨_, _, _, _, h3, h2, h1, h4, by grind⟩)
  · exact Refines.eq_add_add _ _ _ _ (by simp) (by simp) (by simp) (by simp)
      (fun _ _ a1 b1 a2 b2 h1 h2 h3 h4 => ⟨_, _, _, _, h2, h3, h4, h1, by grind⟩)
  · exact Refines.eq_add_add _ _ _ _ (by simp) (by simp) (by simp) (by simp)
      (fun _ _ a1 b1 a2 b2 h1 h2 h3 h4 => ⟨_, _, _, _, h4, h1, h2, h3, by grind⟩)
  · exact Refines.eq_add_add _ _ _ _ (by simp) (by simp) (by simp) (by simp)
      (fun _ _ a1 b1 a2 b2 h1 h2 h3 h4 => ⟨_, _, _, _, h1, h4, h3, h2, by grind⟩)
  · exact Refines.eq_add_add _ _ _ _ (by simp) (by simp) (by simp) (by simp)
      (fun _ _ a1 b1 a2 b2 h1 h2 h3 h4 => ⟨_, _, _, _, h3, h1, h2, h4, by grind⟩)
  · exact Refines.eq_add_add _ _ _ _ (by simp) (by simp) (by simp) (by simp)
      (fun _ _ a1 b1 a2 b2 h1 h2 h3 h4 => ⟨_, _, _, _, h1, h3, h4, h2, by grind⟩)

theorem sem_eq.r_mul_const.proof : sem_eq.r_mul_const.Stmt := by
  sorry

theorem sem_eq.r_ite_ite.proof : sem_eq.r_ite_ite.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_ite_ite, equal] at h
  split at h <;> simp at h
  obtain ⟨rfl, rfl⟩ := h
  exact Refines.trans Refines.eq_ite_ite (Refines.b_ite hO Refines.refl (hO.sem_eq _ _) (hO.sem_eq _ _))

theorem sem_eq.r_mul_cancel.proof : sem_eq.r_mul_cancel.Stmt := by
  sorry

theorem sem_eq.r_or_zero.proof : sem_eq.r_or_zero.Stmt := by
  sorry

theorem sem_eq.r_and_mask.proof : sem_eq.r_and_mask.Stmt := by
  sorry

theorem sem_eq.r_concat_const.proof : sem_eq.r_concat_const.Stmt := by
  sorry

theorem sem_eq.r_zext_const.proof : sem_eq.r_zext_const.Stmt := by
  sorry

theorem sem_eq.r_ite_concat.proof : sem_eq.r_ite_concat.Stmt := by
  sorry

theorem sem_eq.r_concat_concat.proof : sem_eq.r_concat_concat.Stmt := by
  sorry

theorem sem_eq.r_ite_const_l.proof : sem_eq.r_ite_const_l.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_ite_const_l] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> subst h <;>
    exact Refines.trans Refines.eq_ite_l
      (Refines.b_ite hO Refines.refl (hO.sem_eq _ _) (hO.sem_eq _ _))

theorem sem_eq.r_ite_const_r.proof : sem_eq.r_ite_const_r.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_ite_const_r] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> subst h <;>
    exact Refines.trans Refines.eq_ite_r
      (Refines.b_ite hO Refines.refl (hO.sem_eq _ _) (hO.sem_eq _ _))

theorem sem_eq.r_false_l.proof : sem_eq.r_false_l.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_false_l] at h
  split at h <;> simp at h
  subst h
  refine Refines.trans ?_ (hO.b_not _)
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨h1, w1, w2⟩ := WT_sem_eq.1 w
    have := WT_bool.1 w1
    refine ⟨WT_unop.2 ⟨?_, w2⟩, rfl⟩
    simp_all [Unop.WT]
  · obtain ⟨h1, w1, w2⟩ := WT_sem_eq.1 w
    obtain ⟨x, y, hx, hy, rfl⟩ := eval_eq_some e
    rw [eval_bool (WT_bool.1 w1)] at hx; cases hx
    obtain ⟨b, rfl⟩ := eval_bool_val hy (by simp_all [WT_bool])
    rw [b_not.spec, eval_unop w', hy]; cases b <;> simp [evUnop]

theorem sem_eq.r_false_r.proof : sem_eq.r_false_r.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_false_r] at h
  split at h <;> simp at h
  subst h
  refine Refines.trans ?_ (hO.b_not _)
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨h1, w1, w2⟩ := WT_sem_eq.1 w
    have := WT_bool.1 w2
    refine ⟨WT_unop.2 ⟨?_, w1⟩, rfl⟩
    simp_all [Unop.WT]
  · obtain ⟨h1, w1, w2⟩ := WT_sem_eq.1 w
    obtain ⟨x, y, hx, hy, rfl⟩ := eval_eq_some e
    rw [eval_bool (WT_bool.1 w2)] at hy; cases hy
    obtain ⟨b, rfl⟩ := eval_bool_val hx (by simp_all [WT_bool])
    rw [b_not.spec, eval_unop w', hx]; cases b <;> simp [evUnop]

theorem sem_eq.r_true_l.proof : sem_eq.r_true_l.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_true_l] at h
  split at h <;> simp at h
  subst h
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨h1, w1, w2⟩ := WT_sem_eq.1 w
    have := WT_bool.1 w1
    simp_all
  · obtain ⟨h1, w1, w2⟩ := WT_sem_eq.1 w
    obtain ⟨x, y, hx, hy, rfl⟩ := eval_eq_some e
    rw [eval_bool (WT_bool.1 w1)] at hx; cases hx
    obtain ⟨b, rfl⟩ := eval_bool_val hy (by simp_all [WT_bool])
    rw [hy]; cases b <;> simp

theorem sem_eq.r_true_r.proof : sem_eq.r_true_r.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_true_r] at h
  split at h <;> simp at h
  subst h
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨h1, w1, w2⟩ := WT_sem_eq.1 w
    have := WT_bool.1 w2
    simp_all
  · obtain ⟨h1, w1, w2⟩ := WT_sem_eq.1 w
    obtain ⟨x, y, hx, hy, rfl⟩ := eval_eq_some e
    rw [eval_bool (WT_bool.1 w2)] at hy; cases hy
    obtain ⟨b, rfl⟩ := eval_bool_val hx (by simp_all [WT_bool])
    rw [hx]; cases b <;> simp

theorem sem_eq.r_of_bools.proof : sem_eq.r_of_bools.Stmt := by
  sorry

theorem sem_eq.r_nots.proof : sem_eq.r_nots.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_nots] at h
  split at h <;> simp at h
  subst h
  refine Refines.trans ?_ (hO.sem_eq _ _)
  refine Refines.eq_eq (fun hT w1 w2 => ?_) (fun ρ x y hT w1 w2 hx hy => ?_)
  · have ⟨h1, wb⟩ := WT_unop.1 w1
    have ⟨h2, wc⟩ := WT_unop.1 w2
    simp [Unop.WT] at h1 h2
    exact ⟨by rw [h1.1, h2.1], wb, wc⟩
  · have ⟨h1, wb⟩ := WT_unop.1 w1
    have ⟨h2, wc⟩ := WT_unop.1 w2
    rw [eval_unop w1] at hx; rw [eval_unop w2] at hy
    cases hb : eval FS ρ _ <;> rw [hb] at hx <;> simp [evUnop] at hx
    cases hc : eval FS ρ _ <;> rw [hc] at hy <;> simp [evUnop] at hy
    rename_i vb vc
    rcases vb with _ | _ | _ | _ | _ | _ <;> simp [evUnop] at hx
    rcases vc with _ | _ | _ | _ | _ | _ <;> simp [evUnop] at hy
    subst hx hy
    exact ⟨_, _, rfl, rfl, by simp⟩

theorem sem_eq.r_of_bool_const.proof : sem_eq.r_of_bool_const.Stmt := by
  sorry

theorem sem_eq.r_msb.proof : sem_eq.r_msb.Stmt := by
  sorry

theorem sem_eq.r_default.proof : sem_eq.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_default, mk_commut_binop, Option.some.injEq] at h
  subst h
  split
  · exact Refines.refl
  · exact Refines.eq_eq (fun h a b => ⟨h.symm, b, a⟩)
      (fun ρ x y _ _ _ hx hy => ⟨y, x, hy, hx, eq_comm⟩)

theorem float_is_floatclass.r_lit.proof : float_is_floatclass.r_lit.Stmt := by
  intro FS O hO fc v res h
  simp only [float_is_floatclass.r_lit] at h
  split at h <;> simp at h
  subst h
  exact Refines.test_of_unop (fun w => ((WT_ftest (Or.inr (Or.inr ⟨fc, rfl⟩))).1 w).2.1)
    (by simp [evUnop, FloatLit.sem, f_is_class])

theorem float_is_floatclass.r_default.proof : float_is_floatclass.r_default.Stmt := by
  intro FS O hO fc v res h
  simp [float_is_floatclass.r_default] at h; subst h
  exact Refines.refl

theorem float_is_negative.r_lit.proof : float_is_negative.r_lit.Stmt := by
  intro FS O hO v res h
  simp only [float_is_negative.r_lit] at h
  split at h <;> simp at h
  subst h
  exact Refines.test_of_unop (fun w => ((WT_ftest (Or.inl rfl)).1 w).2.1)
    (by simp [evUnop, FloatLit.sem, f_is_negative])

theorem float_is_negative.r_default.proof : float_is_negative.r_default.Stmt := by
  intro FS O hO v res h
  simp [float_is_negative.r_default] at h; subst h
  exact Refines.refl

theorem float_is_positive.r_lit.proof : float_is_positive.r_lit.Stmt := by
  intro FS O hO v res h
  simp only [float_is_positive.r_lit] at h
  split at h <;> simp at h
  subst h
  exact Refines.test_of_unop (fun w => ((WT_ftest (Or.inr (Or.inl rfl))).1 w).2.1)
    (by simp [evUnop, FloatLit.sem, f_is_positive])

theorem float_is_positive.r_default.proof : float_is_positive.r_default.Stmt := by
  intro FS O hO v res h
  simp [float_is_positive.r_default] at h; subst h
  exact Refines.refl

theorem float_cast.r_lit.proof : float_cast.r_lit.Stmt := by
  intro FS O hO rm fp v res h
  simp only [float_cast.r_lit] at h
  split at h <;> simp at h
  subst h
  rename_i f T
  refine Refines.lit_of_unop (fun w => ?_) (fun hf => (hO.orc.convert rm fp f hf).2.2)
  have ⟨w1, w2⟩ := WT_unop.1 w
  have := hO.orc.convert rm fp f (FloatLit.WF_of_WT w2)
  exact ⟨by rw [this.1], this.2.1⟩

theorem float_cast.r_default.proof : float_cast.r_default.Stmt := by
  intro FS O hO rm fp v res h
  simp [float_cast.r_default] at h; subst h
  exact Refines.refl

theorem float_eq.r_lits.proof : float_eq.r_lits.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [float_eq.r_lits] at h
  split at h <;> simp at h
  subst h
  rename_i f1 T1 f2 T2
  refine Refines.intro (fun w => ⟨by simp, by simp [float_eq.spec]⟩) (fun ρ v w w' e => ?_)
  have ⟨_, w1, w2⟩ := WT_binop.1 w
  rw [float_eq.spec, eval_binop w, eval_float w1, eval_float w2] at e
  have hp : f2.prec = f1.prec := by
    obtain ⟨_, h2, _⟩ := (WT_fcmp (Or.inl rfl)).1 w
    rw [(WT_float.1 w1).1, (WT_float.1 w2).1] at h2; simpa using h2
  rw [eval_of_bool]; rw [← e]
  simp [evBinop, fBin, FloatLit.sem, f_eq, FloatLit.cmp, hp]

theorem float_eq.r_same.proof : float_eq.r_same.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [float_eq.r_same, equal] at h
  by_cases hv : v1 = v2 <;> simp [hv] at h
  subst h hv
  refine Refines.trans ?_ (Refines.b_not hO (hO.float_is_floatclass .nan v1))
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

theorem float_eq.r_lit_l.proof : float_eq.r_lit_l.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [float_eq.r_lit_l] at h
  split at h <;> simp at h
  subst h
  rename_i f T
  have ev1 : ∀ ρ v, eval FS ρ (float_eq.spec (.mk (.float f) T) v2) = some v →
      ∃ y, eval FS ρ v2 = some (.float f.prec y) ∧ v = .bool (f.val.eq y) := by
    intro ρ v e
    have w := eval_WT e
    have ⟨_, w1, _⟩ := WT_binop.1 w
    rw [float_eq.spec, eval_binop w, eval_float w1] at e
    simp only [evBinop, fBin_eq_some, FloatLit.sem] at e
    obtain ⟨p, x, y, h1, h2, h3⟩ := e
    simp at h1; obtain ⟨rfl, h1⟩ := h1; subst h1
    simp at h3
    exact ⟨y, h2, h3.symm⟩
  split
  · rename_i hn
    refine Refines.intro (fun w => ⟨by simp, by simp [float_eq.spec]⟩) (fun ρ v w w' e => ?_)
    obtain ⟨y, _, rfl⟩ := ev1 ρ v e
    simp [FBits.eq_of_isNaN_left y (by simpa [f_is_nan] using hn)]
  · rename_i hn
    split
    · rename_i hz
      refine Refines.trans ?_ (hO.float_is_floatclass .zero v2)
      refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
      · obtain ⟨hp, h2, _, w1, w2⟩ := (WT_fcmp (Or.inl rfl)).1 w
        refine ⟨WT_unop.2 ⟨by simpa [Unop.WT, h2] using hp, w2⟩, rfl⟩
      · obtain ⟨y, hy, rfl⟩ := ev1 ρ v e
        rw [float_is_floatclass.spec, eval_unop w', hy]
        simp [evUnop, FBits.isClass, FBits.eq_of_isZero_left y hz]
    · rename_i hz
      refine Refines.trans ?_ (hO.sem_eq _ v2)
      refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
      · obtain ⟨hp, h2, _, w1, w2⟩ := (WT_fcmp (Or.inl rfl)).1 w
        exact ⟨WT_sem_eq.2 ⟨h2.symm, w1, w2⟩, rfl⟩
      · obtain ⟨y, hy, rfl⟩ := ev1 ρ v e
        have ⟨_, w1, _⟩ := WT_binop.1 w'
        rw [sem_eq.spec, eval_eq_of w' (eval_float w1) hy]
        simp only [f_is_nan, f_is_zero, Bool.not_eq_true] at hn hz
        simp [FloatLit.sem, FBits.eq_of_ne_left y hn hz]

theorem float_eq.r_lit_r.proof : float_eq.r_lit_r.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [float_eq.r_lit_r] at h
  split at h <;> simp at h
  subst h
  rename_i f T
  have ev1 : ∀ ρ v, eval FS ρ (float_eq.spec v1 (.mk (.float f) T)) = some v →
      ∃ y, eval FS ρ v1 = some (.float f.prec y) ∧ v = .bool (y.eq f.val) := by
    intro ρ v e
    have w := eval_WT e
    have ⟨_, _, w2⟩ := WT_binop.1 w
    rw [float_eq.spec, eval_binop w, eval_float w2] at e
    simp only [evBinop, fBin_eq_some, FloatLit.sem] at e
    obtain ⟨p, x, y, h1, h2, h3⟩ := e
    simp at h2; obtain ⟨rfl, h2⟩ := h2; subst h2
    simp at h3
    exact ⟨x, h1, h3.symm⟩
  split
  · rename_i hn
    refine Refines.intro (fun w => ⟨by simp, by simp [float_eq.spec]⟩) (fun ρ v w w' e => ?_)
    obtain ⟨y, _, rfl⟩ := ev1 ρ v e
    simp [FBits.eq_of_isNaN_right y (by simpa [f_is_nan] using hn)]
  · rename_i hn
    split
    · rename_i hz
      refine Refines.trans ?_ (hO.float_is_floatclass .zero v1)
      refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
      · obtain ⟨hp, h2, _, w1, w2⟩ := (WT_fcmp (Or.inl rfl)).1 w
        refine ⟨WT_unop.2 ⟨by simpa [Unop.WT] using hp, w1⟩, rfl⟩
      · obtain ⟨y, hy, rfl⟩ := ev1 ρ v e
        rw [float_is_floatclass.spec, eval_unop w', hy]
        simp [evUnop, FBits.isClass, FBits.eq_of_isZero_right y hz]
    · rename_i hz
      refine Refines.trans ?_ (hO.sem_eq v1 _)
      refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
      · obtain ⟨hp, h2, _, w1, w2⟩ := (WT_fcmp (Or.inl rfl)).1 w
        exact ⟨WT_sem_eq.2 ⟨h2.symm, w1, w2⟩, rfl⟩
      · obtain ⟨y, hy, rfl⟩ := ev1 ρ v e
        have ⟨_, _, w2⟩ := WT_binop.1 w'
        rw [sem_eq.spec, eval_eq_of w' hy (eval_float w2)]
        simp only [f_is_nan, f_is_zero, Bool.not_eq_true] at hn hz
        rw [FBits.eq_comm']
        simp [FloatLit.sem, FBits.eq_of_ne_left y hn hz, eq_comm]

theorem float_eq.r_default.proof : float_eq.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [float_eq.r_default, mk_commut_binop, Option.some.injEq] at h
  subst h
  split
  · exact Refines.refl
  · refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
    · obtain ⟨⟨p, hp⟩, h2, _, w1, w2⟩ := (WT_fcmp (Or.inl rfl)).1 w
      refine ⟨(WT_fcmp (Or.inl rfl)).2 ⟨⟨p, h2 ▸ hp⟩, h2.symm, rfl, w2, w1⟩, rfl⟩
    · rw [float_eq.spec, eval_binop w] at e
      rw [eval_binop w']
      simp only [evBinop, fBin_eq_some] at e ⊢
      obtain ⟨p, x, y, h1, h2, h3⟩ := e
      exact ⟨p, y, x, h2, h1, by rw [FBits.eq_comm']; exact h3⟩

theorem float_lt.r_lits.proof : float_lt.r_lits.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [float_lt.r_lits] at h
  split at h <;> simp at h
  subst h
  rename_i f1 T1 f2 T2
  refine Refines.intro (fun w => ⟨by simp, by simp [float_lt.spec]⟩) (fun ρ v w w' e => ?_)
  have ⟨_, w1, w2⟩ := WT_binop.1 w
  rw [float_lt.spec, eval_binop w, eval_float w1, eval_float w2] at e
  have hp : f2.prec = f1.prec := by
    obtain ⟨_, h2, _⟩ := (WT_fcmp (Or.inr (Or.inl rfl))).1 w
    rw [(WT_float.1 w1).1, (WT_float.1 w2).1] at h2; simpa using h2
  rw [eval_of_bool]; rw [← e]
  simp [evBinop, fBin, FloatLit.sem, f_lt, FloatLit.cmp, hp]

theorem float_lt.r_default.proof : float_lt.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp [float_lt.r_default] at h; subst h
  exact Refines.refl

theorem float_leq.r_lits.proof : float_leq.r_lits.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [float_leq.r_lits] at h
  split at h <;> simp at h
  subst h
  rename_i f1 T1 f2 T2
  refine Refines.intro (fun w => ⟨by simp, by simp [float_leq.spec]⟩) (fun ρ v w w' e => ?_)
  have ⟨_, w1, w2⟩ := WT_binop.1 w
  rw [float_leq.spec, eval_binop w, eval_float w1, eval_float w2] at e
  have hp : f2.prec = f1.prec := by
    obtain ⟨_, h2, _⟩ := (WT_fcmp (Or.inr (Or.inr rfl))).1 w
    rw [(WT_float.1 w1).1, (WT_float.1 w2).1] at h2; simpa using h2
  rw [eval_of_bool]; rw [← e]
  simp [evBinop, fBin, FloatLit.sem, f_le, FloatLit.cmp, hp]

theorem float_leq.r_default.proof : float_leq.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp [float_leq.r_default] at h; subst h
  exact Refines.refl

theorem float_add.r_lits.proof : float_add.r_lits.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [float_add.r_lits] at h
  split at h <;> simp at h
  subst h
  exact Refines.float_bin_lits hO (by simp)

theorem float_add.r_default.proof : float_add.r_default.Stmt := by
  -- UNSOUND: when `tag_le v1 v2 = false` the result is `fAdd v2 v1`, but `FS.add` need not
  -- be commutative on bit patterns: with two NaN operands, which payload propagates is
  -- implementation-defined (x86 SSE `addss` returns the first operand's). Counterexample:
  -- `FS.add p x y := x` (quiet-NaN propagation of the first operand), `O := opsRaw orc` with
  -- `orc.tag_le := fun _ _ => false` and `orc.f_add f1 f2 := f1` (so `O.Sound FS`),
  -- v1 = var 0 : float f32, v2 = var 1 : float f32, ρ.var 0 = float f32 0x7fc00001,
  -- ρ.var 1 = float f32 0x7fc00002. The spec `fAdd v1 v2` evaluates to 0x7fc00001, the
  -- result `fAdd v2 v1` to 0x7fc00002.
  sorry

theorem float_sub.r_lits.proof : float_sub.r_lits.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [float_sub.r_lits] at h
  split at h <;> simp at h
  subst h
  exact Refines.float_bin_lits hO (by simp)

theorem float_sub.r_default.proof : float_sub.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp [float_sub.r_default] at h; subst h
  exact Refines.refl

theorem float_div.r_lits.proof : float_div.r_lits.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [float_div.r_lits] at h
  split at h <;> simp at h
  subst h
  exact Refines.float_bin_lits hO (by simp)

theorem float_div.r_default.proof : float_div.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp [float_div.r_default] at h; subst h
  exact Refines.refl

theorem float_mul.r_lits.proof : float_mul.r_lits.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [float_mul.r_lits] at h
  split at h <;> simp at h
  subst h
  exact Refines.float_bin_lits hO (by simp)

theorem float_mul.r_default.proof : float_mul.r_default.Stmt := by
  -- UNSOUND: as for `float_add.r_default`, the operands may be swapped (`fMul v2 v1`), but
  -- `FS.mul` need not be commutative on NaN payloads. Counterexample: `FS.mul p x y := x`,
  -- `O := opsRaw orc` with `orc.tag_le := fun _ _ => false` and `orc.f_mul f1 f2 := f1`,
  -- v1 = var 0, v2 = var 1 : float f32 with values 0x7fc00001 and 0x7fc00002: the spec
  -- evaluates to 0x7fc00001, the result to 0x7fc00002.
  sorry

theorem float_rem.r_lits.proof : float_rem.r_lits.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [float_rem.r_lits] at h
  split at h <;> simp at h
  subst h
  exact Refines.float_bin_lits hO (by simp)

theorem float_rem.r_default.proof : float_rem.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp [float_rem.r_default] at h; subst h
  exact Refines.refl

theorem float_abs.r_lit.proof : float_abs.r_lit.Stmt := by
  intro FS O hO v res h
  simp only [float_abs.r_lit] at h
  split at h <;> simp at h
  subst h
  rename_i f T
  refine Refines.lit_of_unop (fun w => ?_) (fun hf => ?_)
  · have ⟨w1, w2⟩ := WT_unop.1 w
    obtain ⟨rfl, _⟩ := WT_float.1 w2
    simp [Unop.WT] at w1
    exact ⟨by simp [f_abs], by simp only [f_abs, FloatLit.WF]; exact BitVec.isLt _⟩
  · simp [evUnop, FloatLit.sem, f_abs, FloatLit.val_ofNat_toNat]

theorem float_abs.r_abs.proof : float_abs.r_abs.Stmt := by
  intro FS O hO v res h
  simp only [float_abs.r_abs] at h
  split at h <;> simp at h
  subst h
  rename_i y T
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · exact ⟨(WT_unop.1 w).2, rfl⟩
  · rw [float_abs.spec, eval_unop w, eval_unop w'] at e
    rw [eval_unop w']
    cases hy : eval FS ρ y with
    | none => simp [hy] at e
    | some x =>
      rw [hy] at e
      rcases x with _ | _ | _ | ⟨p, x⟩ | _ | _ <;> simp [evUnop] at e
      simp [evUnop, ← e, FBits.abs_abs]

theorem float_abs.r_default.proof : float_abs.r_default.Stmt := by
  intro FS O hO v res h
  simp [float_abs.r_default] at h; subst h
  exact Refines.refl

theorem float_neg.r_lit.proof : float_neg.r_lit.Stmt := by
  intro FS O hO v res h
  simp only [float_neg.r_lit] at h
  split at h <;> simp at h
  subst h
  rename_i f T
  refine Refines.lit_of_unop (fun w => ?_) (fun hf => ?_)
  · have ⟨w1, w2⟩ := WT_unop.1 w
    obtain ⟨rfl, _⟩ := WT_float.1 w2
    simp [Unop.WT] at w1
    exact ⟨by simp [f_neg], by simp only [f_neg, FloatLit.WF]; exact BitVec.isLt _⟩
  · simp [evUnop, FloatLit.sem, f_neg, FloatLit.val_ofNat_toNat]

theorem float_neg.r_neg.proof : float_neg.r_neg.Stmt := by
  intro FS O hO v res h
  simp only [float_neg.r_neg] at h
  split at h <;> simp at h
  subst h
  rename_i y T
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · have ⟨w1, w2⟩ := WT_unop.1 w
    have ⟨w3, w4⟩ := WT_unop.1 w2
    simp [Unop.WT] at w1 w3
    exact ⟨w4, by simp [float_neg.spec, w3.2]⟩
  · have ⟨w1, w2⟩ := WT_unop.1 w
    rw [float_neg.spec, eval_unop w, eval_unop w2] at e
    cases hy : eval FS ρ y with
    | none => simp [hy] at e
    | some x =>
      rw [hy] at e
      rcases x with _ | _ | _ | ⟨p, x⟩ | _ | _ <;> simp [evUnop] at e
      simp [← e, FBits.neg_neg]

theorem float_neg.r_default.proof : float_neg.r_default.Stmt := by
  intro FS O hO v res h
  simp [float_neg.r_default] at h; subst h
  exact Refines.refl

theorem float_fma.r_lits.proof : float_fma.r_lits.Stmt := by
  intro FS O hO a b c res h
  simp only [float_fma.r_lits] at h
  split at h <;> simp at h
  subst h
  rename_i fa Ta fb Tb fc Tc
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

theorem float_fma.r_default.proof : float_fma.r_default.Stmt := by
  intro FS O hO a b c res h
  simp [float_fma.r_default] at h; subst h
  exact Refines.refl

theorem float_fmod_of_rem.r_main.proof : float_fmod_of_rem.r_main.Stmt := by
  intro FS O hO r v1 v2 res h
  simp only [float_fmod_of_rem.r_main, Option.some.injEq] at h
  subst h
  have neg : Refines FS (.mk (.unop .fNeg (.mk (.unop .fAbs v2) (ty v2))) (ty v2))
      (O.float_neg (O.float_abs v2)) := by
    refine Refines.trans (Refines.unop (hO.float_abs v2) (fun w => ?_)) (hO.float_neg _)
    exact ((hO.float_abs v2).syn (WT_unop.1 w).2).2
  have corr := Refines.b_ite hO (hO.float_is_negative v1) neg (hO.float_abs v2)
  have add : Refines FS (.mk (.binop .fAdd r (b_ite.spec (float_is_negative.spec v1)
      (.mk (.unop .fNeg (.mk (.unop .fAbs v2) (ty v2))) (ty v2)) (float_abs.spec v2))) (ty r))
      (O.float_add r (O.b_ite (O.float_is_negative v1) (O.float_neg (O.float_abs v2))
        (O.float_abs v2))) :=
    Refines.trans (Refines.binop Refines.refl corr (fun _ => rfl)) (hO.float_add _ _)
  exact Refines.b_ite hO (Refines.sem_eq hO (hO.float_is_negative r) (hO.float_is_negative v1))
    Refines.refl add

theorem float_fmod.r_lits.proof : float_fmod.r_lits.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [float_fmod.r_lits] at h
  split at h <;> simp at h
  subst h
  rename_i f1 T1 f2 T2
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

theorem float_fmod.r_default.proof : float_fmod.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [float_fmod.r_default, Option.some.injEq] at h
  subst h
  exact Refines.trans (Refines.raw_fmod (hO.float_rem v1 v2)) (hO.float_fmod_of_rem _ v1 v2)

theorem float_min.r_lits.proof : float_min.r_lits.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [float_min.r_lits] at h
  split at h <;> simp at h
  subst h
  exact Refines.float_bin_lits hO (by simp)

theorem float_min.r_default.proof : float_min.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp [float_min.r_default] at h; subst h
  exact Refines.refl

theorem float_max.r_lits.proof : float_max.r_lits.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [float_max.r_lits] at h
  split at h <;> simp at h
  subst h
  exact Refines.float_bin_lits hO (by simp)

theorem float_max.r_default.proof : float_max.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp [float_max.r_default] at h; subst h
  exact Refines.refl

theorem float_sqrt.r_lit.proof : float_sqrt.r_lit.Stmt := by
  intro FS O hO v res h
  simp only [float_sqrt.r_lit] at h
  split at h <;> simp at h
  subst h
  rename_i f T
  refine Refines.lit_of_unop (fun w => ?_) (fun hf => (hO.orc.sqrt f hf).2.2)
  have ⟨w1, w2⟩ := WT_unop.1 w
  obtain ⟨rfl, _⟩ := WT_float.1 w2
  have := hO.orc.sqrt f (FloatLit.WF_of_WT w2)
  simp [Unop.WT] at w1
  exact ⟨by simp [this.1], this.2.1⟩

theorem float_sqrt.r_default.proof : float_sqrt.r_default.Stmt := by
  intro FS O hO v res h
  simp [float_sqrt.r_default] at h; subst h
  exact Refines.refl

theorem float_round.r_lit.proof : float_round.r_lit.Stmt := by
  intro FS O hO rm v res h
  simp only [float_round.r_lit] at h
  split at h <;> simp at h
  subst h
  rename_i f T
  refine Refines.lit_of_unop (fun w => ?_) (fun hf => (hO.orc.round rm f hf).2.2)
  have ⟨w1, w2⟩ := WT_unop.1 w
  obtain ⟨rfl, _⟩ := WT_float.1 w2
  have := hO.orc.round rm f (FloatLit.WF_of_WT w2)
  simp [Unop.WT] at w1
  exact ⟨by simp [this.1], this.2.1⟩

theorem float_round.r_default.proof : float_round.r_default.Stmt := by
  intro FS O hO rm v res h
  simp [float_round.r_default] at h; subst h
  exact Refines.refl

theorem ptr_loc.r_ptr.proof : ptr_loc.r_ptr.Stmt := by
  intro FS O hO p res h
  simp only [ptr_loc.r_ptr] at h
  split at h <;> simp at h
  subst h
  rename_i l o T
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · have ⟨w1, w2⟩ := WT_unop.1 w
    obtain ⟨n, hn, rfl, hl, ho, wl, wo⟩ := WT_ptr.1 w2
    simp [ptr_loc.spec, hl, wl, size_of_ty]
  · have ⟨w1, w2⟩ := WT_unop.1 w
    rw [ptr_loc.spec, eval_unop w] at e
    cases hp : eval FS ρ (Term.mk (Kind.ptr l o) T) with
    | none => simp [hp] at e
    | some pv =>
      obtain ⟨n, x, y, h1, h2, rfl⟩ := (eval_ptr_eq_some w2).1 hp
      rw [hp] at e; simp [evUnop] at e; subst e; exact h1

theorem ptr_loc.r_default.proof : ptr_loc.r_default.Stmt := by
  intro FS O hO p res h
  simp [ptr_loc.r_default] at h; subst h
  exact Refines.refl

theorem ptr_ofs.r_ptr.proof : ptr_ofs.r_ptr.Stmt := by
  intro FS O hO p res h
  simp only [ptr_ofs.r_ptr] at h
  split at h <;> simp at h
  subst h
  rename_i l o T
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · have ⟨w1, w2⟩ := WT_unop.1 w
    obtain ⟨n, hn, rfl, hl, ho, wl, wo⟩ := WT_ptr.1 w2
    simp [ptr_ofs.spec, ho, wo, size_of_ty]
  · have ⟨w1, w2⟩ := WT_unop.1 w
    rw [ptr_ofs.spec, eval_unop w] at e
    cases hp : eval FS ρ (Term.mk (Kind.ptr l o) T) with
    | none => simp [hp] at e
    | some pv =>
      obtain ⟨n, x, y, h1, h2, rfl⟩ := (eval_ptr_eq_some w2).1 hp
      rw [hp] at e; simp [evUnop] at e; subst e; exact h2

theorem ptr_ofs.r_default.proof : ptr_ofs.r_default.Stmt := by
  intro FS O hO p res h
  simp [ptr_ofs.r_default] at h; subst h
  exact Refines.refl

end Bvr
