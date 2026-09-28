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
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_ptrs] at h
  split at h <;> simp at h
  subst h
  refine Refines.trans ?_ (Refines.b_and hO (hO.sem_eq _ _) (hO.sem_eq _ _))
  refine Refines.eq_and (fun hT w1 w2 => ?_) (fun ρ x y hT w1 w2 hx hy => ?_)
  · obtain ⟨n, _, rfl, hl, ho, wl, wo⟩ := WT_ptr.1 w1
    obtain ⟨m, _, hm, hl', ho', wl', wo'⟩ := WT_ptr.1 w2
    simp only [Term.ty_mk] at hT hm; rw [← hT] at hm; cases hm
    exact ⟨by rw [hl, hl'], wl, wl', by rw [ho, ho'], wo, wo'⟩
  · obtain ⟨n, x1, y1, e1, e2, rfl⟩ := (eval_ptr_eq_some w1).1 hx
    obtain ⟨m, x2, y2, e3, e4, rfl⟩ := (eval_ptr_eq_some w2).1 hy
    obtain ⟨N, _, hN, hl, _⟩ := WT_ptr.1 w1
    obtain ⟨M, _, hM, hl', _⟩ := WT_ptr.1 w2
    simp only [Term.ty_mk] at hT hN hM
    rw [hT, hM] at hN; cases hN
    obtain ⟨_, _, h1⟩ := eval_bv_of_ty e1 (Or.inr hl)
    obtain ⟨_, _, h2⟩ := eval_bv_of_ty e3 (Or.inr hl')
    simp only [Val.bv.injEq] at h1 h2
    have : m = n := by omega
    subst this
    refine ⟨_, _, _, _, e1, e3, e2, e4, ?_⟩
    simp

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
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_mul_const] at h
  rcases orElse_eq_some4 h with h | h | h | h <;> split at h <;>
    simp only [reduceCtorEq, Option.ite_none_right_eq_some, Option.some.injEq] at h <;>
    obtain ⟨hck, rfl⟩ := h
  · exact Refines.eq_mul_const hO (Or.inl ⟨rfl, rfl⟩) hck
  · exact Refines.eq_mul_const hO (Or.inr ⟨rfl, rfl⟩) hck
  · exact Refines.trans Refines.eq_symm (Refines.eq_mul_const hO (Or.inl ⟨rfl, rfl⟩) hck)
  · exact Refines.trans Refines.eq_symm (Refines.eq_mul_const hO (Or.inr ⟨rfl, rfl⟩) hck)

theorem sem_eq.r_ite_ite.proof : sem_eq.r_ite_ite.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_ite_ite, equal] at h
  split at h <;> simp at h
  obtain ⟨rfl, rfl⟩ := h
  exact Refines.trans Refines.eq_ite_ite (Refines.b_ite hO Refines.refl (hO.sem_eq _ _) (hO.sem_eq _ _))

theorem sem_eq.r_mul_cancel.proof : sem_eq.r_mul_cancel.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_mul_cancel] at h
  rcases orElse_eq_some4 h with h | h | h | h <;> split at h <;>
    simp only [reduceCtorEq, Option.ite_none_right_eq_some, Option.some.injEq, Bool.and_eq_true,
      Bool.or_eq_true, decide_eq_true_eq] at h <;>
    obtain ⟨⟨rfl, hc⟩, rfl⟩ := h <;>
    refine Refines.trans ?_ (hO.sem_eq _ _)
  · exact Refines.eq_mul_cancel (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) hc
  · exact Refines.eq_mul_cancel (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) hc
  · exact Refines.eq_mul_cancel (Or.inr ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) hc
  · exact Refines.eq_mul_cancel (Or.inr ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) hc

theorem sem_eq.r_or_zero.aux {FS : FloatSem} {l r : Term} {T1 T2 : Ty} {N : Int}
    (hN : N = size_of_ty T1 ∨ N = size_of_ty T2) :
    Refines FS (sem_eq.spec (.mk (.bitVec 0) T1) (.mk (.binop .bitOr l r) T2))
      (b_and.spec (sem_eq.spec l (bv_zero N)) (sem_eq.spec r (bv_zero N))) := by
  have key : T1 = T2 → (Term.mk (.binop .bitOr l r) T2).WT →
      ∃ n : Int, 0 < n ∧ N = n ∧ l.ty = .bitVector n ∧ r.ty = .bitVector n ∧ T2 = .bitVector n ∧
        l.WT ∧ r.WT := by
    intro hT w2
    obtain ⟨⟨n, hn, hl⟩, hr, hT2, wl, wr⟩ := (WT_bvbin (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).1 w2
    subst hT
    refine ⟨n, hn, ?_, hl, by rw [hr, hl], by rw [hT2, hl], wl, wr⟩
    rcases hN with rfl | rfl <;> rw [hT2, hl] <;> rfl
  refine Refines.eq_and (fun hT w1 w2 => ?_) (fun ρ x y hT w1 w2 hx hy => ?_)
  · obtain ⟨n, hn, rfl, hl, hr, _, wl, wr⟩ := key (by simpa using hT) w2
    exact ⟨by simp [hl], wl, bv_zero_WT' hn, by simp [hr], wr, bv_zero_WT' hn⟩
  · simp only [Term.ty_mk] at hT
    obtain ⟨n, hn, rfl, hl, hr, hT2, wl, wr⟩ := key hT w2
    rw [eval_binop w2] at hy; simp only [evBinop] at hy
    obtain ⟨m, a, b, ha, hb, hab⟩ := bvBin_eq_some.1 hy
    simp only [Option.some.injEq] at hab; subst hab
    obtain ⟨rfl, _⟩ := eval_bv_ty ha hl
    rw [hT2] at hT; subst hT
    rw [eval_lit' w1] at hx; cases hx
    refine ⟨_, _, _, _, ha, eval_bv_zero'' hn, hb, eval_bv_zero'' hn, ?_⟩
    simp only [Val.bv.injEq, heq_eq_eq, true_and]
    rw [@eq_comm _ (BitVec.ofInt _ 0)]; simp [BitVec.or_eq_zero_iff]

theorem sem_eq.r_or_zero.proof : sem_eq.r_or_zero.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_or_zero] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp only [reduceCtorEq, Option.some.injEq, decide_eq_true_eq, Option.ite_none_right_eq_some] at h
  all_goals
    obtain ⟨rfl, rfl⟩ := h
    refine Refines.trans ?_ (Refines.b_and hO (hO.sem_eq _ _) (hO.sem_eq _ _))
  · exact sem_eq.r_or_zero.aux (Or.inl rfl)
  · exact Refines.trans Refines.eq_symm (sem_eq.r_or_zero.aux (Or.inr rfl))

theorem sem_eq.r_and_mask.proof : sem_eq.r_and_mask.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_and_mask] at h
  rcases orElse_eq_some4 h with h | h | h | h <;> split at h <;>
    simp only [reduceCtorEq, Option.ite_none_right_eq_some, Option.some.injEq] at h <;>
    obtain ⟨hc, rfl⟩ := h
  · exact Refines.eq_and_mask (Or.inl rfl) (Or.inl rfl) hc
  · exact Refines.eq_and_mask (Or.inr rfl) (Or.inl rfl) hc
  · exact Refines.trans Refines.eq_symm (Refines.eq_and_mask (Or.inl rfl) (Or.inr rfl) hc)
  · exact Refines.trans Refines.eq_symm (Refines.eq_and_mask (Or.inr rfl) (Or.inr rfl) hc)

theorem sem_eq.r_concat_const.aux {FS : FloatSem} {Z l r : Term} {T : Ty} :
    Refines FS (sem_eq.spec Z (.mk (.binop .bvConcat l r) T))
      (b_and.spec (sem_eq.spec l (bv_extract.spec (size r) (size r + size l - 1) Z))
        (sem_eq.spec r (bv_extract.spec 0 (size r - 1) Z))) := by
  refine Refines.trans ?_ Refines.and_eq_symm
  refine Refines.eq_concat (fun n m hn hm hl hr wZ hZ => ?_) (fun n m hn hm hl hr wZ hZ ρ W c h => ?_)
  · simp only [size, ty_eq, hl, hr, size_of_ty_bitVector]
    obtain ⟨a1, a2, -⟩ := extract_hi (FS := FS) (ρ := ⟨fun _ => none, fun _ _ => none⟩) hn hm wZ hZ
    obtain ⟨b1, b2, -⟩ := extract_lo (FS := FS) (ρ := ⟨fun _ => none, fun _ _ => none⟩) hn hm wZ hZ
    exact ⟨a1, a2, b1, b2⟩
  · simp only [size, ty_eq, hl, hr, size_of_ty_bitVector]
    exact ⟨(extract_hi hn hm wZ hZ).2.2 W c h, (extract_lo hn hm wZ hZ).2.2 W c h⟩

theorem sem_eq.r_concat_const.proof : sem_eq.r_concat_const.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_concat_const] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp only [reduceCtorEq, Option.some.injEq] at h <;> subst h
  all_goals
    refine Refines.trans ?_ (Refines.b_and hO (Refines.sem_eq hO Refines.refl (hO.bv_extract _ _ _))
      (Refines.sem_eq hO Refines.refl (hO.bv_extract _ _ _)))
  · exact sem_eq.r_concat_const.aux
  · exact Refines.trans Refines.eq_symm (Refines.trans Refines.eq_retype sem_eq.r_concat_const.aux)

theorem sem_eq.r_zext_const.aux {FS : FloatSem} {O : Ops} (hO : O.Sound FS) {k z : Int}
    {bv : Term} {T1 T2 : Ty} :
    Refines FS (sem_eq.spec (.mk (.unop (.bvExtend false k) bv) T1) (.mk (.bitVec z) T2))
      (if (!decide (zland z (zshiftl (zshiftl 1 k - 1) (size bv)) = 0)) = true then v_false
        else O.sem_eq bv (mk_bv (size bv) z)) := by
  have key : ∀ (hT : (Term.mk (.unop (.bvExtend false k) bv) T1).ty = (Term.mk (.bitVec z) T2).ty)
      (w1 : (Term.mk (.unop (.bvExtend false k) bv) T1).WT) (w2 : (Term.mk (.bitVec z) T2).WT),
      ∃ n : Int, 0 < n ∧ 0 ≤ k ∧ bv.ty = .bitVector n ∧ bv.WT ∧ 0 ≤ z ∧ z < 2 ^ (n + k).toNat ∧
        size bv = n ∧ ∀ ρ v, eval FS ρ (.mk (.bitVec z) T2) = some v →
          v = .bv (n + k).toNat (BitVec.ofInt _ z) := by
    intro hT w1 w2
    have ⟨h1, wb⟩ := WT_unop.1 w1
    simp only [Unop.WT, Ty.sort_eq, Term.ty_mk] at h1 hT
    obtain ⟨n, hn, hb, hk, rfl⟩ := h1
    obtain ⟨W, hW, hT2, z0, z1, -⟩ := eval_bitVec_range (FS := FS) (ρ := ⟨fun _ => none, fun _ _ => none⟩) w2
    have hW' : (W : Int) = n + k := by
      rcases hT2 with h | h <;> rw [h] at hT <;> simp at hT; omega
    refine ⟨n, hn, hk, hb, wb, z0, by rw [← hW']; simpa using z1, by simp [size, hb], fun ρ v e => ?_⟩
    obtain ⟨W', _, hT2', _, _, e'⟩ := eval_bitVec_range (FS := FS) (ρ := ρ) w2
    rw [e'] at e; cases e
    have : W' = (n + k).toNat := by
      rcases hT2' with h | h <;> rw [h] at hT <;> simp at hT; omega
    subst this; rfl
  split
  · rename_i hm
    refine Refines.eq_const (fun _ _ _ => by simp) (fun ρ x y hT w1 w2 hx hy => ?_)
    obtain ⟨n, hn, hk, hb, wb, z0, z1, hs, hy'⟩ := key hT w1 w2
    rw [hs] at hm
    have hz : ¬ z < 2 ^ n.toNat := by
      intro h; simp [(zland_mask_eq_zero_iff (by omega) hk z0 z1).2 h] at hm
    obtain rfl := hy' ρ y hy
    rw [eval_unop w1] at hx
    cases he : eval FS ρ bv with
    | none => rw [he] at hx; simp at hx
    | some vb =>
      obtain ⟨_, x0, rfl⟩ := eval_bv_of_ty he (Or.inl hb)
      rw [he] at hx; simp only [evUnop, Option.some.injEq, Bool.false_eq_true, ite_false] at hx
      subst hx
      simp only [eval_v_false, Option.some.injEq, Val.bool.injEq, Bool.false_eq,
        decide_eq_false_iff_not]
      intro h
      have := toNat_of_val_bv_eq h
      rw [BitVec.toNat_setWidth] at this
      have h2 := toNat_ofInt_of_range (w := (n + k).toNat) z0 z1
      have h3 := x0.isLt
      have h4 : x0.toNat % 2 ^ (n.toNat + k.toNat) = x0.toNat :=
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h3 (Nat.pow_le_pow_right (by omega) (by omega)))
      apply hz
      have : (x0.toNat : Int) = z := by omega
      rw [← this]; exact_mod_cast h3
  · rename_i hm
    refine Refines.trans ?_ (hO.sem_eq bv _)
    refine Refines.eq_eq (fun hT w1 w2 => ?_) (fun ρ x y hT w1 w2 hx hy => ?_)
    · obtain ⟨n, hn, hk, hb, wb, z0, z1, hs, -⟩ := key hT w1 w2
      rw [hs]
      exact ⟨by simp [hb, mk_bv], wb, mk_masked_WT hn⟩
    · obtain ⟨n, hn, hk, hb, wb, z0, z1, hs, hy'⟩ := key hT w1 w2
      rw [hs] at hm ⊢
      have hz : z < 2 ^ n.toNat := by
        simpa using (zland_mask_eq_zero_iff (by omega) hk z0 z1).1 (by simpa using hm)
      obtain rfl := hy' ρ y hy
      rw [eval_unop w1] at hx
      cases he : eval FS ρ bv with
      | none => rw [he] at hx; simp at hx
      | some vb =>
        obtain ⟨_, x0, rfl⟩ := eval_bv_of_ty he (Or.inl hb)
        rw [he] at hx; simp only [evUnop, Option.some.injEq, Bool.false_eq_true, ite_false] at hx
        subst hx
        refine ⟨_, _, rfl, by rw [mk_bv, eval_mk_masked hn], ?_⟩
        rw [val_bv_eq_iff _ _ (by omega), val_bv_eq_iff _ _ rfl, BitVec.toNat_setWidth]
        have h2 := toNat_ofInt_of_range (w := (n + k).toNat) z0 z1
        have h2' := toNat_ofInt_of_range (w := n.toNat) z0 hz
        have h3 := x0.isLt
        have h4 : x0.toNat % 2 ^ (n.toNat + k.toNat) = x0.toNat :=
          Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h3 (Nat.pow_le_pow_right (by omega) (by omega)))
        rw [h4]; omega

theorem sem_eq.r_zext_const.proof : sem_eq.r_zext_const.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_zext_const] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp only [reduceCtorEq, Option.some.injEq] at h <;> subst h
  · exact sem_eq.r_zext_const.aux hO
  · exact Refines.trans Refines.eq_symm (sem_eq.r_zext_const.aux hO)

theorem sem_eq.r_ite_concat.aux {FS : FloatSem} {g t e l r : Term} {T T' : Ty} :
    Refines FS (sem_eq.spec (.mk (.triop .ite g t e) T) (.mk (.binop .bvConcat l r) T'))
      (b_and.spec
        (sem_eq.spec (b_ite.spec g (bv_extract.spec (size r) (size r + size l - 1) t)
          (bv_extract.spec (size r) (size r + size l - 1) e)) l)
        (sem_eq.spec (b_ite.spec g (bv_extract.spec 0 (size r - 1) t)
          (bv_extract.spec 0 (size r - 1) e)) r)) := by
  have key : ∀ n m : Int, 0 < n → 0 < m → (Term.mk (.triop .ite g t e) T).WT →
      (Term.mk (.triop .ite g t e) T).ty = .bitVector (n + m) →
      g.ty = .bool ∧ g.WT ∧ t.WT ∧ t.ty = .bitVector (n + m) ∧ e.WT ∧ e.ty = .bitVector (n + m) := by
    intro n m _ _ wZ hZ
    obtain ⟨hg, h1, h2, wg, wt, we⟩ := WT_ite.1 wZ
    simp only [Term.ty_mk] at hZ
    exact ⟨hg, wg, wt, by rw [← h2, hZ], we, by rw [h1, ← h2, hZ]⟩
  refine Refines.eq_concat (fun n m hn hm hl hr wZ hZ => ?_) (fun n m hn hm hl hr wZ hZ ρ W c h => ?_)
  · simp only [size, ty_eq, hl, hr, size_of_ty_bitVector]
    obtain ⟨hg, wg, wt, ht, we, he⟩ := key n m hn hm wZ hZ
    have E : Env := ⟨fun _ => none, fun _ _ => none⟩
    obtain ⟨a1, a2, -⟩ := extract_hi (FS := FS) (ρ := E) hn hm wt ht
    obtain ⟨b1, b2, -⟩ := extract_lo (FS := FS) (ρ := E) hn hm wt ht
    obtain ⟨c1, c2, -⟩ := extract_hi (FS := FS) (ρ := E) hn hm we he
    obtain ⟨d1, d2, -⟩ := extract_lo (FS := FS) (ρ := E) hn hm we he
    refine ⟨WT_triop.2 ⟨by simp [Triop.WT, hg, a2, c2], wg, a1, c1⟩, by simp [b_ite.spec, a2],
      WT_triop.2 ⟨by simp [Triop.WT, hg, b2, d2], wg, b1, d1⟩, by simp [b_ite.spec, b2]⟩
  · simp only [size, ty_eq, hl, hr, size_of_ty_bitVector]
    obtain ⟨hg, wg, wt, ht, we, he⟩ := key n m hn hm wZ hZ
    obtain ⟨a1, a2, a3⟩ := extract_hi (FS := FS) (ρ := ρ) hn hm wt ht
    obtain ⟨b1, b2, b3⟩ := extract_lo (FS := FS) (ρ := ρ) hn hm wt ht
    obtain ⟨c1, c2, c3⟩ := extract_hi (FS := FS) (ρ := ρ) hn hm we he
    obtain ⟨d1, d2, d3⟩ := extract_lo (FS := FS) (ρ := ρ) hn hm we he
    have w1 : (b_ite.spec g (bv_extract.spec m (m + n - 1) t) (bv_extract.spec m (m + n - 1) e)).WT :=
      WT_triop.2 ⟨by simp [Triop.WT, hg, a2, c2], wg, a1, c1⟩
    have w2 : (b_ite.spec g (bv_extract.spec 0 (m - 1) t) (bv_extract.spec 0 (m - 1) e)).WT :=
      WT_triop.2 ⟨by simp [Triop.WT, hg, b2, d2], wg, b1, d1⟩
    rcases (eval_ite_eq_some wZ).1 h with ⟨hc, hv⟩ | ⟨hc, hv⟩
    · rw [b_ite.spec, eval_ite_of w1 hc, b_ite.spec, eval_ite_of w2 hc]
      exact ⟨a3 W c hv, b3 W c hv⟩
    · rw [b_ite.spec, eval_ite_of w1 hc, b_ite.spec, eval_ite_of w2 hc]
      exact ⟨c3 W c hv, d3 W c hv⟩

theorem sem_eq.r_ite_concat.proof : sem_eq.r_ite_concat.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_ite_concat] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp only [reduceCtorEq, Option.some.injEq] at h <;> subst h
  all_goals
    refine Refines.trans ?_ (Refines.b_and hO
      (Refines.sem_eq hO (Refines.b_ite hO Refines.refl (hO.bv_extract _ _ _) (hO.bv_extract _ _ _))
        Refines.refl)
      (Refines.sem_eq hO (Refines.b_ite hO Refines.refl (hO.bv_extract _ _ _) (hO.bv_extract _ _ _))
        Refines.refl))
  · exact sem_eq.r_ite_concat.aux
  · exact Refines.trans Refines.eq_symm sem_eq.r_ite_concat.aux

theorem sem_eq.r_concat_concat.proof : sem_eq.r_concat_concat.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_concat_concat] at h
  split at h <;> simp only [reduceCtorEq, Option.ite_none_right_eq_some, Option.some.injEq,
    decide_eq_true_eq] at h
  obtain ⟨hs, rfl⟩ := h
  refine Refines.trans ?_ (Refines.b_and hO (hO.sem_eq _ _) (hO.sem_eq _ _))
  rename_i l1 r1 T1 l2 r2 T2
  have key : T1 = T2 → (Term.mk (.binop .bvConcat l1 r1) T1).WT →
      (Term.mk (.binop .bvConcat l2 r2) T2).WT →
      ∃ n m : Int, 0 < n ∧ 0 < m ∧ l1.ty = .bitVector n ∧ l2.ty = .bitVector n ∧
        r1.ty = .bitVector m ∧ r2.ty = .bitVector m ∧ l1.WT ∧ l2.WT ∧ r1.WT ∧ r2.WT := by
    intro hT w1 w2
    obtain ⟨n1, m1, hn1, hm1, hl1, hr1, hT1, wl1, wr1⟩ := WT_concat.1 w1
    obtain ⟨n2, m2, hn2, hm2, hl2, hr2, hT2, wl2, wr2⟩ := WT_concat.1 w2
    simp only [size, ty_eq, hl1, hl2, size_of_ty_bitVector] at hs
    subst hs hT hT1
    simp only [Ty.bitVector.injEq] at hT2
    have : m1 = m2 := by omega
    subst this
    exact ⟨_, _, hn1, hm1, hl1, hl2, hr1, hr2, wl1, wl2, wr1, wr2⟩
  refine Refines.eq_and (fun hT w1 w2 => ?_) (fun ρ x y hT w1 w2 hx hy => ?_)
  · obtain ⟨n, m, _, _, h1, h2, h3, h4, w1, w2, w3, w4⟩ := key (by simpa using hT) w1 w2
    exact ⟨by rw [h1, h2], w1, w2, by rw [h3, h4], w3, w4⟩
  · obtain ⟨n, m, _, _, h1, h2, h3, h4, -⟩ := key (by simpa using hT) w1 w2
    obtain ⟨a1, b1, x1, y1, e1, e2, rfl⟩ := eval_concat_some w1 hx
    obtain ⟨a2, b2, x2, y2, e3, e4, rfl⟩ := eval_concat_some w2 hy
    obtain ⟨rfl, _⟩ := eval_bv_ty e1 h1
    obtain ⟨rfl, _⟩ := eval_bv_ty e2 h3
    obtain ⟨rfl, _⟩ := eval_bv_ty e3 h2
    obtain ⟨rfl, _⟩ := eval_bv_ty e4 h4
    refine ⟨_, _, _, _, e1, e3, e2, e4, ?_⟩
    simp [BitVec.append_inj_iff]

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
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_of_bools] at h
  split at h <;> simp at h
  subst h
  refine Refines.trans ?_ (hO.sem_eq _ _)
  refine Refines.eq_eq (fun hT w1 w2 => ?_) (fun ρ x y hT w1 w2 hx hy => ?_)
  · have ⟨h1, wb⟩ := WT_unop.1 w1
    have ⟨h2, wc⟩ := WT_unop.1 w2
    simp [Unop.WT] at h1 h2
    exact ⟨by rw [h1.2.1, h2.2.1], wb, wc⟩
  · have ⟨h1, wb⟩ := WT_unop.1 w1
    have ⟨h2, wc⟩ := WT_unop.1 w2
    simp only [Unop.WT, Ty.sort_eq, Term.ty_mk] at h1 h2 hT
    obtain ⟨hn, _, rfl⟩ := h1
    obtain ⟨hm, _, hT'⟩ := h2
    rw [hT'] at hT; cases hT
    rw [eval_unop w1] at hx; rw [eval_unop w2] at hy
    cases hb : eval FS ρ _ <;> rw [hb] at hx <;> simp [evUnop] at hx
    cases hc : eval FS ρ _ <;> rw [hc] at hy <;> simp [evUnop] at hy
    rename_i vb vc
    rcases vb with _ | _ | _ | _ | _ | _ <;> simp [evUnop] at hx
    rcases vc with _ | _ | _ | _ | _ | _ <;> simp [evUnop] at hy
    subst hx hy
    refine ⟨_, _, rfl, rfl, ?_⟩
    simp only [Val.bv.injEq, heq_eq_eq, true_and, Val.bool.injEq]
    exact BitVec.ofBool_inj (by omega)

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
    rcases vb with _ | _ | _ | _ | _ | _ <;> simp at hx
    rcases vc with _ | _ | _ | _ | _ | _ <;> simp at hy
    subst hx hy
    exact ⟨_, _, rfl, rfl, by simp⟩

theorem sem_eq.r_of_bool_const.aux {FS : FloatSem} {O : Ops} (hO : O.Sound FS) {b : Term}
    {k z : Int} {T1 T2 : Ty} :
    Refines FS (sem_eq.spec (.mk (.unop (.bvOfBool k) b) T1) (.mk (.bitVec z) T2))
      (if z = 1 then b else if z = 0 then O.b_not b else v_false) := by
  split
  · subst_vars
    refine Refines.eq_of_bool_lit (fun h w => ⟨w, h⟩) (fun ρ c n hn _ _ e => ?_)
    rw [e]; cases c <;> simp <;> omega
  split
  · subst_vars
    refine Refines.trans ?_ (hO.b_not b)
    refine Refines.eq_of_bool_lit (fun h w => ⟨WT_unop.2 ⟨by simp [Unop.WT, h], w⟩, rfl⟩)
      (fun ρ c n hn _ _ e => ?_)
    have hb : b.ty = .bool := by have := eval_hasSort e; simpa using this
    rw [b_not.spec, eval_unop (WT_unop.2 ⟨by simp [Unop.WT, hb], eval_WT e⟩), e]
    cases c <;> simp [evUnop] <;> omega
  · rename_i h1 h0
    refine Refines.eq_of_bool_lit (fun _ _ => ⟨by simp, rfl⟩) (fun ρ c n hn z1 z2 e => ?_)
    simp only [eval_v_false, Option.some.injEq, Val.bool.injEq, Bool.false_eq, decide_eq_false_iff_not]
    intro heq
    have := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt z1 (by exact_mod_cast z2)] at this
    cases c
    · simp at this; omega
    · have h1 : (1 : BitVec n).toNat = 1 := by simp; omega
      simp only [ite_true, h1] at this; omega

theorem sem_eq.r_of_bool_const.proof : sem_eq.r_of_bool_const.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_of_bool_const] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp only [reduceCtorEq, Option.some.injEq] at h <;> subst h <;> simp only [decide_eq_true_eq]
  · exact sem_eq.r_of_bool_const.aux hO
  · exact Refines.trans Refines.eq_symm (sem_eq.r_of_bool_const.aux hO)

theorem sem_eq.r_msb.proof : sem_eq.r_msb.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_msb, Option.ite_none_right_eq_some, Option.some.injEq] at h
  obtain ⟨hbv, rfl⟩ := h
  simp only [Bool.and_eq_true] at hbv
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    refine Refines.trans ?_ (Refines.sem_eq hO (hO.bv_extract _ _ _) (hO.bv_extract _ _ _))
    exact Refines.eq_low hc.1 (le_zmax_left _ _) (le_zmax_right _ _) hc.2 (is_bv_true hbv.1)
  · simp only [mk_commut_binop]
    split
    · exact Refines.refl
    · exact Refines.eq_eq (fun h a b => ⟨h.symm, b, a⟩)
        (fun ρ x y _ _ _ hx hy => ⟨y, x, hy, hx, eq_comm⟩)

theorem sem_eq.r_default.proof : sem_eq.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq.r_default, mk_commut_binop, Option.some.injEq] at h
  subst h
  split
  · exact Refines.refl
  · exact Refines.eq_eq (fun h a b => ⟨h.symm, b, a⟩)
      (fun ρ x y _ _ _ hx hy => ⟨y, x, hy, hx, eq_comm⟩)

end Bvr
