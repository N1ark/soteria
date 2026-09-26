import Bvr.Proofs.BoolLemmas

/-! Booleans: `b_and`, `b_or`, `b_not`, `b_ite`, `b_mk_exists`, `b_distinct`, `sem_eq_untyped`. -/

namespace Bvr

open Classical BoolL

theorem b_and.r_same.proof : b_and.r_same.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_and.r_same] at h
  split at h <;> bool_fire h
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · simp only [b_and.spec, WT_and', WT_or, WT_not, WT_ite, Term.ty_mk] at w ⊢; grind
  · simp only [b_and.spec] at w e
    rw [eval_binop w] at e
    bool_fin

theorem b_and.r_false_.proof : b_and.r_false_.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_and.r_false_] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> subst h
  all_goals
    refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
    · simp_all [b_and.spec, WT_and]
    · simp only [b_and.spec] at w e
      rw [eval_binop w] at e
      obtain ⟨_, _, _, w1, w2⟩ := WT_and.1 w
      simp_all [Ty.sort_eq_bool, evBinop, pand_eq_some, eval_bool] <;> grind

theorem b_and.r_true_l.proof : b_and.r_true_l.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_and.r_true_l] at h
  split at h <;> bool_fire h
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · simp only [b_and.spec, WT_and', WT_or, WT_not, WT_ite, Term.ty_mk] at w ⊢; grind
  · simp only [b_and.spec] at w e
    have := WT_and'.1 w
    simp only [Term.ty_mk] at this
    rw [eval_binop w, eval_bool this.1] at e
    bool_fin

theorem b_and.r_true_r.proof : b_and.r_true_r.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_and.r_true_r] at h
  split at h <;> bool_fire h
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · bool_syn
  · simp only [b_and.spec] at w e
    have := WT_and'.1 w
    simp only [Term.ty_mk] at this
    rw [eval_binop w, eval_bool this.2.1] at e
    bool_fin

theorem b_and.r_not.proof : b_and.r_not.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_and.r_not] at h
  have h' := orElse_eq_some h; clear h; rcases h' with h | h <;> split at h <;> bool_fire h
  all_goals
    refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
    · bool_syn
    · simp only [b_and.spec] at w e
      have ⟨_, _, _, w1, w2⟩ := WT_and'.1 w
      rw [eval_binop w] at e
      first | rw [eval_unop w1] at e | rw [eval_unop w2] at e
      bool_fin

theorem b_and.r_and_l.proof : b_and.r_and_l.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_and.r_and_l] at h
  have h' := orElse_eq_some h; clear h; rcases h' with h | h <;> split at h <;> bool_fire h
  all_goals
    refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
    · simp only [b_and.spec, WT_and', WT_or, WT_not, WT_ite, Term.ty_mk] at w ⊢; grind
    · simp only [b_and.spec] at w e
      have ⟨_, _, _, w1, _⟩ := WT_and'.1 w
      rw [eval_binop w, eval_binop w1] at e
      rw [eval_binop w1]
      bool_fin

theorem b_and.r_and_r.proof : b_and.r_and_r.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_and.r_and_r] at h
  have h' := orElse_eq_some h; clear h; rcases h' with h | h <;> split at h <;> bool_fire h
  all_goals
    refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
    · bool_syn
    · simp only [b_and.spec] at w e
      have ⟨_, _, _, _, w1⟩ := WT_and'.1 w
      rw [eval_binop w, eval_binop w1] at e
      rw [eval_binop w1]
      bool_fin

theorem b_and.r_or_l.proof : b_and.r_or_l.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_and.r_or_l] at h
  have h' := orElse_eq_some h; clear h; rcases h' with h | h <;> split at h <;> bool_fire h
  all_goals
    refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
    · bool_syn
    · simp only [b_and.spec] at w e
      have ⟨_, _, _, w1, _⟩ := WT_and'.1 w
      rw [eval_binop w, eval_binop w1] at e
      bool_fin

theorem b_and.r_or_r.proof : b_and.r_or_r.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_and.r_or_r] at h
  have h' := orElse_eq_some h; clear h; rcases h' with h | h <;> split at h <;> bool_fire h
  all_goals
    refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
    · bool_syn
    · simp only [b_and.spec] at w e
      have ⟨_, _, _, _, w1⟩ := WT_and'.1 w
      rw [eval_binop w, eval_binop w1] at e
      bool_fin

theorem b_and.r_eq_neq.proof : b_and.r_eq_neq.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_and.r_eq_neq] at h
  bool_alts h
  all_goals (split at h <;> simp only [Option.ite_none_right_eq_some, Option.some.injEq,
    reduceCtorEq, Bool.and_eq_true, equal_iff] at h)
  all_goals (obtain ⟨⟨rfl, hn⟩, rfl⟩ := h)
  all_goals first
    | exact Refines.and_eq_neq (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) hn
    | exact Refines.and_eq_neq (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) hn
    | exact Refines.and_eq_neq (Or.inr ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) hn
    | exact Refines.and_eq_neq (Or.inr ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) hn

theorem b_and.r_eq_extracts.proof : b_and.r_eq_extracts.Stmt := by
  sorry

theorem b_and.r_upper_bounds.proof : b_and.r_upper_bounds.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_and.r_upper_bounds] at h
  bool_alts h
  all_goals (split at h <;> bool_fire h)
  all_goals first
    | exact Refines.and_upper_bounds as_upper_bound_lt as_upper_bound_lt
    | exact Refines.and_upper_bounds as_upper_bound_lt as_upper_bound_leq
    | exact Refines.and_upper_bounds as_upper_bound_leq as_upper_bound_lt
    | exact Refines.and_upper_bounds as_upper_bound_leq as_upper_bound_leq

theorem b_and.r_lower_bounds.proof : b_and.r_lower_bounds.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_and.r_lower_bounds] at h
  bool_alts h
  all_goals (split at h <;> bool_fire h)
  all_goals first
    | exact Refines.and_lower_bounds as_lower_bound_lt as_lower_bound_lt
    | exact Refines.and_lower_bounds as_lower_bound_lt as_lower_bound_leq
    | exact Refines.and_lower_bounds as_lower_bound_leq as_lower_bound_lt
    | exact Refines.and_lower_bounds as_lower_bound_leq as_lower_bound_leq

theorem b_and.r_default.proof : b_and.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_and.r_default, mk_commut_binop, Option.some.injEq] at h
  subst h
  split
  · exact Refines.refl
  · refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
    · bool_syn
    · simp only [b_and.spec] at w e
      rw [eval_binop w] at e; rw [eval_binop w']
      simpa [evBinop, pand_comm] using e

theorem b_or.r_same.proof : b_or.r_same.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_or.r_same] at h
  split at h <;> bool_fire h
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · simp only [b_or.spec, WT_or, WT_or, WT_not, WT_ite, Term.ty_mk] at w ⊢; grind
  · simp only [b_or.spec] at w e
    rw [eval_binop w] at e
    bool_fin

theorem b_or.r_true_.proof : b_or.r_true_.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_or.r_true_] at h
  have h' := orElse_eq_some h; clear h; rcases h' with h | h <;> split at h <;> bool_fire h
  all_goals
    refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
    · bool_syn
    · simp only [b_or.spec] at w e
      have := WT_or.1 w
      simp only [Term.ty_mk] at this
      rw [eval_binop w] at e
      first | rw [eval_bool this.1] at e | rw [eval_bool this.2.1] at e
      bool_fin

theorem b_or.r_false_l.proof : b_or.r_false_l.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_or.r_false_l] at h
  split at h <;> bool_fire h
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · simp only [b_or.spec, WT_or, WT_or, WT_not, WT_ite, Term.ty_mk] at w ⊢; grind
  · simp only [b_or.spec] at w e
    have := WT_or.1 w
    simp only [Term.ty_mk] at this
    rw [eval_binop w, eval_bool this.1] at e
    bool_fin

theorem b_or.r_false_r.proof : b_or.r_false_r.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_or.r_false_r] at h
  split at h <;> bool_fire h
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · bool_syn
  · simp only [b_or.spec] at w e
    have := WT_or.1 w
    simp only [Term.ty_mk] at this
    rw [eval_binop w, eval_bool this.2.1] at e
    bool_fin

theorem b_or.r_not.proof : b_or.r_not.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_or.r_not] at h
  have h' := orElse_eq_some h; clear h; rcases h' with h | h <;> split at h <;> bool_fire h
  all_goals
    refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
    · bool_syn
    · simp only [b_or.spec] at w e
      have ⟨_, _, _, w1, w2⟩ := WT_or.1 w
      rw [eval_binop w] at e
      first | rw [eval_unop w1] at e | rw [eval_unop w2] at e
      bool_fin

theorem b_or.r_lt_lt.proof : b_or.r_lt_lt.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_or.r_lt_lt] at h
  split at h <;> simp only [Option.ite_none_right_eq_some, Option.some.injEq, reduceCtorEq,
    Bool.and_eq_true, decide_eq_true_eq, equal_iff] at h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h
  exact (Refines.or_lt_lt.trans (Refines.unop (hO.sem_eq _ _) (fun _ => rfl))).trans (hO.b_not _)

theorem b_or.r_lt_leq.proof : b_or.r_lt_leq.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_or.r_lt_leq] at h
  bool_alts h
  all_goals (split at h <;> simp only [Option.ite_none_right_eq_some, Option.some.injEq,
    reduceCtorEq, Bool.and_eq_true, decide_eq_true_eq, equal_iff] at h)
  all_goals (obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h)
  · exact Refines.or_lt_leq
  · exact Refines.or_comm Refines.or_lt_leq

theorem b_or.r_or_l.proof : b_or.r_or_l.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_or.r_or_l] at h
  have h' := orElse_eq_some h; clear h; rcases h' with h | h <;> split at h <;> bool_fire h
  all_goals
    refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
    · simp only [b_or.spec, WT_or, WT_or, WT_not, WT_ite, Term.ty_mk] at w ⊢; grind
    · simp only [b_or.spec] at w e
      have ⟨_, _, _, w1, _⟩ := WT_or.1 w
      rw [eval_binop w, eval_binop w1] at e
      rw [eval_binop w1]
      bool_fin

theorem b_or.r_or_r.proof : b_or.r_or_r.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_or.r_or_r] at h
  have h' := orElse_eq_some h; clear h; rcases h' with h | h <;> split at h <;> bool_fire h
  all_goals
    refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
    · bool_syn
    · simp only [b_or.spec] at w e
      have ⟨_, _, _, _, w1⟩ := WT_or.1 w
      rw [eval_binop w, eval_binop w1] at e
      rw [eval_binop w1]
      bool_fin

theorem b_or.r_and_l.proof : b_or.r_and_l.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_or.r_and_l] at h
  have h' := orElse_eq_some h; clear h; rcases h' with h | h <;> split at h <;> bool_fire h
  all_goals
    refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
    · bool_syn
    · simp only [b_or.spec] at w e
      have ⟨_, _, _, w1, _⟩ := WT_or.1 w
      rw [eval_binop w, eval_binop w1] at e
      bool_fin

theorem b_or.r_and_r.proof : b_or.r_and_r.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_or.r_and_r] at h
  have h' := orElse_eq_some h; clear h; rcases h' with h | h <;> split at h <;> bool_fire h
  all_goals
    refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
    · bool_syn
    · simp only [b_or.spec] at w e
      have ⟨_, _, _, _, w1⟩ := WT_or.1 w
      rw [eval_binop w, eval_binop w1] at e
      bool_fin

theorem b_or.r_complementary.proof : b_or.r_complementary.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_or.r_complementary] at h
  bool_alts h
  all_goals (split at h <;> simp only [Option.ite_none_right_eq_some, Option.some.injEq, reduceCtorEq] at h)
  all_goals (obtain ⟨hc, rfl⟩ := h; exact Refines.or_complementary hc)

theorem b_or.r_bound_eq.proof : b_or.r_bound_eq.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_or.r_bound_eq] at h
  bool_alts h
  all_goals (split at h <;> simp only [Option.ite_none_right_eq_some, Option.some.injEq,
    reduceCtorEq] at h)
  all_goals (obtain ⟨hc, rfl⟩ := h; exact Refines.or_bound_eq hc)

theorem b_or.r_eq_bound.proof : b_or.r_eq_bound.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_or.r_eq_bound] at h
  bool_alts h
  all_goals (split at h <;> simp only [Option.ite_none_right_eq_some, Option.some.injEq,
    reduceCtorEq] at h)
  all_goals (obtain ⟨hc, rfl⟩ := h; exact Refines.or_comm (Refines.or_bound_eq hc))

theorem b_or.r_upper_bounds.proof : b_or.r_upper_bounds.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_or.r_upper_bounds] at h
  bool_alts h
  all_goals (split at h <;> bool_fire h)
  all_goals first
    | exact Refines.or_upper_bounds as_upper_bound_lt as_upper_bound_lt
    | exact Refines.or_upper_bounds as_upper_bound_lt as_upper_bound_leq
    | exact Refines.or_upper_bounds as_upper_bound_leq as_upper_bound_lt
    | exact Refines.or_upper_bounds as_upper_bound_leq as_upper_bound_leq

theorem b_or.r_lower_bounds.proof : b_or.r_lower_bounds.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_or.r_lower_bounds] at h
  bool_alts h
  all_goals (split at h <;> bool_fire h)
  all_goals first
    | exact Refines.or_lower_bounds as_lower_bound_lt as_lower_bound_lt
    | exact Refines.or_lower_bounds as_lower_bound_lt as_lower_bound_leq
    | exact Refines.or_lower_bounds as_lower_bound_leq as_lower_bound_lt
    | exact Refines.or_lower_bounds as_lower_bound_leq as_lower_bound_leq

theorem b_or.r_default.proof : b_or.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_or.r_default, mk_commut_binop, Option.some.injEq] at h
  subst h
  split
  · exact Refines.refl
  · refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
    · bool_syn
    · simp only [b_or.spec] at w e
      rw [eval_binop w] at e; rw [eval_binop w']
      simpa [evBinop, por_comm] using e

theorem b_not.r_true_.proof : b_not.r_true_.Stmt := by
  intro FS O hO sv res h
  simp only [b_not.r_true_] at h
  split at h <;> bool_fire h
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · bool_syn
  · simp only [b_not.spec] at w e
    have := WT_not.1 w
    simp only [Term.ty_mk] at this
    rw [eval_unop w, eval_bool this.1] at e
    bool_fin

theorem b_not.r_false_.proof : b_not.r_false_.Stmt := by
  intro FS O hO sv res h
  simp only [b_not.r_false_] at h
  split at h <;> bool_fire h
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · bool_syn
  · simp only [b_not.spec] at w e
    have := WT_not.1 w
    simp only [Term.ty_mk] at this
    rw [eval_unop w, eval_bool this.1] at e
    bool_fin

theorem b_not.r_not.proof : b_not.r_not.Stmt := by
  intro FS O hO sv res h
  simp only [b_not.r_not] at h
  split at h <;> bool_fire h
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · bool_syn
  · simp only [b_not.spec] at w e
    have ⟨_, _, w1⟩ := WT_not.1 w
    rw [eval_unop w, eval_unop w1] at e
    simp only [evUnop_not_eq_some] at e
    obtain ⟨b, ⟨c, hc, h1⟩, rfl⟩ := e
    simp only [Val.bool.injEq] at h1; subst h1; simp [hc]

theorem b_not.r_lt.proof : b_not.r_lt.Stmt := by
  intro FS O hO sv res h
  simp only [b_not.r_lt] at h
  split at h <;> bool_fire h
  exact (Refines.not_cmp (Or.inl ⟨rfl, rfl⟩)).trans (hO.bv_leq _ _ _)

theorem b_not.r_leq.proof : b_not.r_leq.Stmt := by
  intro FS O hO sv res h
  simp only [b_not.r_leq] at h
  split at h <;> bool_fire h
  exact (Refines.not_cmp (Or.inr ⟨rfl, rfl⟩)).trans (hO.bv_lt _ _ _)

theorem b_not.r_or_.proof : b_not.r_or_.Stmt := by
  intro FS O hO sv res h
  simp only [b_not.r_or_] at h
  split at h <;> bool_fire h
  exact (Refines.not_andor (Or.inl ⟨rfl, rfl⟩) (hO.b_not _) (hO.b_not _)).trans (hO.b_and _ _)

theorem b_not.r_and_.proof : b_not.r_and_.Stmt := by
  intro FS O hO sv res h
  simp only [b_not.r_and_] at h
  split at h <;> bool_fire h
  exact (Refines.not_andor (Or.inr ⟨rfl, rfl⟩) (hO.b_not _) (hO.b_not _)).trans (hO.b_or _ _)

theorem b_not.r_ite.proof : b_not.r_ite.Stmt := by
  intro FS O hO sv res h
  simp only [b_not.r_ite] at h
  split at h <;> bool_fire h
  rename_i g a b T
  refine Refines.trans Refines.unop_ite ?_
  refine Refines.trans ?_ (hO.b_ite _ _ _)
  refine Refines.ite Refines.refl (hO.b_not a) (hO.b_not b) (fun w => ?_)
  have ⟨_, _, wa, _⟩ := WT_triop.1 w
  have := ((hO.b_not a).syn wa).2
  simp_all [b_ite.spec, b_not.spec]

theorem b_not.r_eq_bit.proof : b_not.r_eq_bit.Stmt := by
  intro FS O hO sv res h
  simp only [b_not.r_eq_bit] at h
  have h' := orElse_eq_some h; clear h; rcases h' with h | h <;> split at h <;> bool_fire h
  all_goals
    try simp only [ty_eq, Term.ty_mk, decide_eq_true_eq] at *
    try subst_vars
    simp only [b_not.spec]
    refine Refines.trans ?_ (hO.sem_eq _ _)
    exact Refines.not_eq_bit rfl (by simp)

theorem b_not.r_distinct.proof : b_not.r_distinct.Stmt := by
  intro FS O hO sv res h
  simp only [b_not.r_distinct] at h
  split at h <;> bool_fire h
  rename_i l r T
  refine Refines.trans ?_ (hO.sem_eq l r)
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · simp only [b_not.spec] at w
    have ⟨_, _, w1⟩ := WT_not.1 w
    simp only [Term.WT, Term.WTList] at w1
    obtain ⟨-, E, h1, wl, h2, wr, -⟩ := w1
    exact ⟨WT_eq.2 ⟨by simp_all, rfl, wl, wr⟩, rfl⟩
  · simp only [b_not.spec] at w e
    have ⟨_, _, w1⟩ := WT_not.1 w
    rw [eval_unop w, eval_eq_ev w1] at e
    simp only [sem_eq.spec] at w' ⊢
    rw [eval_binop w']
    have ⟨_, wl, wr⟩ := WT_eq.1 w' |>.2
    rw [eval_eq_ev wl, eval_eq_ev wr]
    cases hl : ev FS ρ l <;> cases hr : ev FS ρ r <;> simp [ev, evList, hl, hr, evUnop] at e ⊢
    subst e; rfl

theorem b_not.r_default.proof : b_not.r_default.Stmt := by
  intro FS O hO sv res h
  simp [b_not.r_default] at h; subst h
  exact Refines.refl

theorem b_ite.r_true_.proof : b_ite.r_true_.Stmt := by
  intro FS O hO g a b res h
  simp only [b_ite.r_true_] at h
  split at h <;> bool_fire h
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · bool_isyn
  · simp only [b_ite.spec, ty_eq] at w e ⊢
    rw [eval_ite_eq_some w] at e
    have := WT_ite.1 w
    simp only [Term.ty_mk] at this
    rw [eval_bool this.1] at e
    simp_all

theorem b_ite.r_false_.proof : b_ite.r_false_.Stmt := by
  intro FS O hO g a b res h
  simp only [b_ite.r_false_] at h
  split at h <;> bool_fire h
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · bool_isyn
  · simp only [b_ite.spec, ty_eq] at w e ⊢
    rw [eval_ite_eq_some w] at e
    have := WT_ite.1 w
    simp only [Term.ty_mk] at this
    rw [eval_bool this.1] at e
    simp_all

theorem b_ite.r_bool.proof : b_ite.r_bool.Stmt := by
  intro FS O hO g a b res h
  simp only [b_ite.r_bool] at h
  split at h <;> bool_fire h
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · bool_isyn
  · simp only [b_ite.spec, ty_eq] at w e ⊢
    rw [eval_ite_eq_some w] at e
    have := WT_ite.1 w
    simp only [Term.ty_mk] at this
    rw [eval_bool_lit this.2.2.2.2.1, eval_bool_lit this.2.2.2.2.2] at e
    grind

theorem b_ite.r_not_bool.proof : b_ite.r_not_bool.Stmt := by
  intro FS O hO g a b res h
  simp only [b_ite.r_not_bool] at h
  split at h <;> bool_fire h
  refine Refines.trans ?_ (hO.b_not g)
  refine Refines.ite_bool (fun w => WT_bool.1 w) (fun ρ h1 h2 wg wa wb => ⟨WT_not.2 ⟨h1, rfl, wg⟩, rfl, fun v e => ?_⟩)
  have w : (Term.mk (.unop .not_ g) .bool).WT := WT_not.2 ⟨h1, rfl, wg⟩
  simp only [b_not.spec]
  rw [eval_not w]
  simp only [Term.ty_mk] at h2
  rw [eval_bool_lit wa, eval_bool_lit wb] at e
  bool_fin

theorem b_ite.r_false_then.proof : b_ite.r_false_then.Stmt := by
  intro FS O hO g a b res h
  simp only [b_ite.r_false_then] at h
  split at h <;> bool_fire h
  refine Refines.trans ?_ ((Refines.binop (hO.b_not g) Refines.refl (fun _ => rfl)).trans
    (hO.b_and _ _))
  refine Refines.ite_bool (fun w => WT_bool.1 w) (fun ρ h1 h2 wg wa wb =>
    ⟨WT_and'.2 ⟨rfl, h2, rfl, WT_not.2 ⟨h1, rfl, wg⟩, wb⟩, rfl, fun v e => ?_⟩)
  have w : (Term.mk (.unop .not_ g) .bool).WT := WT_not.2 ⟨h1, rfl, wg⟩
  simp only [b_not.spec]
  rw [eval_binop (WT_and'.2 ⟨rfl, h2, rfl, w, wb⟩), eval_not w]
  rw [eval_bool_lit wa] at e
  rcases e with ⟨hg, e⟩ | ⟨hg, e⟩
  · simp at e; subst e; rw [hg]; rfl
  · obtain ⟨c, rfl⟩ := eval_bool_val e h2
    rw [hg, e]; cases c <;> rfl

theorem b_ite.r_true_then.proof : b_ite.r_true_then.Stmt := by
  intro FS O hO g a b res h
  simp only [b_ite.r_true_then] at h
  split at h <;> bool_fire h
  refine Refines.trans ?_ (hO.b_or _ _)
  refine Refines.ite_bool (fun w => WT_bool.1 w) (fun ρ h1 h2 wg wa wb =>
    ⟨WT_or.2 ⟨h1, h2, rfl, wg, wb⟩, rfl, fun v e => ?_⟩)
  simp only [b_or.spec]
  rw [eval_binop (WT_or.2 ⟨h1, h2, rfl, wg, wb⟩)]
  rw [eval_bool_lit wa] at e
  rcases e with ⟨hg, e⟩ | ⟨hg, e⟩
  · simp at e; subst e; rw [hg]; rfl
  · obtain ⟨c, rfl⟩ := eval_bool_val e h2
    rw [hg, e]; cases c <;> rfl

theorem b_ite.r_false_else.proof : b_ite.r_false_else.Stmt := by
  intro FS O hO g a b res h
  simp only [b_ite.r_false_else] at h
  split at h <;> bool_fire h
  rename_i T
  refine Refines.trans ?_ (hO.b_and _ _)
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · bool_isyn
  · simp only [b_ite.spec, ty_eq] at w e ⊢
    rw [eval_ite_eq_some w] at e
    obtain ⟨h1, h2, h3, wg, wa, wb⟩ := WT_ite.1 w
    simp only [Term.ty_mk] at h2
    have hT := WT_bool.1 wb; subst hT; have h2 := h2.symm
    simp only [b_and.spec]
    rw [eval_binop (WT_and'.2 ⟨h1, h2, rfl, wg, wa⟩)]
    rw [eval_bool_lit wb] at e
    rcases e with ⟨hg, e⟩ | ⟨hg, e⟩
    · obtain ⟨c, rfl⟩ := eval_bool_val e h2
      rw [hg, e]; cases c <;> rfl
    · simp at e; subst e; rw [hg]; rfl

theorem b_ite.r_true_else.proof : b_ite.r_true_else.Stmt := by
  intro FS O hO g a b res h
  simp only [b_ite.r_true_else] at h
  split at h <;> bool_fire h
  rename_i T
  refine Refines.trans ?_ ((Refines.binop (hO.b_not g) Refines.refl (fun _ => rfl)).trans
    (hO.b_or _ _))
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · bool_isyn
  · simp only [b_ite.spec, ty_eq] at w e ⊢
    rw [eval_ite_eq_some w] at e
    obtain ⟨h1, h2, h3, wg, wa, wb⟩ := WT_ite.1 w
    simp only [Term.ty_mk] at h2
    have hT := WT_bool.1 wb; subst hT; have h2 := h2.symm
    have wn : (Term.mk (.unop .not_ g) .bool).WT := WT_not.2 ⟨h1, rfl, wg⟩
    simp only [b_not.spec]
    rw [eval_binop (WT_or.2 ⟨rfl, h2, rfl, wn, wa⟩), eval_not wn]
    rw [eval_bool_lit wb] at e
    rcases e with ⟨hg, e⟩ | ⟨hg, e⟩
    · obtain ⟨c, rfl⟩ := eval_bool_val e h2
      rw [hg, e]; cases c <;> rfl
    · simp at e; subst e; rw [hg]; rfl

theorem b_ite.r_bv_of_bool.proof : b_ite.r_bv_of_bool.Stmt := by
  intro FS O hO g a b res h
  simp only [b_ite.r_bv_of_bool] at h
  split at h
  · rename_i z1 T1 z2 T2
    simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨hc, rfl⟩ := h
    simp only [Bool.and_eq_true, decide_eq_true_eq, ty_eq, Term.ty_mk] at hc
    obtain ⟨⟨rfl, rfl⟩, hbv⟩ := hc
    obtain ⟨m, rfl⟩ := is_bv_true hbv
    refine Refines.trans ?_ (hO.bv_of_bool _ _)
    refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
    · simp only [b_ite.spec, bv_of_bool.spec, ty_eq, Term.ty_mk, size_eq,
        size_of_ty_bitVector] at w ⊢
      obtain ⟨h1, h2, h3, wg, wa, wb⟩ := WT_ite.1 w
      obtain ⟨n, hn, hT, -, -⟩ := WT_bitVec.1 wa
      have : m = n := by rcases hT with hT | hT <;> simp at hT; exact hT
      subst this
      exact ⟨WT_unop.2 ⟨by simp [Unop.WT, h1]; omega, wg⟩, by simp⟩
    · simp only [b_ite.spec, bv_of_bool.spec, ty_eq, Term.ty_mk, size_eq,
        size_of_ty_bitVector] at w w' e ⊢
      obtain ⟨h1, h2, h3, wg, wa, wb⟩ := WT_ite.1 w
      simp only [Term.ty_mk] at h2
      subst h2
      rw [eval_ite_eq_some w] at e
      rw [eval_unop w']
      rw [eval_bitVec' (n := m) wa (Or.inl rfl)] at e
      rw [eval_bitVec' (n := m) wb (Or.inl rfl)] at e
      rcases e with ⟨hg, e⟩ | ⟨hg, e⟩ <;> rw [hg] <;> cases e <;> simp [evUnop]
  · simp at h

theorem b_ite.r_not_guard.proof : b_ite.r_not_guard.Stmt := by
  intro FS O hO g a b res h
  simp only [b_ite.r_not_guard] at h
  split at h <;> bool_fire h
  rename_i g T
  refine Refines.trans ?_ (hO.b_ite _ _ _)
  refine Refines.ite_ite (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨h1, h2, h3, wg, wa, wb⟩ := WT_ite.1 w
    obtain ⟨h4, -, wg'⟩ := WT_not.1 wg
    exact ⟨WT_ite.2 ⟨h4, h2.symm, rfl, wg', wb, wa⟩, by simp_all⟩
  · obtain ⟨h1, h2, h3, wg, wa, wb⟩ := WT_ite.1 w
    rw [eval_not wg] at e
    simp only [evUnop_not_eq_some] at e
    grind

theorem b_ite.r_guard_then.proof : b_ite.r_guard_then.Stmt := by
  intro FS O hO g a b res h
  simp only [b_ite.r_guard_then] at h
  split at h <;> bool_fire h
  refine Refines.trans ?_ (hO.b_or _ _)
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · bool_isyn
  · simp only [b_ite.spec, b_or.spec, ty_eq] at w e ⊢
    obtain ⟨h1, h2, h3, wg, -, wb⟩ := WT_ite.1 w
    rw [eval_ite_eq_some w] at e
    rw [eval_binop (WT_or.2 ⟨h1, h2.trans h1, rfl, wg, wb⟩)]
    rcases e with ⟨hg, e⟩ | ⟨hg, e⟩
    · rw [hg] at e; cases e; rw [hg]; rfl
    · obtain ⟨c, rfl⟩ := eval_bool_val e (h2.trans h1)
      rw [hg, e]; cases c <;> rfl

theorem b_ite.r_guard_else.proof : b_ite.r_guard_else.Stmt := by
  intro FS O hO g a b res h
  simp only [b_ite.r_guard_else] at h
  split at h <;> bool_fire h
  refine Refines.trans ?_ (hO.b_and _ _)
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · bool_isyn
  · simp only [b_ite.spec, b_and.spec, ty_eq] at w e ⊢
    obtain ⟨h1, h2, h3, wg, wa, -⟩ := WT_ite.1 w
    rw [eval_ite_eq_some w] at e
    rw [eval_binop (WT_and'.2 ⟨h1, h2.symm.trans h1, rfl, wg, wa⟩)]
    rcases e with ⟨hg, e⟩ | ⟨hg, e⟩
    · obtain ⟨c, rfl⟩ := eval_bool_val e (h2.symm.trans h1)
      rw [hg, e]; cases c <;> rfl
    · rw [hg] at e; cases e; rw [hg]; rfl

theorem b_ite.r_ite_then.proof : b_ite.r_ite_then.Stmt := by
  intro FS O hO g a b res h
  simp only [b_ite.r_ite_then] at h
  split at h <;> bool_fire h
  refine Refines.trans ?_ (hO.b_ite _ _ _)
  refine Refines.ite_ite (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨h1, h2, h3, wg, wa, wb⟩ := WT_ite.1 w
    obtain ⟨h4, h5, h6, -, wx, wy⟩ := WT_ite.1 wa
    simp only [Term.ty_mk] at *
    exact ⟨WT_ite.2 ⟨h1, by simp_all, rfl, wg, wx, wb⟩, by simp_all⟩
  · obtain ⟨h1, h2, h3, wg, wa, wb⟩ := WT_ite.1 w
    rw [eval_ite_eq_some wa] at e
    grind

theorem b_ite.r_ite_else.proof : b_ite.r_ite_else.Stmt := by
  intro FS O hO g a b res h
  simp only [b_ite.r_ite_else] at h
  split at h <;> bool_fire h
  refine Refines.trans ?_ (hO.b_ite _ _ _)
  refine Refines.ite_ite (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨h1, h2, h3, wg, wa, wb⟩ := WT_ite.1 w
    obtain ⟨h4, h5, h6, -, wx, wy⟩ := WT_ite.1 wb
    simp only [Term.ty_mk] at *
    exact ⟨WT_ite.2 ⟨h1, by simp_all, rfl, wg, wa, wy⟩, by simp_all⟩
  · obtain ⟨h1, h2, h3, wg, wa, wb⟩ := WT_ite.1 w
    rw [eval_ite_eq_some wb] at e
    grind

theorem b_ite.r_and_ite_then.proof : b_ite.r_and_ite_then.Stmt := by
  intro FS O hO g a b res h
  simp only [b_ite.r_and_ite_then] at h
  have h' := orElse_eq_some h; clear h; rcases h' with h | h <;> split at h <;> bool_fire h
  all_goals
    refine Refines.trans ?_ (hO.b_ite _ _ _)
    refine Refines.ite_ite (fun w => ?_) (fun ρ v w w' e => ?_)
    · obtain ⟨h1, h2, h3, wg, wa, wb⟩ := WT_ite.1 w
      obtain ⟨h4, h5, h6, -, wx, wy⟩ := WT_ite.1 wa
      simp only [Term.ty_mk] at *
      exact ⟨WT_ite.2 ⟨h1, by simp_all, rfl, wg, wx, wb⟩, by simp_all⟩
    · obtain ⟨h1, h2, h3, wg, wa, wb⟩ := WT_ite.1 w
      rw [eval_ite_eq_some wa, eval_binop wg] at e
      rw [eval_binop wg]
      simp only [evBinop, pand_eq_some] at e ⊢
      grind

theorem b_ite.r_or_ite_else.proof : b_ite.r_or_ite_else.Stmt := by
  intro FS O hO g a b res h
  simp only [b_ite.r_or_ite_else] at h
  have h' := orElse_eq_some h; clear h; rcases h' with h | h <;> split at h <;> bool_fire h
  all_goals
    refine Refines.trans ?_ (hO.b_ite _ _ _)
    refine Refines.ite_ite (fun w => ?_) (fun ρ v w w' e => ?_)
    · obtain ⟨h1, h2, h3, wg, wa, wb⟩ := WT_ite.1 w
      obtain ⟨h4, h5, h6, -, wx, wy⟩ := WT_ite.1 wb
      simp only [Term.ty_mk] at *
      exact ⟨WT_ite.2 ⟨h1, by simp_all, rfl, wg, wa, wy⟩, by simp_all⟩
    · obtain ⟨h1, h2, h3, wg, wa, wb⟩ := WT_ite.1 w
      rw [eval_ite_eq_some wb, eval_binop wg] at e
      rw [eval_binop wg]
      simp only [evBinop, por_eq_some] at e ⊢
      grind

theorem b_ite.r_same.proof : b_ite.r_same.Stmt := by
  intro FS O hO g a b res h
  simp only [b_ite.r_same] at h
  split at h <;> bool_fire h
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · bool_isyn
  · simp only [b_ite.spec, ty_eq] at w e
    rw [eval_ite_eq_some w] at e
    grind

theorem b_ite.r_default.proof : b_ite.r_default.Stmt := by
  intro FS O hO g a b res h
  simp [b_ite.r_default] at h; subst h
  exact Refines.refl

theorem b_mk_exists.r_empty.proof : b_mk_exists.r_empty.Stmt := by
  sorry

theorem b_mk_exists.r_default.proof : b_mk_exists.r_default.Stmt := by
  sorry

theorem sem_eq_untyped.r_main.proof : sem_eq_untyped.r_main.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [sem_eq_untyped.r_main, Option.some.injEq] at h
  subst h
  split
  · exact hO.sem_eq v1 v2
  · rename_i hne
    refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
    · exact absurd (WT_eq.1 w).1 (fun h => by simp [h] at hne)
    · exact absurd (WT_eq.1 w).1 (fun h => by simp [h] at hne)

theorem b_distinct.r_small.proof : b_distinct.r_small.Stmt := by
  intro FS O hO l res h
  simp only [b_distinct.r_small] at h
  bool_alts h
  all_goals (split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h)
  all_goals subst h
  all_goals
    refine Refines.intro (fun w => by simp [b_distinct.spec]) (fun ρ v w _ e => ?_)
    simp only [b_distinct.spec] at w e
    rw [eval_eq_ev w] at e
    simp only [ev, evList] at e
  · simp at e; subst e; simp
  · split at e
    · simp_all
    · simp at e

theorem b_distinct.r_default.proof : b_distinct.r_default.Stmt := by
  sorry

end Bvr
