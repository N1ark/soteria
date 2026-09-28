import Bvr.Lib.Bool

/-! The boolean operations, proved per alternative. -/

namespace Bvr

open Classical Lib

theorem b_and.r_eq_neq.a1.proof : b_and.r_eq_neq.a1.Stmt := by
  bvr_and_eq_neq

theorem b_and.r_eq_extracts.a1.proof : b_and.r_eq_extracts.a1.Stmt := by
  bvr_rule_sem
  all_goals first
    | omega
    | exact concat_eq_extract_of rfl rfl (by omega) (by omega)
    | exact concat_ne_extract ‹_› (by omega) (by omega)
    | exact concat_ne_extract' ‹_› (by omega) (by omega)

theorem b_and.r_upper_bounds.a1.proof : b_and.r_upper_bounds.a1.Stmt := by
  bvr_rule_bounds

theorem b_and.r_upper_bounds.a2.proof : b_and.r_upper_bounds.a2.Stmt := by
  bvr_rule_bounds

theorem b_and.r_upper_bounds.a3.proof : b_and.r_upper_bounds.a3.Stmt := by
  bvr_rule_bounds

theorem b_and.r_upper_bounds.a4.proof : b_and.r_upper_bounds.a4.Stmt := by
  bvr_rule_bounds

theorem b_and.r_lower_bounds.a1.proof : b_and.r_lower_bounds.a1.Stmt := by
  bvr_rule_bounds

theorem b_and.r_lower_bounds.a2.proof : b_and.r_lower_bounds.a2.Stmt := by
  bvr_rule_bounds

theorem b_and.r_lower_bounds.a3.proof : b_and.r_lower_bounds.a3.Stmt := by
  bvr_rule_bounds

theorem b_and.r_lower_bounds.a4.proof : b_and.r_lower_bounds.a4.Stmt := by
  bvr_rule_bounds

theorem b_or.r_lt_lt.a1.proof : b_or.r_lt_lt.a1.Stmt := by
  bvr_rule
  all_goals bvr_int_cmp

theorem b_or.r_complementary.a1.proof : b_or.r_complementary.a1.Stmt := by
  bvr_rule_bounds

theorem b_or.r_complementary.a3.proof : b_or.r_complementary.a3.Stmt := by
  bvr_rule_bounds

theorem b_or.r_complementary.a2.proof : b_or.r_complementary.a2.Stmt := by
  bvr_rule_bounds

theorem b_or.r_complementary.a4.proof : b_or.r_complementary.a4.Stmt := by
  bvr_rule_bounds

theorem b_or.r_upper_eq.a1.proof : b_or.r_upper_eq.a1.Stmt := by
  bvr_rule_bounds

theorem b_or.r_upper_eq.a3.proof : b_or.r_upper_eq.a3.Stmt := by
  bvr_rule_bounds

theorem b_or.r_lower_eq.a1.proof : b_or.r_lower_eq.a1.Stmt := by
  bvr_rule_bounds

theorem b_or.r_lower_eq.a3.proof : b_or.r_lower_eq.a3.Stmt := by
  bvr_rule_bounds

theorem b_or.r_upper_bounds.a1.proof : b_or.r_upper_bounds.a1.Stmt := by
  bvr_rule_bounds

theorem b_or.r_upper_bounds.a2.proof : b_or.r_upper_bounds.a2.Stmt := by
  bvr_rule_bounds

theorem b_or.r_upper_bounds.a3.proof : b_or.r_upper_bounds.a3.Stmt := by
  bvr_rule_bounds

theorem b_or.r_upper_bounds.a4.proof : b_or.r_upper_bounds.a4.Stmt := by
  bvr_rule_bounds

theorem b_or.r_lower_bounds.a1.proof : b_or.r_lower_bounds.a1.Stmt := by
  bvr_rule_bounds

theorem b_or.r_lower_bounds.a2.proof : b_or.r_lower_bounds.a2.Stmt := by
  bvr_rule_bounds

theorem b_or.r_lower_bounds.a3.proof : b_or.r_lower_bounds.a3.Stmt := by
  bvr_rule_bounds

theorem b_or.r_lower_bounds.a4.proof : b_or.r_lower_bounds.a4.Stmt := by
  bvr_rule_bounds

theorem b_not.r_distinct.a1.proof : b_not.r_distinct.a1.Stmt := by
  intro FS O hO l r t
  simp only [bvr_spec]
  bvr_lift_body
  simp only [bvr_spec]
  refine Refines.intro ?_ (fun ρ v w w' e => ?_)
  · intro w; simp_all [Term.WT, Term.WTList, Binop.WT]
  · rw [eval_eq_ev w] at e
    rw [eval_eq_ev w']
    simp only [ev, evList] at e ⊢
    cases hl : ev FS ρ l <;> cases hr : ev FS ρ r <;> simp_all [evUnop, evBinop]

theorem b_ite.r_true_.a1.proof : b_ite.r_true_.a1.Stmt := by
  bvr_rule_ev

theorem b_ite.r_false_.a1.proof : b_ite.r_false_.a1.Stmt := by
  bvr_rule_ev

theorem b_ite.r_bool.a1.proof : b_ite.r_bool.a1.Stmt := by
  bvr_rule_typed

theorem b_ite.r_not_bool.a1.proof : b_ite.r_not_bool.a1.Stmt := by
  bvr_rule_typed

theorem b_ite.r_false_then.a1.proof : b_ite.r_false_then.a1.Stmt := by
  bvr_rule_typed

theorem b_ite.r_true_then.a1.proof : b_ite.r_true_then.a1.Stmt := by
  bvr_rule_typed

theorem b_ite.r_false_else.a1.proof : b_ite.r_false_else.a1.Stmt := by
  bvr_rule_typed

theorem b_ite.r_true_else.a1.proof : b_ite.r_true_else.a1.Stmt := by
  bvr_rule_typed

theorem b_ite.r_bv_of_bool.a1.proof : b_ite.r_bv_of_bool.a1.Stmt := by
  bvr_rule_typed

theorem b_ite.r_not_guard.a1.proof : b_ite.r_not_guard.a1.Stmt := by
  bvr_rule_ev

theorem b_ite.r_guard_then.a1.proof : b_ite.r_guard_then.a1.Stmt := by
  bvr_rule_typed

theorem b_ite.r_guard_else.a1.proof : b_ite.r_guard_else.a1.Stmt := by
  bvr_rule_typed

theorem b_ite.r_ite_then.a1.proof : b_ite.r_ite_then.a1.Stmt := by
  bvr_rule_ev

theorem b_ite.r_ite_else.a1.proof : b_ite.r_ite_else.a1.Stmt := by
  bvr_rule_ev

theorem b_ite.r_and_ite_then.a1.proof : b_ite.r_and_ite_then.a1.Stmt := by
  bvr_rule_ev

theorem b_ite.r_and_ite_then.a2.proof : b_ite.r_and_ite_then.a2.Stmt := by
  bvr_rule_ev

theorem b_ite.r_or_ite_else.a1.proof : b_ite.r_or_ite_else.a1.Stmt := by
  bvr_rule_ev

theorem b_ite.r_or_ite_else.a2.proof : b_ite.r_or_ite_else.a2.Stmt := by
  bvr_rule_ev

theorem b_ite.r_same.a1.proof : b_ite.r_same.a1.Stmt := by
  bvr_rule_ev

theorem b_mk_exists.r_empty.a1.proof : b_mk_exists.r_empty.a1.Stmt := by
  intro FS O hO bs body hu
  replace hu : used_binders bs body = [] := by
    cases h : used_binders bs body <;> simp_all [no_binders, firstSome]
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_) <;>
    obtain ⟨-, hn, hw, hb, wb⟩ := WT_exists.1 w
  · exact ⟨wb, by simp [hb, b_mk_exists.spec]⟩
  · simp only [b_mk_exists.spec] at w e
    rw [eval_eq_ev w, ev_exists_used (T' := Ty.bool) hn hw, hu] at e
    rw [eval_eq_ev wb]
    simp only [ev, extends_nil, forall_eq, exists_eq_left] at e
    split at e
    · rename_i hc
      obtain ⟨b, hb⟩ := hc
      rw [hb] at e ⊢
      cases b <;> simp at e <;> rw [← e]
    · simp at e

theorem b_mk_exists.r_default.a1.proof : b_mk_exists.r_default.a1.Stmt := by
  intro FS O hO bs body
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_) <;>
    obtain ⟨-, hn, hw, hb, wb⟩ := WT_exists.1 w
  · exact ⟨WT_exists.2 ⟨rfl, ((List.filter_sublist).map _).nodup hn,
      fun b h => hw b (mem_used_binders.1 h).1, hb, wb⟩, rfl⟩
  · simp only [b_mk_exists.spec] at w e
    rw [eval_eq_ev w, ev_exists_used hn hw] at e
    rw [eval_eq_ev w']; exact e

theorem sem_eq_untyped.r_ill_typed.a1.proof : sem_eq_untyped.r_ill_typed.a1.Stmt := by
  intro FS O hO v1 v2 h
  have h' : ¬ v1.ty = v2.ty := fun e => by simp [e] at h
  exact Refines.of_WT fun w => absurd (by simpa [Binop.WT] using (WT_binop.1 w).1) h'

theorem b_distinct.r_small.a1.proof : b_distinct.r_small.a1.Stmt := by
  intro FS O hO l h
  rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp [at_most_one, firstSome] at h <;>
    refine Refines.intro (fun w => by simp [b_distinct.spec, v_true, WT_bool]) (fun ρ v w _ e => ?_) <;>
    simp only [b_distinct.spec] at w e <;> rw [eval_eq_ev w] at e <;> simp only [ev, evList] at e <;>
    rw [v_true, eval_bool rfl]
  · simp at e; simp [e]
  · split at e <;> simp_all

theorem b_distinct.r_distinct.a1.proof : b_distinct.r_distinct.a1.Stmt := by
  intro FS O hO l hc
  simp only [decide_eq_true_eq] at hc
  refine Refines.intro (fun w => by simp [v_true, WT_bool, b_distinct.spec]) (fun ρ v w _ e => ?_)
  obtain ⟨⟨E, hE⟩, hall, rfl⟩ := eval_distinct_eq_some e
  have : (l.map (evD FS ρ)).Nodup := by
    refine List.pairwise_map.2 ((distinct_check_true hc).imp_of_mem fun {a b} ha hb hs heq => ?_)
    obtain ⟨u, hu⟩ := hall a ha
    obtain ⟨u', hu'⟩ := hall b hb
    have ea : eval FS ρ a = some u := by rw [eval_eq_ev (hE a ha).2, hu]
    have eb : eval FS ρ b = some u := by
      rw [eval_eq_ev (hE b hb).2, hu']
      simp only [evD, hu, hu', Option.getD_some] at heq; rw [heq]
    exact sure_neq_sound hs ((hE a ha).1.trans (hE b hb).1.symm) ea eb
  simp [this, v_true, eval_bool]

theorem b_distinct.r_not_distinct.a1.proof : b_distinct.r_not_distinct.a1.Stmt := by
  intro FS O hO l hc
  simp only [decide_eq_true_eq] at hc
  refine Refines.intro (fun w => by simp [v_false, WT_bool, b_distinct.spec]) (fun ρ v w _ e => ?_)
  obtain ⟨-, -, rfl⟩ := eval_distinct_eq_some e
  have := distinct_check_false hc
  have : ¬ (l.map (evD FS ρ)).Nodup :=
    fun h => this (List.Pairwise.of_map _ (fun a b hne he => hne (he ▸ rfl)) h)
  simp [this, v_false, eval_bool]

theorem b_distinct.r_default.a1.proof : b_distinct.r_default.a1.Stmt := by
  intro FS O hO l
  have hp := hO.orc.sort_by_tag l
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · simp only [b_distinct.spec, Term.WT] at w
    obtain ⟨-, E, wl⟩ := w
    refine ⟨?_, rfl⟩
    simp only [Term.WT]
    exact ⟨by simp, E, WTList_iff.2 fun t ht => WTList_iff.1 wl t (hp.mem_iff.1 ht)⟩
  · obtain ⟨-, hall, rfl⟩ := eval_distinct_eq_some e
    rw [eval_eq_ev w']
    simp only [ev]
    rw [evList_eq_some.2 ⟨fun t ht => hall t (hp.mem_iff.1 ht), rfl⟩]
    simp [(hp.map (evD FS ρ)).nodup_iff]

end Bvr
