import Kanon.Lib.Bool

/-! The boolean operations, proved per alternative. -/

namespace Kanon

open Classical Lib

@[kanon_arm] theorem b_and.r_eq_neq.main.proof : b_and.r_eq_neq.main.Stmt := by
  kanon_and_eq_neq

@[kanon_arm] theorem b_and.r_eq_extracts.main.proof : b_and.r_eq_extracts.main.Stmt := by
  kanon_rule_sem
  all_goals first
    | omega
    | exact concat_eq_extract_of rfl rfl (by omega) (by omega)
    | exact concat_ne_extract ‹_› (by omega) (by omega)
    | exact concat_ne_extract' ‹_› (by omega) (by omega)

@[kanon_arm] theorem b_not.r_distinct.main.proof : b_not.r_distinct.main.Stmt := by
  intro FS O hO l r t
  simp only [kanon_spec]
  kanon_lift_body
  simp only [kanon_spec]
  refine Refines.intro ?_ (fun ρ v w w' e => ?_)
  · intro w; simp_all [Term.WT, Term.WTList, Binop.WT]
  · rw [eval_eq_ev w] at e
    rw [eval_eq_ev w']
    simp only [ev, evList] at e ⊢
    cases hl : ev FS ρ l <;> cases hr : ev FS ρ r <;> simp_all [evUnop, evBinop]

@[kanon_arm] theorem b_mk_exists.r_empty.main.proof : b_mk_exists.r_empty.main.Stmt := by
  intro FS O hO bs body hu
  replace hu : used_binders bs body = [] := by
    cases h : used_binders bs body <;> simp_all [no_binders, firstSome]
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_) <;>
    obtain ⟨-, hn, hw, hb, wb⟩ := WT_exists.1 w
  · exact ⟨wb, by simp [hb, b_mk_exists.spec]⟩
  · simp only [b_mk_exists.spec] at w e
    rw [eval_eq_ev w, ev_exists_used (T' := Ty.TBool) hn hw, hu] at e
    rw [eval_eq_ev wb]
    simp only [ev, extends_nil, forall_eq, exists_eq_left] at e
    split at e
    · rename_i hc
      obtain ⟨b, hb⟩ := hc
      rw [hb] at e ⊢
      cases b <;> simp at e <;> rw [← e]
    · simp at e

@[kanon_arm] theorem b_mk_exists.r_default.main.proof : b_mk_exists.r_default.main.Stmt := by
  intro FS O hO bs body
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_) <;>
    obtain ⟨-, hn, hw, hb, wb⟩ := WT_exists.1 w
  · exact ⟨WT_exists.2 ⟨rfl, ((List.filter_sublist).map _).nodup hn,
      fun b h => hw b (mem_used_binders.1 h).1, hb, wb⟩, rfl⟩
  · simp only [b_mk_exists.spec] at w e
    rw [eval_eq_ev w, ev_exists_used hn hw] at e
    rw [eval_eq_ev w']; exact e

@[kanon_arm] theorem b_distinct.r_small.main.proof : b_distinct.r_small.main.Stmt := by
  intro FS O hO l h
  rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp [at_most_one, firstSome] at h <;>
    refine Refines.intro (fun w => by simp [b_distinct.spec, v_true, WT_bool]) (fun ρ v w _ e => ?_) <;>
    simp only [b_distinct.spec] at w e <;> rw [eval_eq_ev w] at e <;> simp only [ev, evList] at e <;>
    rw [v_true, eval_bool rfl]
  · simp at e; simp [e]
  · split at e <;> simp_all

@[kanon_arm] theorem b_distinct.r_distinct.main.proof : b_distinct.r_distinct.main.Stmt := by
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

@[kanon_arm] theorem b_distinct.r_not_distinct.main.proof : b_distinct.r_not_distinct.main.Stmt := by
  intro FS O hO l hc
  simp only [decide_eq_true_eq] at hc
  refine Refines.intro (fun w => by simp [v_false, WT_bool, b_distinct.spec]) (fun ρ v w _ e => ?_)
  obtain ⟨-, -, rfl⟩ := eval_distinct_eq_some e
  have := distinct_check_false hc
  have : ¬ (l.map (evD FS ρ)).Nodup :=
    fun h => this (List.Pairwise.of_map _ (fun a b hne he => hne (he ▸ rfl)) h)
  simp [this, v_false, eval_bool]

@[kanon_arm] theorem b_distinct.r_default.main.proof : b_distinct.r_default.main.Stmt := by
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

end Kanon
