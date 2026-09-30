import Tiny.Lib.Bool

/-! The boolean operations, proved per alternative. -/

namespace Tiny

open Classical Kanon Lib

@[kanon_arm] theorem b_and.r_eq_neq.main.proof : b_and.r_eq_neq.main.Stmt := by
  kanon_and_eq_neq

@[kanon_arm] theorem b_not.r_distinct.main.proof : b_not.r_distinct.main.Stmt := by
  intro O hO l r t
  simp only [kanon_spec]
  kanon_lift_body
  simp only [kanon_spec]
  refine Refines.intro ?_ (fun ρ v w w' e => ?_)
  · intro w; simp_all [Term.WT, Term.WTList, Binop.WT, Unop.WT]
  · simp only [ev, evList] at e ⊢
    cases hl : ev ρ l <;> cases hr : ev ρ r <;> simp_all [evUnop, evBinop, eqOp]

@[kanon_arm] theorem b_distinct.r_small.main.proof : b_distinct.r_small.main.Stmt := by
  intro O hO l h
  rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp [at_most_one, firstSome] at h <;>
    refine Refines.intro (fun w => by simp [b_distinct.spec, v_true]) (fun ρ v w _ e => ?_) <;>
    simp only [b_distinct.spec, ev, evList] at e <;> simp only [v_true, ev]
  · simp at e; simp [e]
  · split at e <;> simp_all

@[kanon_arm] theorem b_distinct.r_distinct.main.proof : b_distinct.r_distinct.main.Stmt := by
  intro O hO l hc
  simp only [decide_eq_true_eq] at hc
  refine Refines.intro (fun w => by simp [v_true, b_distinct.spec]) (fun ρ v w _ e => ?_)
  obtain ⟨⟨E, hE⟩, hall, rfl⟩ := ev_distinct_eq_some w e
  have : (l.map (evD ρ)).Nodup := by
    refine List.pairwise_map.2 ((distinct_check_true hc).imp_of_mem fun {a b} ha hb hs heq => ?_)
    obtain ⟨u, hu⟩ := hall a ha
    obtain ⟨u', hu'⟩ := hall b hb
    have eb : ev ρ b = some u := by
      rw [hu']
      simp only [evD, hu, hu', Option.getD_some] at heq; rw [heq]
    exact sure_neq_sound hs ((hE a ha).1.trans (hE b hb).1.symm) hu eb
  simp [this, v_true, ev]

@[kanon_arm] theorem b_distinct.r_not_distinct.main.proof :
    b_distinct.r_not_distinct.main.Stmt := by
  intro O hO l hc
  simp only [decide_eq_true_eq] at hc
  refine Refines.intro (fun w => by simp [v_false, b_distinct.spec]) (fun ρ v w _ e => ?_)
  obtain ⟨-, -, rfl⟩ := ev_distinct_eq_some w e
  have := distinct_check_false hc
  have : ¬ (l.map (evD ρ)).Nodup :=
    fun h => this (List.Pairwise.of_map _ (fun a b hne he => hne (he ▸ rfl)) h)
  simp [this, v_false, ev]

@[kanon_arm] theorem b_distinct.r_default.main.proof : b_distinct.r_default.main.Stmt := by
  intro O hO l
  have hp := hO.orc.sort_by_tag l
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · simp only [b_distinct.spec, Term.WT] at w
    obtain ⟨-, E, wl⟩ := w
    refine ⟨?_, rfl⟩
    simp only [Term.WT]
    exact ⟨trivial, E, WTList_iff.2 fun t ht => WTList_iff.1 wl t (hp.mem_iff.1 ht)⟩
  · obtain ⟨-, hall, rfl⟩ := ev_distinct_eq_some w e
    simp only [ev]
    rw [evList_eq_some.2 ⟨fun t ht => hall t (hp.mem_iff.1 ht), rfl⟩]
    simp [(hp.map (evD ρ)).nodup_iff]

end Tiny
