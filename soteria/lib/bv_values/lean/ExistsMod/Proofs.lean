import ExistsMod.Statements

/-!
# The proofs of the exists module

Both rules of `Exists.mk` drop the binders that the body does not use, which
does not change the quantifier (`Laws.ev_used`, which each language proves);
without binders, it is its body.
-/

namespace ExistsMod

open Kanon

@[kanon_arm] theorem Exists.mk.r_empty.main.proof : Exists.mk.r_empty.main.Stmt := by
  intro S _ _ _ _ _ _ O hO bs body h
  have hu : used_binders bs body = [] := by
    cases hn : used_binders bs body with
    | nil => rfl
    | cons _ _ => simp [Exists.no_binders, firstSome, hn] at h
  refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · obtain ⟨-, -, hb, wb⟩ := WT_exists w
    exact ⟨wb, by simp [Exists.mk.spec, hb]⟩
  · rw [Exists.mk.spec] at e
    have e := Laws.ev_used ρ _ _ _ _ w e
    rw [show Laws.used_binders bs body = [] from hu, ev_mk] at e
    simp only [Node.map, Node.eval] at e
    obtain ⟨b, hb, rfl⟩ := existsV_nil e
    exact hb

@[kanon_arm] theorem Exists.mk.r_default.main.proof : Exists.mk.r_default.main.Stmt := by
  intro S _ _ _ _ _ _ O hO bs body
  refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · obtain ⟨-, hn, hb, wb⟩ := WT_exists w
    refine ⟨(WT_mk _ _).2 ⟨?_, by simp [Node.All, wb]⟩, by simp [Exists.mk.spec]⟩
    simp only [Node.wt, exists_wf]
    exact ⟨by simp, ((Laws.used_sublist bs body).map Prod.fst).nodup hn, hb⟩
  · exact Laws.ev_used ρ _ _ _ _ w e

end ExistsMod
