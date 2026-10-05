import Kanon.Lib.Bool
import Kanon.Statements.Exists.mk

/-! The arms of `Exists.mk` that the default tactics do not prove. -/

namespace Kanon

open Classical Lib

@[kanon_arm] theorem Exists.mk.r_empty.main.proof : Exists.mk.r_empty.main.Stmt := by
  intro FS O hO bs body hu
  replace hu : used_binders bs body = [] := by
    cases h : used_binders bs body <;> simp_all [Exists.no_binders, firstSome]
  refine Sem.Refines.intro_eval (fun w => ?_) (fun ρ v w w' e => ?_) <;>
    obtain ⟨-, hn, hw, hb, wb⟩ := WT_exists.1 w
  · exact ⟨wb, by simp [hb, Exists.mk.spec]⟩
  · rw [← eval] at e ⊢
    simp only [Exists.mk.spec] at w e
    rw [eval_eq_ev w, ev_exists_used (T' := Ty.TBool) hn hw, hu] at e
    rw [eval_eq_ev wb]
    simp only [ev, extends_nil, forall_eq, exists_eq_left] at e
    split at e
    · rename_i hc
      obtain ⟨b, hb⟩ := hc
      rw [hb] at e ⊢
      cases b <;> simp at e <;> rw [← e]
    · simp at e

@[kanon_arm] theorem Exists.mk.r_default.main.proof : Exists.mk.r_default.main.Stmt := by
  intro FS O hO bs body
  refine Sem.Refines.intro_eval (fun w => ?_) (fun ρ v w w' e => ?_) <;>
    obtain ⟨-, hn, hw, hb, wb⟩ := WT_exists.1 w
  · exact ⟨WT_exists.2 ⟨rfl, ((List.filter_sublist).map _).nodup hn,
      fun b h => hw b (mem_used_binders.1 h).1, hb, wb⟩, rfl⟩
  · rw [← eval] at e ⊢
    simp only [Exists.mk.spec] at w e
    rw [eval_eq_ev w, ev_exists_used hn hw] at e
    rw [eval_eq_ev w']; exact e

end Kanon
