import ExistsMod.Statements.Exists.mk
import ExistsMod.Lifts

/-!
# The arms of `Exists.mk`

Over the interface: without the binders that its body does not use, an
`Exists` is the same (`Sem.ev_used_binders`), and without binders it is its
body, a boolean (`Sem.extends_nil`, and `KanonBool.Sem.ev_bool`).
-/

namespace ExistsMod

open Classical Kanon

@[kanon_arm] theorem Exists.mk.r_empty.main.proof : Exists.mk.r_empty.main.Stmt := by
  intro S _ _ B LBool LCore L _ _ _ O hO bs body hu
  replace hu : L.exists_used_binders bs body = [] := by
    rw [L.exists_no_binders_eq] at hu
    revert hu; cases L.exists_used_binders bs body <;> simp [firstSome]
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;>
    simp only [Exists.mk.spec] at w ⊢ <;> rw [L.WT_Exists, Sem.exists_wf_Exists] at w <;>
    obtain ⟨-, wb, hn, hw, hb⟩ := w
  · exact ⟨wb, by rw [hb, B.ty_node]⟩
  · simp only [Exists.mk.spec] at e
    rw [Sem.ev_used_binders ρ bs body _ LBool.TBool hn hw, hu, Sem.ev_Exists] at e
    simp only [Sem.extends_nil, forall_eq, exists_eq_left] at e
    split at e
    · rename_i hc
      obtain ⟨b, hb⟩ := hc
      rw [hb] at e ⊢
      cases b <;> simp [KanonBool.Sem.vbool_eq_iff] at e <;> rw [← e]
    · simp at e

@[kanon_arm] theorem Exists.mk.r_default.main.proof : Exists.mk.r_default.main.Stmt := by
  intro S _ _ B LBool LCore L _ _ _ O hO bs body
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;>
    simp only [Exists.mk.spec] at w ⊢ <;> rw [L.WT_Exists, Sem.exists_wf_Exists] at w <;>
    obtain ⟨-, wb, hn, hw, hb⟩ := w
  · have hs := Sem.used_binders_sublist (L := L) bs body
    refine ⟨(L.WT_Exists _ _ _).2 ⟨rfl, wb, (Sem.exists_wf_Exists _ _ _).2
      ⟨(hs.map _).nodup hn, fun b h => hw b (hs.subset h), hb⟩⟩, by rw [B.ty_node, B.ty_node]⟩
  · simp only [Exists.mk.spec] at e
    rw [Sem.ev_used_binders ρ bs body _ LBool.TBool hn hw] at e
    exact e

end ExistsMod
