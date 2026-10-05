import KanonCore.Proof
import ExistsMod.Statements

/-!
# Refinement by congruence

The congruence of `Exists` in its body, with which `kanon_congr` proves that
the spec of `Exists.mk` is monotone (`Lifts.lean`): the body is refined in
every environment, and in particular in those that extend the current one.
-/

namespace ExistsMod

open Classical Kanon Kanon.Sem

namespace Sem

variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
  {LBool : KanonBool.Syntax B} {LCore : CoreMod.Syntax B} {L : Syntax B LBool LCore}
  [KanonBool.Sem LBool] [CoreMod.Sem LCore] [Sem L]

theorem refines_exists {bs : List (Int × S.Ty)} {body body' : S.Term} {t : S.Ty}
    (h : S.Refines body body') :
    S.Refines (B.node (L.ExistsK bs body) t) (B.node (L.ExistsK bs body') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> rw [L.WT_Exists] at w
  · obtain ⟨ht, wb, hf⟩ := w
    obtain ⟨wb', sb⟩ := h.syn wb
    rw [Sem.exists_wf_Exists] at hf
    refine ⟨(L.WT_Exists _ _ _).2 ⟨ht, wb', ?_⟩, by rw [B.ty_node, B.ty_node]⟩
    rw [Sem.exists_wf_Exists, sb]
    exact hf
  · have hev : ∀ ρ', (∃ b, S.ev ρ' body = some (KanonBool.Sem.vbool LBool b)) →
        S.ev ρ' body' = S.ev ρ' body :=
      fun ρ' ⟨_, hb⟩ => (h.ev w.2.1 ρ' _ hb).trans hb.symm
    rw [Sem.ev_Exists] at e ⊢
    split at e
    · rename_i hall
      have hall' : ∀ ρ', Sem.Extends L ρ' ρ bs →
          ∃ b, S.ev ρ' body' = some (KanonBool.Sem.vbool LBool b) := fun ρ' hx => by
        rw [hev ρ' (hall ρ' hx)]; exact hall ρ' hx
      rw [if_pos hall', ← e]
      congr 3
      apply propext; constructor
      · rintro ⟨ρ', hx, hb⟩; exact ⟨ρ', hx, by rw [← hev ρ' (hall ρ' hx)]; exact hb⟩
      · rintro ⟨ρ', hx, hb⟩; exact ⟨ρ', hx, by rw [hev ρ' (hall ρ' hx)]; exact hb⟩
    · simp at e

attribute [kanon_congr_lemma] refines_exists

end Sem

end ExistsMod
