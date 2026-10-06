import KanonBool.Lifts
import PtrMod.Lib.Rule
import PtrMod.Statements.Bool.eq

/-! The equality of two pointers is that of their locations and of their
offsets (`Lib.ev_Ptr_of`, `Sem.vptr_inj`). -/

namespace PtrMod

open Classical Kanon Kanon.Sem Lib

@[kanon_arm] theorem Bool.eq.r_ptrs.main.proof : Bool.eq.r_ptrs.main.Stmt := by
  intro S _ _ B LBool LCore LBitvec L _ _ _ _ O hO l1 o1 t4 l2 o2 t8
  have hb := hO.toBitvecSound.toBoolSound
  refine Refines.trans ?_ (KanonBool.Lib.lift_bool_and_ hb
    (KanonBool.Lib.lift_bool_eq hb Refines.refl Refines.refl)
    (KanonBool.Lib.lift_bool_eq hb Refines.refl Refines.refl))
  simp only [KanonBool.Bool.and_.spec, KanonBool.Bool.eq.spec]
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> rw [LBool.WT_Eq] at w
  · obtain ⟨⟨h2, -⟩, w1, w2⟩ := w
    obtain ⟨⟨n, -, hl1, ho1, ht1⟩, wl1, wo1⟩ := (L.WT_Ptr _ _ _).1 w1
    obtain ⟨⟨m, -, hl2, ho2, ht2⟩, wl2, wo2⟩ := (L.WT_Ptr _ _ _).1 w2
    rw [B.ty_node, B.ty_node, ht1, ht2] at h2
    obtain rfl := L.TPointer_inj _ _ h2
    exact ⟨(LBool.WT_And _ _ _).2 ⟨⟨B.ty_node _ _, B.ty_node _ _, rfl⟩,
      (LBool.WT_Eq _ _ _).2 ⟨⟨by rw [hl1, hl2], rfl⟩, wl1, wl2⟩,
      (LBool.WT_Eq _ _ _).2 ⟨⟨by rw [ho1, ho2], rfl⟩, wo1, wo2⟩⟩,
      by rw [B.ty_node, B.ty_node]⟩
  · obtain ⟨-, w1, w2⟩ := w
    rw [KanonBool.Sem.ev_Eq] at e
    rcases e1 : S.ev ρ (B.node (L.PtrK l1 o1) t4) with _ | v1 <;> rw [e1] at e
    · simp [KanonBool.peq] at e
    rcases e2 : S.ev ρ (B.node (L.PtrK l2 o2) t8) with _ | v2 <;> rw [e2] at e
    · simp [KanonBool.peq] at e
    obtain ⟨n, x1, y1, el1, eo1, rfl⟩ := ev_Ptr_of w1 e1
    obtain ⟨m, x2, y2, el2, eo2, rfl⟩ := ev_Ptr_of w2 e2
    rw [KanonBool.Sem.ev_And, KanonBool.Sem.ev_Eq, KanonBool.Sem.ev_Eq, el1, el2, eo1, eo2]
    simp only [KanonBool.peq_some] at e ⊢
    rw [← e]
    by_cases hp : Sem.vptr L n x1 y1 = Sem.vptr L m x2 y2
    · have h := Sem.vptr_inj _ _ _ _ _ _ hp
      cases h
      simp [KanonBool.pand, KanonBool.Sem.vbool_inj.eq_iff]
    · by_cases h1 : BitvecMod.Sem.vbv LBitvec n x1 = BitvecMod.Sem.vbv LBitvec m x2
      · have h := BitvecMod.Lib.vbv_sigma_inj _ _ _ _ h1
        cases h
        by_cases h2 : BitvecMod.Sem.vbv LBitvec n y1 = BitvecMod.Sem.vbv LBitvec n y2
        · have := BitvecMod.Sem.vbv_inj _ _ _ h2
          subst this
          exact absurd rfl hp
        · simp [KanonBool.pand, hp, h2, KanonBool.Sem.vbool_inj.eq_iff]
      · simp [KanonBool.pand, hp, h1, KanonBool.Sem.vbool_inj.eq_iff]

end PtrMod
