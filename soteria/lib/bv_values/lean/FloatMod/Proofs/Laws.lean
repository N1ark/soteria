import FloatMod.Lib.Rule

/-! The commutativity of `FEq`, whose value is symmetric (`fBin_comm`). -/

namespace FloatMod

open Classical Kanon Kanon.Sem CoreMod

set_option linter.unusedSectionVars false

theorem fBin_comm {V : Type} {vf : (p : Fp) → FBits p → V}
    {f : (p : Fp) → FBits p → FBits p → Option V} (hf : ∀ p x y, f p x y = f p y x)
    (a b : Option V) : fBin vf f a b = fBin vf f b a := by
  simp only [fBin]
  rcases decF vf a with _ | ⟨p, x⟩ <;> rcases decF vf b with _ | ⟨q, y⟩ <;> try rfl
  by_cases h : q = p
  · subst h; simp [hf]
  · simp [h, Ne.symm h]

theorem FBits.eq_comm' {p : Fp} (x y : FBits p) : x.eq y = y.eq x := by
  simp only [FBits.eq]; grind

@[kanon_arm] theorem FEq.comm.proof : FEq.comm.Stmt := by
  intro S _ _ B LBool LCore LBitvec L _ _ _ _ a b t
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · rw [L.WT_FEq] at w
    obtain ⟨⟨⟨p, hp⟩, hb, ht⟩, wa, wb⟩ := w
    exact ⟨(L.WT_FEq _ _ _).2 ⟨⟨⟨p, hb.trans hp⟩, hb.symm, ht⟩, wb, wa⟩,
      by rw [B.ty_node, B.ty_node]⟩
  · rw [Sem.ev_FEq] at e ⊢
    rw [fBin_comm (fun p x y => by rw [FBits.eq_comm' x y])]; exact e

end FloatMod
