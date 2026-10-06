import FloatMod.Lib.Rule
import FloatMod.Statements.Float.fma

/-! The arms of `Float.fma` that the default tactic does not prove. -/

namespace FloatMod

open Classical Kanon Kanon.Sem CoreMod Lib

@[kanon_arm] theorem Float.fma.r_lits.main.proof : Float.fma.r_lits.main.Stmt := by
  intro S _ _ B LBool LCore LBitvec L _ _ _ _ O hO f1 t1 f2 t2 f3 t3
  simp only [kanon_spec]
  have key : S.WT (B.node (L.FmaK (B.node (L.FloatK f1) t1) (B.node (L.FloatK f2) t2)
      (B.node (L.FloatK f3) t3)) (S.ty (B.node (L.FloatK f1) t1))) →
      t1 = L.TFloat f1.prec ∧ f1.WF ∧ f2.WF ∧ f3.WF ∧ f1.prec = f2.prec ∧ f1.prec = f3.prec := by
    intro w
    obtain ⟨⟨-, h2, h3, -⟩, w1, w2, w3⟩ := (L.WT_Fma _ _ _ _).1 w
    obtain ⟨rfl, h1⟩ := WT_lit.1 w1
    obtain ⟨rfl, h4⟩ := WT_lit.1 w2
    obtain ⟨rfl, h5⟩ := WT_lit.1 w3
    simp only [B.ty_node] at h2 h3
    exact ⟨rfl, h1, h4, h5, (L.TFloat_inj _ _ h2).symm, (L.TFloat_inj _ _ h3).symm⟩
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;>
    obtain ⟨ht, h1, h2, h3, hp2, hp3⟩ := key w <;>
    obtain ⟨e1, e2, e3⟩ := hO.float_orc.fma f1 f2 f3 h1 h2 h3 hp2 hp3
  · refine ⟨lit_WT e2, ?_⟩
    rw [lit_ty, B.ty_node, B.ty_node, ht, e1]
  · rw [Sem.ev_Fma, Sem.ev_Float, Sem.ev_Float, Sem.ev_Float] at e
    obtain ⟨p1, b1⟩ := f1
    obtain ⟨p2, b2⟩ := f2
    obtain ⟨p3, b3⟩ := f3
    simp only at hp2 hp3
    subst hp2 hp3
    rw [e3] at e
    rw [Sem.ev_Float]; exact e

end FloatMod
