import FloatMod.Lib.Rule
import FloatMod.Statements.Float.fmod

/-! The arms of `Float.fmod` that the default tactic does not prove. -/

namespace FloatMod

open Classical Kanon Kanon.Sem CoreMod Lib

@[kanon_arm] theorem Float.fmod.r_lits.main.proof : Float.fmod.r_lits.main.Stmt := by
  intro S _ _ B LBool LCore LBitvec L _ _ _ _ O hO f1 t1 f2 t2
  simp only [kanon_spec]
  have key : S.WT (L.float_raw_fmod_of_rem (B.node (L.FRemK (B.node (L.FloatK f1) t1)
      (B.node (L.FloatK f2) t2)) (S.ty (B.node (L.FloatK f1) t1))) (B.node (L.FloatK f1) t1)
      (B.node (L.FloatK f2) t2)) →
      t1 = L.TFloat f1.prec ∧ t2 = L.TFloat f2.prec ∧ f1.WF ∧ f2.WF ∧ f1.prec = f2.prec := by
    intro w
    rw [L.float_raw_fmod_of_rem_eq] at w
    obtain ⟨-, -, wr, -⟩ := (LBool.WT_Ite _ _ _ _).1 w
    obtain ⟨⟨-, h2, -⟩, w1, w2⟩ := (L.WT_FRem _ _ _).1 wr
    obtain ⟨rfl, h1⟩ := WT_lit.1 w1
    obtain ⟨rfl, h4⟩ := WT_lit.1 w2
    simp only [B.ty_node] at h2
    exact ⟨rfl, rfl, h1, h4, (L.TFloat_inj _ _ h2).symm⟩
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;>
    obtain ⟨ht1, ht2, h1, h2, hp⟩ := key w <;> subst ht1 ht2
  · obtain ⟨e1, e2, -⟩ := hO.float_orc.fmod f1 f2 h1 h2 hp
    refine ⟨lit_WT e2, ?_⟩
    rw [lit_ty, L.float_raw_fmod_of_rem_eq]
    simp only [B.ty_node, e1]
  · have := (hO.float_orc.fmod f1 f2 h1 h2 hp).2.2 ρ
    simp only [Syntax.lit] at this
    rw [Kanon.Sem.eval_eq_ev (by simpa only [B.ty_node] using w)] at this
    simp only [B.ty_node] at e this
    rw [this] at e
    rw [Sem.ev_Float]; exact e

end FloatMod
