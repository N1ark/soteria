import FloatMod.Lib.Rule
import FloatMod.Statements.Float.cast

/-! The arms of `Float.cast` that the default tactic does not prove. -/

namespace FloatMod

open Classical Kanon Kanon.Sem CoreMod Lib

@[kanon_arm] theorem Float.cast.r_lit.main.proof : Float.cast.r_lit.main.Stmt := by
  intro S _ _ B LBool LCore LBitvec L _ _ _ _ O hO rm p f t
  simp only [kanon_spec]
  refine Refines.un_lit (fun a t w => ((L.WT_FloatOfFloat rm p a t).1 w).2)
    (Sem.ev_FloatOfFloat · rm p) (fun w ht1 hf => ?_) (fun hf ρ => ?_)
  · obtain ⟨hp, hw, -⟩ := hO.float_orc.convert rm p f hf
    rw [L.WT_FloatOfFloat] at w
    exact ⟨lit_WT hw, by rw [lit_ty, w.1.2, hp]⟩
  · rw [Sem.ev_Float, (hO.float_orc.convert rm p f hf).2.2]

end FloatMod
