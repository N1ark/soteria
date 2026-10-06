import FloatMod.Lib.Rule
import FloatMod.Statements.Float.sqrt

/-! The arms of `Float.sqrt` that the default tactic does not prove. -/

namespace FloatMod

open Classical Kanon Kanon.Sem CoreMod Lib

@[kanon_arm] theorem Float.sqrt.r_lit.main.proof : Float.sqrt.r_lit.main.Stmt := by
  intro S _ _ B LBool LCore LBitvec L _ _ _ _ O hO f t
  simp only [kanon_spec]
  refine Refines.un_lit (fun a t w => ((L.WT_FSqrt a t).1 w).2) Sem.ev_FSqrt (fun w ht1 hf => ?_)
    (fun hf ρ => ?_)
  · obtain ⟨hp, hw, -⟩ := hO.float_orc.sqrt f hf
    rw [L.WT_FSqrt] at w
    refine ⟨lit_WT hw, ?_⟩
    rw [lit_ty, w.1.2, B.ty_node, ht1, hp]
  · rw [Sem.ev_Float, (hO.float_orc.sqrt f hf).2.2]

end FloatMod
