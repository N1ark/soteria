import FloatMod.Lib.Rule
import FloatMod.Statements.Float.round

/-! The arms of `Float.round` that the default tactic does not prove. -/

namespace FloatMod

open Classical Kanon Kanon.Sem CoreMod Lib

@[kanon_arm] theorem Float.round.r_lit.main.proof : Float.round.r_lit.main.Stmt := by
  intro S _ _ B LBool LCore LBitvec L _ _ _ _ O hO rm f t
  simp only [kanon_spec]
  refine Refines.un_lit (fun a t w => ((L.WT_FRound rm a t).1 w).2) (Sem.ev_FRound · rm)
    (fun w ht1 hf => ?_) (fun hf ρ => ?_)
  · obtain ⟨hp, hw, -⟩ := hO.float_orc.round rm f hf
    rw [L.WT_FRound] at w
    refine ⟨lit_WT hw, ?_⟩
    rw [lit_ty, w.1.2, B.ty_node, ht1, hp]
  · rw [Sem.ev_Float, (hO.float_orc.round rm f hf).2.2]

end FloatMod
