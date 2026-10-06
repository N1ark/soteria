import FloatMod.Lib.Rule
import FloatMod.Statements.Float.is_negative

/-! The arms of `Float.is_negative` that the default tactic does not prove. -/

namespace FloatMod

open Classical Kanon Kanon.Sem CoreMod Lib

@[kanon_arm] theorem Float.is_negative.r_lit.main.proof : Float.is_negative.r_lit.main.Stmt := by
  intro S _ _ B LBool LCore LBitvec L _ _ _ _ O hO f t
  simp only [kanon_spec]
  refine Refines.un_lit (fun a t w => ((L.WT_FIsNeg a t).1 w).2) Sem.ev_FIsNeg
    (fun w ht1 hf => ?_) (fun hf ρ => ?_)
  · exact ⟨(LBool.WT_Bool _ _).2 rfl, by rw [B.ty_node]⟩
  · rw [KanonBool.Sem.ev_Bool, Sem.f_is_negative_eq]; rfl

end FloatMod
