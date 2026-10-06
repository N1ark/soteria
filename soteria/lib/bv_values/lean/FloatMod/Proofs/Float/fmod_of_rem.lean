import FloatMod.Soundness.Laws
import FloatMod.Statements.Float.fmod_of_rem

/-! The arm of `Float.fmod_of_rem`, whose two sides are the same term once
`float_raw_fmod_of_rem` is unfolded. -/

namespace FloatMod

open Classical Kanon Kanon.Sem CoreMod Lib

attribute [local kanon_body] Syntax.float_raw_fmod_of_rem_eq in
@[kanon_arm] theorem Float.fmod_of_rem.r_main.main.proof : Float.fmod_of_rem.r_main.main.Stmt := by
  kanon_rule_lift
  simp only [Kanon.Base.ty_node]
  exact Refines.refl

end FloatMod
