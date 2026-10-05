import Kanon.Lib.Rule
import Kanon.Statements.Float.fmod_of_rem

/-! The arm of `Float.fmod_of_rem`: its spec is the helper `raw_fmod_of_rem`,
which `kanon_refl` (up to reducible definitions) does not unfold. -/

namespace Kanon

open Classical Lib

attribute [local kanon_body] Float.raw_fmod_of_rem in
@[kanon_arm] theorem Float.fmod_of_rem.r_main.main.proof : Float.fmod_of_rem.r_main.main.Stmt := by
  kanon_rule_bv

end Kanon
