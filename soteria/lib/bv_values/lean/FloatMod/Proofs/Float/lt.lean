import FloatMod.Lib.Rule
import FloatMod.Statements.Float.lt

/-! The arms of `Float.lt` that the default tactic does not prove. -/

namespace FloatMod

open Classical Kanon Kanon.Sem CoreMod Lib

@[kanon_arm] theorem Float.lt.r_lits.main.proof : Float.lt.r_lits.main.Stmt := by
  intro S _ _ B LBool LCore LBitvec L _ _ _ _ O hO f1 t1 f2 t2
  simp only [kanon_spec, Sem.f_lt_eq, Prim.f_lt]
  exact Refines.cmp_lits L.WT_FLt Sem.ev_FLt

end FloatMod
