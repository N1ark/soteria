import FloatMod.Lib.Rule
import FloatMod.Statements.Float.leq

/-! The arms of `Float.leq` that the default tactic does not prove. -/

namespace FloatMod

open Classical Kanon Kanon.Sem CoreMod Lib

@[kanon_arm] theorem Float.leq.r_lits.main.proof : Float.leq.r_lits.main.Stmt := by
  intro S _ _ B LBool LCore LBitvec L _ _ _ _ O hO f1 t1 f2 t2
  simp only [kanon_spec, Sem.f_le_eq, Prim.f_le]
  exact Refines.cmp_lits L.WT_FLeq Sem.ev_FLeq

end FloatMod
