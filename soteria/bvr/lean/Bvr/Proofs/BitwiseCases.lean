import Bvr.Lib.Tactic

/-! Bitwise operations and shifts, proved per alternative. -/

namespace Bvr

open Classical Lib

theorem bv_not.r_lit.a1.proof : bv_not.r_lit.a1.Stmt := by
  bvr_rule

theorem bv_not.r_ite.a1.proof : bv_not.r_ite.a1.Stmt := by
  bvr_rule

theorem bv_not.r_default.a1.proof : bv_not.r_default.a1.Stmt := by
  bvr_rule

end Bvr
