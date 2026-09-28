import Bvr.Lib.Bool
import Bvr.Lib.Compare
import Bvr.Lib.Eq
import Bvr.Lib.Resize
import Bvr.Lib.Bitwise

/-! The default proof of the arms. -/

namespace Bvr.Lib

/-- The rule tactics of the libraries, in turn. -/
macro "bvr_auto" : tactic => `(tactic| first
  | (bvr_rule; done)
  | (bvr_rule_r; done)
  | (bvr_rule_b; done)
  | (bvr_rule_typed; done)
  | (bvr_rule_ev; done)
  | (bvr_rule_bounds; done)
  | (bvr_cmp; done))

open Lean Elab Term in
/-- `bvr_proof% X`: the proof of the statement `X.Stmt` of an arm, by its
hand-written proof `X.proof` if there is one, and by `bvr_auto` otherwise. -/
elab "bvr_proof% " x:ident : term => do
  let n := `Bvr ++ x.getId
  if (← getEnv).contains (n ++ `proof) then return mkConst (n ++ `proof)
  elabTermEnsuringType (← `(by bvr_auto)) (some (mkConst (n ++ `Stmt)))

end Bvr.Lib
