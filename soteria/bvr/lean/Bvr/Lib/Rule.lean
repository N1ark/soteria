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
  | (bvr_rule_b; done)
  | (bvr_rule_typed; done)
  | (bvr_rule_ev; done)
  | (bvr_rule_bounds; done))

/-- The rule tactic of `bv_lt_zero`: `v <s 0` is the sign bit of `v`. -/
macro "bvr_msb" : tactic => `(tactic| (
  bvr_rule_b_sem
  all_goals simp only [BitVec.slt_zero_eq_msb] at *
  all_goals (try simp_all [BitVec.msb_signExtend, BitVec.msb_not, BitVec.msb_append,
    BitVec.msb_setWidth, BitVec.msb_srem])
  all_goals (rename_i h; first
    | (split at h
       all_goals (try simp (disch := omega) only [Nat.sub_eq_zero_of_le] at h)
       all_goals simpa [BitVec.msb] using h)
    | (simp (disch := omega) [BitVec.getLsbD_of_ge] at h; done)
    | (split at h
       · omega
       · exact h))))

attribute [bvr_tactic "bvr_msb"] bv_lt_zero.spec

open Lean Elab Term in
/-- `bvr_proof% X`: the proof of the statement `X.Stmt` of an arm, by its
hand-written proof (`bvr_arm`) if there is one, and otherwise by the tactic of
its function (`bvr_tactic`), or `bvr_auto`. -/
elab "bvr_proof% " x:ident : term => do
  let n := `Bvr ++ x.getId
  let env ← getEnv
  if let some p := (bvrArmExt.getState env).find? n then return mkConst p
  let f := x.getId.components.head!
  let tac ← match (bvrTacticExt.getState env).find? (`Bvr ++ f ++ `spec) with
    | some t => do
      let t ← ofExcept (Parser.runParserCategory env `tactic t)
      `(tactic| first | ($(⟨t⟩):tactic; done) | bvr_auto)
    | none => `(tactic| bvr_auto)
  let seq ← `(Lean.Parser.Tactic.tacticSeq| $tac:tactic)
  elabTermEnsuringType (← `(by $seq)) (some (mkConst (n ++ `Stmt)))

end Bvr.Lib
