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
  | (bvr_rule_bounds; done)
  | (bvr_cmp; done))

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

open Lean Elab Term in
/-- `bvr_proof% X`: the proof of the statement `X.Stmt` of an arm, by its
hand-written proof `X.proof` if there is one, and otherwise by the rule tactic
of the library of its function, or `bvr_auto`. -/
elab "bvr_proof% " x:ident : term => do
  let n := `Bvr ++ x.getId
  if (← getEnv).contains (n ++ `proof) then return mkConst (n ++ `proof)
  let tac ← match x.getId.components.head!.toString with
    | "bv_lt" | "bv_leq" => `(tactic| first | (bvr_cmp; done) | bvr_auto)
    | "bv_lt_zero" => `(tactic| first | (bvr_msb; done) | bvr_auto)
    | "sem_eq" | "bv_neg" | "bv_mod" | "bv_rem" | "bv_add_overflows" | "bv_sub_overflows"
    | "bv_mul_overflows" | "bv_neg_overflows" => `(tactic| first | (bvr_rule_b; done) | bvr_auto)
    | _ => `(tactic| bvr_auto)
  let seq ← `(Lean.Parser.Tactic.tacticSeq| $tac:tactic)
  elabTermEnsuringType (← `(by $seq)) (some (mkConst (n ++ `Stmt)))

end Bvr.Lib
