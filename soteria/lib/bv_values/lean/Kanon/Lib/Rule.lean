import Kanon.Lib.Bool
import Kanon.Lib.Compare
import Kanon.Lib.Eq
import Kanon.Lib.Resize
import Kanon.Lib.Bitwise

/-! The default proof of the arms. -/

namespace Kanon.Lib

/-- The rule tactics of the libraries, in turn. -/
macro_rules | `(tactic| kanon_auto) => `(tactic| first
  | (kanon_rule_bv; done)
  | (kanon_rule_b; done)
  | (kanon_rule_typed; done)
  | (kanon_rule_ev; done)
  | (kanon_rule_bounds; done))

/-- The rule tactic of `bv_lt_zero`: `v <s 0` is the sign bit of `v`. -/
macro "kanon_msb" : tactic => `(tactic| (
  kanon_rule_b_sem
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

attribute [kanon_tactic "kanon_msb"] bv_lt_zero.spec

end Kanon.Lib
