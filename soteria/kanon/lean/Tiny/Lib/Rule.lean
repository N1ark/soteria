import Tiny.Lib.Int

/-! The default proof of the arms. -/

namespace Tiny.Lib

/-- The rule tactics of the libraries, in turn. -/
macro_rules | `(tactic| kanon_auto) => `(tactic| first
  | (kanon_rule; done)
  | (kanon_rule_arith; done))

end Tiny.Lib
