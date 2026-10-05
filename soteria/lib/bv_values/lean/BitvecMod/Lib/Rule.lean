import BitvecMod.Lib.Tactic
import BitvecMod.Lib.Arith
import BitvecMod.Lib.Compare
import BitvecMod.Lib.Eq
import BitvecMod.Lib.Resize

/-!
# The default proof of the arms of the bitvec module

`bv_rule` (`Lib/Tactic.lean`) proves the arms of the rule functions of the
module, and those it adds to the functions of the modules it uses
(`Bool.eq`, …), unless they have a hand-written proof (`Proofs/`) or their
function has a tactic of its own (`attribute [kanon_tactic "…"] Bitvec.f.spec`,
given by the library file of its rules: `Lib/Arith.lean`, `Lib/Compare.lean`,
`Lib/Eq.lean`, `Lib/Resize.lean`).
-/

namespace BitvecMod

attribute [kanon_tactic "bv_rule"] Syntax

end BitvecMod
