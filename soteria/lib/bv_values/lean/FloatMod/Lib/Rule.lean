import FloatMod.Lib.Float
import BitvecMod.Lib.Rule

/-!
# The default proof of the arms of the float module

The arms of the float module, and those it adds to the functions of the
modules it uses (`Bool.eq`), are proved by the tactic of their function
(`attribute [kanon_tactic "…"] Float.f.spec`), or by `bv_rule`, the tactic of
the bitvec module (`BitvecMod/Lib/Rule.lean`).
-/

namespace FloatMod

attribute [kanon_tactic "bv_rule"] Syntax

end FloatMod
