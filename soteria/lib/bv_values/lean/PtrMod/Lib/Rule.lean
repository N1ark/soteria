import PtrMod.Lib.Ptr
import BitvecMod.Lib.Rule

/-!
# The default proof of the arms of the ptr module

The arms of the ptr module, and those it adds to the functions of the modules
it uses (`Bool.eq`), are proved by the tactic of their function
(`attribute [kanon_tactic "…"] Ptr.f.spec`), or by `bv_rule`, the tactic of the
bitvec module (`BitvecMod/Lib/Rule.lean`).
-/

namespace PtrMod

attribute [kanon_tactic "bv_rule"] Syntax

end PtrMod
