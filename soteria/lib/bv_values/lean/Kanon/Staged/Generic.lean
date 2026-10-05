import Kanon.Lang.Bitvec
import Kanon.Lang.Float
import Kanon.Lang.Ptr
import BitvecMod.Soundness.Laws
import Kanon.Staged.Ported.BvArith
import Kanon.Staged.Ported.BvCompare
import Kanon.Staged.Ported.BvEq
import Kanon.Staged.Ported.BvResize
import Kanon.Staged.Ported.FloatPtr

/-!
# The generic proofs of the bitvec, float and ptr modules, as they are ported

The bitvec, float and ptr modules are being ported to proofs over their
interfaces (`BitvecMod`, `FloatMod`, `PtrMod`), proved once like `CoreMod`
and `ExistsMod`. Until all their arms are, the rules do not mark them
`[@@@lean_module]`, so the language's own proofs of their arms
(`Kanon/Soundness/`) still build, and their generic files are staged: Kanon
generates them with the marks on (`stage.sh`), and the interfaces of the
language (`Interface/*.lean`) are staged here (`Interface/`).

This file imports the language's instances of their semantics (`Lang/`) and
the arms proved so far (`Ported/`, a file per work package), so that `lake build` checks them (and
`check_axioms.lean` that they do not depend on `sorryAx`).
-/
