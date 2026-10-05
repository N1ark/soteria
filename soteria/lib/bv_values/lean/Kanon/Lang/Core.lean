import Kanon.Interface.Core
import CoreMod.Sem

/-! # The language, for the core module, which needs nothing of its semantics -/

namespace Kanon

open Classical

variable (FS : FloatSem)

/-- The core module needs nothing of the semantics. -/
instance coreSem : CoreMod.Sem (S := sem FS) (coreSyntax FS) := {}

end Kanon
