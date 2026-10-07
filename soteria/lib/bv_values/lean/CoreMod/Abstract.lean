import CoreMod.Types

/-!
# The abstract types of the core module

Kanon generates the data types of the core module (`../rules/core.knl`) in
`Types.lean`; this file defines the one that it declares without defining it.
-/

namespace CoreMod

/-- A concrete float of Floatml, given by its precision and bit pattern. -/
structure Float where
  prec : Fp
  bits : Nat
  deriving DecidableEq, Repr, Inhabited

end CoreMod
