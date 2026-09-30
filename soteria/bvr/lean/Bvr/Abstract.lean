import Bvr.Types

/-!
# The abstract types of the svalue grammar

The svalue grammar mirrors `soteria/lib/bv_values/svalue_ast.ml`: bvr generates
it from `soteria/lib/bv_values/rules/lang.bvl`, in `Types.lean` and in
`Syntax.lean`. Widths and indices are `Int`s, like OCaml's `int`s; hash-consed
terms are modelled as trees, so that the physical equality of hash-consed terms
is structural equality.

This file defines the types that `lang.bvl` declares without defining them.
-/

namespace Bvr

/-- A concrete float of Floatml, given by its precision and bit pattern. -/
structure Float where
  prec : Fp
  bits : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Values of an extension, which the rules never inspect. -/
structure Ext where
  id : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Types of an extension. -/
structure ExtTy where
  id : Nat
  deriving DecidableEq, Repr, Inhabited

end Bvr
