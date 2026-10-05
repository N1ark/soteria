import Kanon.Types

/-!
# The abstract types of the svalue grammar

Kanon generates the types of the language from `soteria/lib/bv_values/rules/lang.knl`,
in `Types.lean` and in `Syntax.lean`. Widths and indices are `Int`s, like OCaml's `int`s; hash-consed
terms are modelled as trees, so that the physical equality of hash-consed terms
is structural equality.

The language declares no abstract type of its own: that of floats is the core
module's (`CoreMod/Abstract.lean`).
-/
