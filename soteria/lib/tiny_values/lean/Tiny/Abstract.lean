import Tiny.Types

/-!
# The abstract types of Tiny_values

The terms of Tiny_values mirror `soteria/lib/tiny_values/svalue.ml`: Kanon
generates them from `soteria/lib/tiny_values/rules/lang.knl`, in `Types.lean` and
in `Syntax.lean`. Hash-consed terms are modelled as trees, so that the physical
equality of hash-consed terms is structural equality.

`lang.knl` declares no abstract type (variables are `Int`s), so this file only
brings the generated types into scope of `Syntax.lean`.
-/
