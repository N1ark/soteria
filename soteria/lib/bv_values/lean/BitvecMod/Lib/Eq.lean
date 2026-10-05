import BitvecMod.Lib.Tactic

/-!
# Equality, the boolean rules and the overflow checks

The lemmas and tactics of the arms of `Bool.eq`, `and_`, `or_`, `not_` of the module,
`Bitvec.add_overflows`, `sub_overflows`, `mul_overflows`, `div`, `rem`, `mod_`, over the interface: the
counterparts of the language's `Kanon/Lib/Eq.lean`, `Ovf.lean` and `Bool.lean`, being
ported (see the plan of the generic port).
-/
