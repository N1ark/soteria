import Tiny.Lemmas

/-!
# Congruence

`kanon_congr` (declared by Kanon's library) proves `Refines s s'`, where `s'` is
`s` with some of its subterms replaced by terms that refine them (hypotheses of
the context): the generated `Lifts.lean` proves with it that the specs are
monotone in their term arguments.
-/

namespace Tiny.Lib

/-- Proves `Refines s s'`, where `s'` is `s` with some of its subterms replaced
by terms that refine them (hypotheses of the context). The type of a node is
either fixed, or that of its first operand (`rem`) or of its branches (`ite`). -/
macro_rules
  | `(tactic| kanon_congr) => `(tactic| first
      | exact Refines.refl
      | assumption
      | ((first
          | apply Refines.unop
          | apply Refines.binop
          | apply Refines.ite) <;>
         first
           | (intro _; rfl)
           | exact Refines.ty_binop_left (by assumption)
           | exact Refines.ty_ite (by assumption)
           | kanon_congr))

end Tiny.Lib
