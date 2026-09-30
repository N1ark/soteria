import Tiny.Lemmas

/-!
# Congruence

`kanon_congr` (Kanon's) proves `Refines s s'`, where `s'` is `s` with some of
its subterms replaced by terms that refine them (hypotheses of the context),
with the congruence lemmas of the nodes (`kanon_congr_lemma`): the generated
`Lifts.lean` proves with it that the specs are monotone in their term arguments.
The type of a node is either fixed, or that of its first operand (`rem`) or of
its branches (`ite`).
-/

namespace Tiny.Lib

macro_rules
  | `(tactic| kanon_congr_side) => `(tactic| first
      | exact Refines.ty_binop_left (by assumption)
      | exact Refines.ty_ite (by assumption))

end Tiny.Lib
