import Lean

/-!
# The simp sets of the proofs of the bitvec module

- `bv_den`: the equations of `Sem.den` and `Sem.denB` at the nodes;
- `bv_wt`: the typing of the nodes, and the facts on sorts;
- `bv_lits`: the primitives and the helpers that build terms, unfolded to
  `Prim` and to nodes;
- `bv_ofInt`: the operations on literals (in range) as the operations on their
  values (`BitVec.ofInt n (Prim.lit_add n a b) = …`), and the like;
- `bv_range`: that the results of the operations on literals are in range
  (`0 ≤ Prim.lit_add w a b`, …), for the typing of the literals they build.

The lemmas of a library file join these sets with `attribute [bv_ofInt] …`, so
that the tactics of `Lib/Tactic.lean` use them.
-/

register_simp_attr bv_den
register_simp_attr bv_wt
register_simp_attr bv_lits
register_simp_attr bv_ofInt
register_simp_attr bv_range
