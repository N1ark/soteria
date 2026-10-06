import BitvecMod.Lib.Rule
import BitvecMod.Soundness.Laws
import BitvecMod.Statements.Bitvec.lt

/-! The arm of `Bitvec.lt` that `bv_cmp` does not prove:
`r_mul_mul.swap1_swap2`, which is `r_mul_mul.main` up to the order of the
products (`kanon_comm`). -/

namespace BitvecMod

open Classical Kanon Kanon.Sem Lib

@[kanon_arm] theorem Bitvec.lt.r_mul_mul.main.proof : Bitvec.lt.r_mul_mul.main.Stmt := by
  bv_cmp

@[kanon_arm] theorem Bitvec.lt.r_mul_mul.swap1_swap2.proof :
    Bitvec.lt.r_mul_mul.swap1_swap2.Stmt := by
  intro S _ _ B LBool LCore L _ _ _ O hO signed cl x a t5 cr y k t11 h
  refine Refines.trans ?_ (Bitvec.lt.r_mul_mul.main.proof L O hO signed cl a x t5 cr k y t11 h)
  simp only [kanon_spec]
  kanon_comm

end BitvecMod
