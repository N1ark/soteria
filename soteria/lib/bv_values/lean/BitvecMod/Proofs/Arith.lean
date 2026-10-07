import BitvecMod.Proofs.ArithLib
import BitvecMod.Statements.Comm
import BitvecMod.Statements.Bitvec.add
import BitvecMod.Statements.Bitvec.and_
import BitvecMod.Statements.Bitvec.mul
import BitvecMod.Statements.Bitvec.neg
import BitvecMod.Statements.Bitvec.not_
import BitvecMod.Statements.Bitvec.or_
import BitvecMod.Statements.Bitvec.sub
import BitvecMod.Proofs.IteLib

/-!
# The proofs of the arithmetic arms of the bitvec module

The arms of `Bitvec.add`, `sub`, `mul`, `neg`, `not_`, `and_`, `or_`, `xor`,
`of_bool`, `to_bool`, `not_bool` and of the overflow functions are proved by
`bv_arith` (`Proofs/ArithLib.lean`), and the commutativity of `Add`, `Mul`,
`AddOvf` and `MulOvf` too; `Bitvec.or_.r_extend_shl` by hand, on its bits, and
`Bitvec.sub.r_add_const.swap` from its main arm, and the arms that distribute an operation
over conditionals by `bv_ite_arm` (`Proofs/IteLib.lean`).
-/

namespace BitvecMod

attribute [kanon_tactic "bv_arith"] Bitvec.add.spec Bitvec.sub.spec Bitvec.mul.spec
  Bitvec.neg.spec Bitvec.not_.spec Bitvec.and_.spec Bitvec.or_.spec Bitvec.xor.spec
  Bitvec.of_bool.spec Bitvec.to_bool.spec Bitvec.not_bool.spec Bitvec.add_overflows.spec
  Bitvec.sub_overflows.spec Bitvec.mul_overflows.spec Bitvec.neg_overflows.spec

@[kanon_arm] theorem Add.comm.proof : Add.comm.Stmt := by bv_arith
@[kanon_arm] theorem Mul.comm.proof : Mul.comm.Stmt := by bv_arith
@[kanon_arm] theorem AddOvf.comm.proof : AddOvf.comm.Stmt := by bv_arith
@[kanon_arm] theorem MulOvf.comm.proof : MulOvf.comm.Stmt := by bv_arith

@[kanon_arm] theorem Bitvec.add.r_ite.main.proof : Bitvec.add.r_ite.main.Stmt := by bv_ite_arm
@[kanon_arm] theorem Bitvec.sub.r_ite_ite.main.proof : Bitvec.sub.r_ite_ite.main.Stmt := by
  bv_ite_arm
@[kanon_arm] theorem Bitvec.sub.r_ite_l.main.proof : Bitvec.sub.r_ite_l.main.Stmt := by bv_ite_arm
@[kanon_arm] theorem Bitvec.sub.r_ite_r.main.proof : Bitvec.sub.r_ite_r.main.Stmt := by bv_ite_arm
@[kanon_arm] theorem Bitvec.mul.r_ite.main.proof : Bitvec.mul.r_ite.main.Stmt := by bv_ite_arm
@[kanon_arm] theorem Bitvec.neg.r_ite.main.proof : Bitvec.neg.r_ite.main.Stmt := by bv_ite_arm
@[kanon_arm] theorem Bitvec.not_.r_ite.main.proof : Bitvec.not_.r_ite.main.Stmt := by bv_ite_arm
@[kanon_arm] theorem Bitvec.and_.r_ite.main.proof : Bitvec.and_.r_ite.main.Stmt := by bv_ite_arm

@[kanon_arm] theorem Bitvec.sub.r_add_const.main.proof : Bitvec.sub.r_add_const.main.Stmt := by
  bv_arith

/-- `sub.r_add_const` with the sum swapped, from the main arm by `Add.comm` (the generated
proof re-runs `bv_arith`, as the right-hand side mentions the sum). -/
@[kanon_arm] theorem Bitvec.sub.r_add_const.swap.proof : Bitvec.sub.r_add_const.swap.Stmt := by
  intro S _ _ _ _ _ _ O hO checked c l k1 t__4 t__6 k2 t__9
  have hm := Bitvec.sub.r_add_const.main.proof O hO checked c k1 t__4 l t__6 k2 t__9
  simp only [Bitvec.size, ty_mk] at hm ⊢
  refine Kanon.Sem.Refines.trans ?_ hm
  have := Add.comm.proof c l (mk (.BitVec k1) t__4) t__6
  simp only [Bitvec.sub.spec, ty_mk]
  kanon_congr

/-- The bits of `zext base ||| (zext tail << size base)` are those of the
concatenation of `tail` (or of its low bits) and `base`, of the widths that the
typing gives (equal up to arithmetic, `bv_eq_cast`). -/
@[kanon_arm] theorem Bitvec.or_.r_extend_shl.main.proof : Bitvec.or_.r_extend_shl.main.Stmt := by
  (try intro _)
  intros
  kanon_rule_lift
  all_goals kanon_on_refines (
    (try dsimp only)
    bv_split_ifs
    all_goals (try kanon_lift_body)
    all_goals (try simp only [kanon_spec, kanon_body]))
  all_goals kanon_on_refines (
    refine Kanon.Sem.Refines.intro ?_ ?_
    · bv_arith_wt)
  all_goals bv_arith_sem_core
  all_goals (try simp only [withW_none, asBV_none, binOp_none_l, binOp_none_r, Option.map_none,
    reduceCtorEq] at e)
  all_goals (try simp (disch := omega) only [Arith.asBV_bv_cast, binOp_some, Option.map_some,
    Option.some.injEq] at e)
  all_goals (try subst e)
  all_goals (try (refine ⟨_, _, ⟨rfl, HEq.rfl⟩, ?_⟩))
  all_goals (try simp only [asBV_bv, Option.map_some, Option.bind_some, Option.some.injEq])
  all_goals (try (refine Arith.bv_eq_cast (by omega) ?_))
  all_goals (apply BitVec.eq_of_getLsbD_eq; intro i hi)
  all_goals (simp only [BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_or,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, BitVec.shiftLeft_eq', BitVec.getLsbD_extractLsb',
    BitVec.toNat_cast])
  all_goals (simp (disch := omega) only [Arith.toNat_ofInt_natCast_of_le])
  all_goals (split <;> rename_i hc)
  all_goals (try simp (disch := omega) only [BitVec.getLsbD_of_ge, decide_eq_true, decide_eq_false,
    Nat.zero_add, Bool.true_and, Bool.and_true, Bool.not_true, Bool.not_false, Bool.false_and,
    Bool.and_false, Bool.or_false, Bool.false_or])

end BitvecMod
