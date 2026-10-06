import BitvecMod.Statements.Bitvec.add
import BitvecMod.Lib.Rule
import BitvecMod.Lifts
import BitvecMod.Proofs.Laws

/-! The arms of `Bitvec.add` that `bv_arith` does not prove:

- the default arm: the unsigned check of an addition that cannot wrap around
  (`Lib.arith_refines_add_no_wrap`), then the order of the operands (`Add.comm`);
- the swaps of `r_factor` and `r_factor_const`: the products in the order of the main arm
  (`Mul.comm`), then the main arm. -/

namespace BitvecMod

@[kanon_arm] theorem Bitvec.add.r_default.main.proof : Bitvec.add.r_default.main.Stmt := by
  intro S _ _ B LBool LCore L _ _ _ O hO checked v1 v2
  refine Kanon.Sem.Refines.trans Lib.arith_refines_add_no_wrap ?_
  split
  · exact Kanon.Sem.Refines.refl
  · exact Add.comm.proof L _ v1 v2 _

theorem Bitvec.add.r_factor.main.aux : Bitvec.add.r_factor.main.Stmt := by
  bv_arith

@[kanon_arm] theorem Bitvec.add.r_factor.swap1.proof : Bitvec.add.r_factor.swap1.Stmt := by
  intro S _ _ B LBool LCore L _ _ _ O hO checked ck1 b a t5 ck2 k9 c t11 hg
  unfold Bitvec.add.spec
  refine Kanon.Sem.Refines.trans (Lib.refines_add (t' := S.ty (B.node (L.MulK ck1 a b) t5))
    (Mul.comm.proof L ck1 b a t5) Kanon.Sem.Refines.refl
    (fun _ => by simp only [Kanon.Base.ty_node])) ?_
  exact Bitvec.add.r_factor.main.aux L O hO checked ck1 a b t5 ck2 k9 c t11 hg

@[kanon_arm] theorem Bitvec.add.r_factor.swap2.proof : Bitvec.add.r_factor.swap2.Stmt := by
  intro S _ _ B LBool LCore L _ _ _ O hO checked ck1 a b t5 ck2 c k9 t11 hg
  unfold Bitvec.add.spec
  refine Kanon.Sem.Refines.trans (Lib.refines_add Kanon.Sem.Refines.refl
    (Mul.comm.proof L ck2 c k9 t11) (fun _ => rfl)) ?_
  exact Bitvec.add.r_factor.main.aux L O hO checked ck1 a b t5 ck2 k9 c t11 hg

@[kanon_arm] theorem Bitvec.add.r_factor.swap1_swap2.proof :
    Bitvec.add.r_factor.swap1_swap2.Stmt := by
  intro S _ _ B LBool LCore L _ _ _ O hO checked ck1 b a t5 ck2 c k9 t11 hg
  unfold Bitvec.add.spec
  refine Kanon.Sem.Refines.trans (Lib.refines_add (t' := S.ty (B.node (L.MulK ck1 a b) t5))
    (Mul.comm.proof L ck1 b a t5)
    (Mul.comm.proof L ck2 c k9 t11) (fun _ => by simp only [Kanon.Base.ty_node])) ?_
  exact Bitvec.add.r_factor.main.aux L O hO checked ck1 a b t5 ck2 k9 c t11 hg

theorem Bitvec.add.r_factor_const.main.aux : Bitvec.add.r_factor_const.main.Stmt := by
  bv_arith

@[kanon_arm] theorem Bitvec.add.r_factor_const.swap1.proof :
    Bitvec.add.r_factor_const.swap1.Stmt := by
  intro S _ _ B LBool LCore L _ _ _ O hO checked ck1 r1 k1 t4 t7 ck2 k2 t12 r2 t15 hg
  unfold Bitvec.add.spec
  refine Kanon.Sem.Refines.trans
    (Lib.refines_add (t' := S.ty (B.node (L.MulK ck1 (B.node (L.BitVecK k1) t4) r1) t7))
      (Mul.comm.proof L ck1 r1 _ t7) Kanon.Sem.Refines.refl
      (fun _ => by simp only [Kanon.Base.ty_node])) ?_
  exact Bitvec.add.r_factor_const.main.aux L O hO checked ck1 k1 t4 r1 t7 ck2 k2 t12 r2 t15 hg

@[kanon_arm] theorem Bitvec.add.r_factor_const.swap2.proof :
    Bitvec.add.r_factor_const.swap2.Stmt := by
  intro S _ _ B LBool LCore L _ _ _ O hO checked ck1 k1 t4 r1 t7 ck2 r2 k2 t12 t15 hg
  unfold Bitvec.add.spec
  refine Kanon.Sem.Refines.trans (Lib.refines_add Kanon.Sem.Refines.refl
    (Mul.comm.proof L ck2 r2 _ t15) (fun _ => rfl)) ?_
  exact Bitvec.add.r_factor_const.main.aux L O hO checked ck1 k1 t4 r1 t7 ck2 k2 t12 r2 t15 hg

@[kanon_arm] theorem Bitvec.add.r_factor_const.swap1_swap2.proof :
    Bitvec.add.r_factor_const.swap1_swap2.Stmt := by
  intro S _ _ B LBool LCore L _ _ _ O hO checked ck1 r1 k1 t4 t7 ck2 r2 k2 t12 t15 hg
  unfold Bitvec.add.spec
  refine Kanon.Sem.Refines.trans
    (Lib.refines_add (t' := S.ty (B.node (L.MulK ck1 (B.node (L.BitVecK k1) t4) r1) t7))
      (Mul.comm.proof L ck1 r1 _ t7) (Mul.comm.proof L ck2 r2 _ t15)
      (fun _ => by simp only [Kanon.Base.ty_node])) ?_
  exact Bitvec.add.r_factor_const.main.aux L O hO checked ck1 k1 t4 r1 t7 ck2 k2 t12 r2 t15 hg

end BitvecMod
