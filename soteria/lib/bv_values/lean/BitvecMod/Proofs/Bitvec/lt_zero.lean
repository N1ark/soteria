import BitvecMod.Lib.Rule
import KanonBool.Lib.Lift
import BitvecMod.Statements.Bitvec.lt_zero

/-! The arms of `Bitvec.lt_zero` that its tactic does not prove. -/

namespace BitvecMod

open Classical Kanon Lib

/-- `lt_zero (ite g l r)` is `ite g (lt_zero l) (lt_zero r)`. -/
theorem Lib.cmp_lt_zero_ite {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty]
    {B : Kanon.Base S} {LBool : KanonBool.Syntax B} {LCore : CoreMod.Syntax B}
    {L : Syntax B LBool LCore} [KanonBool.Sem LBool] [CoreMod.Sem LCore] [Sem L]
    {g l r : S.Term} {t : S.Ty} :
    S.Refines (Bitvec.lt_zero.spec L (B.node (LBool.IteK g l r) t))
      (B.node (LBool.IteK g (Bitvec.lt_zero.spec L l) (Bitvec.lt_zero.spec L r)) LBool.TBool) := by
  simp only [kanon_spec]
  bv_rule_apply
  all_goals first
    | (bv_rs_wt; done)
    | bv_msb_sem

@[kanon_arm] theorem Bitvec.lt_zero.r_ite.main.proof : Bitvec.lt_zero.r_ite.main.Stmt := by
  intro S _ _ B LBool LCore L _ _ _ O hO g l r t
  simp only
  split
  · rename_i he
    simp only [decide_eq_true_eq] at he
    exact Kanon.Sem.Refines.trans cmp_lt_zero_ite (Kanon.Sem.Refines.trans
      (KanonBool.Sem.refines_ite Kanon.Sem.Refines.refl (hO.bitvec_lt_zero l)
        (he ▸ hO.bitvec_lt_zero r) (fun _ => rfl)) cmp_refines_ite_same)
  · exact Kanon.Sem.Refines.refl

end BitvecMod
