import BitvecMod.Proofs.CompareLib
import BitvecMod.Proofs.IteLib
import BitvecMod.Statements.Bitvec.leq

/-!
# The proofs of the arms of `Bitvec.leq`

By `cmp_rule` (`CompareLib.lean`), `bv_ite_arm` (`IteLib.lean`) for the conditionals, or a
closer of their own.
-/

noncomputable section

namespace BitvecMod

open Classical Kanon

@[kanon_arm] theorem Bitvec.leq.r_add_add.main.proof : Bitvec.leq.r_add_add.main.Stmt := by
  intro S _ _ _ _ _ _ O hO signed cl l tl y t1 cr r tr x t2 hg
  simp only [Bitvec.const_keeps_in_range, cmp_zmin_eq_min, cmp_zmax_eq_max]
  cmp_lift
  all_goals kanon_on_refines (
    refine Kanon.Sem.Refines.intro (by cmp_wt) ?_
    cmp_sem_core
    cmp_norm
    cmp_norm
    cmp_add_add_close)

/-! The arms of `leq.r_add_add` with the left sum swapped, from the main arm by the
commutativity of `Add`. -/

@[kanon_arm] theorem Bitvec.leq.r_add_add.swap1.proof : Bitvec.leq.r_add_add.swap1.Stmt := by
  intro S _ _ _ _ _ _ O hO signed cl y l tl t1 cr r tr x t2 hg
  have h1 : S.Refines (mk (.Add cl y (mk (.BitVec l) tl)) t1) (mk (.Add cl (mk (.BitVec l) tl) y) t1) :=
    cmp_add_comm ..
  have h1' : S.Refines (mk (.Add cl (mk (.BitVec l) tl) y) t1) (mk (.Add cl y (mk (.BitVec l) tl)) t1) :=
    cmp_add_comm ..
  refine Kanon.Sem.Refines.trans ?_
    (Kanon.Sem.Refines.trans (Bitvec.leq.r_add_add.main.proof O hO signed cl l tl y t1 cr r tr x t2 hg) ?_)
  · simp only [Bitvec.leq.spec]
    kanon_congr
  · dsimp only
    simp only [Bitvec.size, ty_mk]
    (repeat' apply Kanon.Refinement.ite_congr) <;> first | exact Kanon.Sem.Refines.refl | kanon_congr

@[kanon_arm] theorem Bitvec.leq.r_add_add.swap1_swap2.proof :
    Bitvec.leq.r_add_add.swap1_swap2.Stmt := by
  intro S _ _ _ _ _ _ O hO signed cl y l tl t1 cr x r tr t2 hg
  have h1 : S.Refines (mk (.Add cl y (mk (.BitVec l) tl)) t1) (mk (.Add cl (mk (.BitVec l) tl) y) t1) :=
    cmp_add_comm ..
  have h1' : S.Refines (mk (.Add cl (mk (.BitVec l) tl) y) t1) (mk (.Add cl y (mk (.BitVec l) tl)) t1) :=
    cmp_add_comm ..
  have h2 : S.Refines (mk (.Add cr x (mk (.BitVec r) tr)) t2) (mk (.Add cr (mk (.BitVec r) tr) x) t2) :=
    cmp_add_comm ..
  have h2' : S.Refines (mk (.Add cr (mk (.BitVec r) tr) x) t2) (mk (.Add cr x (mk (.BitVec r) tr)) t2) :=
    cmp_add_comm ..
  refine Kanon.Sem.Refines.trans ?_
    (Kanon.Sem.Refines.trans (Bitvec.leq.r_add_add.main.proof O hO signed cl l tl y t1 cr r tr x t2 hg) ?_)
  · simp only [Bitvec.leq.spec]
    kanon_congr
  · dsimp only
    simp only [Bitvec.size, ty_mk]
    (repeat' apply Kanon.Refinement.ite_congr) <;> first | exact Kanon.Sem.Refines.refl | kanon_congr

@[kanon_arm] theorem Bitvec.leq.r_add_const.main.proof : Bitvec.leq.r_add_const.main.Stmt := by cmp_rule

@[kanon_arm] theorem Bitvec.leq.r_add_const.swap.proof : Bitvec.leq.r_add_const.swap.Stmt := by cmp_rule

@[kanon_arm] theorem Bitvec.leq.r_const_add.main.proof : Bitvec.leq.r_const_add.main.Stmt := by cmp_rule

/-! The arm `leq.r_const_mul`, one lemma per branch of its body (each branch a few goals of
`cmp_rule`, within the default budget). -/

theorem cmp_leq_cm_b0 :
  ∀ {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [BitvecMod.Lang S] [KanonBool.Typed S] [CoreMod.Typed S] [BitvecMod.Typed S] (O : Ops S), O.Sound →
  ∀ (signed : Bool) (c2 : Int) (t__2 : S.Ty) (checked : CoreMod.Checked) (x : S.Term) (c1 : Int) (t__7 : S.Ty) (t__9 : S.Ty),
  ((BitvecMod.Bitvec.checked_has signed checked) && (! (decide (c1 = (0 : Int))))) = true →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c1); let z2 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c2); ((BitvecMod.divisible z2 z1)) = true) →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c1); ((decide (z1 < (0 : Int)))) = true) →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c1); ((signed && ((decide (z1 = (-1 : Int))) && (BitvecMod.Bitvec.is_int_min (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c2)))) = true) →
  S.Refines (BitvecMod.Bitvec.leq.spec signed (BitvecMod.mk (.BitVec c2) t__2) (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__7)) t__9))
  (KanonBool.v_true) := by
  intros
  dsimp only at *
  cmp_lift
  cmp_halves

theorem cmp_leq_cm_b1 :
  ∀ {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [BitvecMod.Lang S] [KanonBool.Typed S] [CoreMod.Typed S] [BitvecMod.Typed S] (O : Ops S), O.Sound →
  ∀ (signed : Bool) (c2 : Int) (t__2 : S.Ty) (checked : CoreMod.Checked) (x : S.Term) (c1 : Int) (t__7 : S.Ty) (t__9 : S.Ty),
  ((BitvecMod.Bitvec.checked_has signed checked) && (! (decide (c1 = (0 : Int))))) = true →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c1); let z2 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c2); ((BitvecMod.divisible z2 z1)) = true) →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c1); ((decide (z1 < (0 : Int)))) = true) →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c1); ¬((signed && ((decide (z1 = (-1 : Int))) && (BitvecMod.Bitvec.is_int_min (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c2)))) = true) →
  S.Refines (BitvecMod.Bitvec.leq.spec signed (BitvecMod.mk (.BitVec c2) t__2) (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__7)) t__9))
  (O.bitvec_leq signed x (O.bitvec_div signed (BitvecMod.mk (.BitVec c2) t__2) (BitvecMod.mk (.BitVec c1) t__7))) := by
  intros
  dsimp only at *
  cmp_lift
  cmp_halves

theorem cmp_leq_cm_b2 :
  ∀ {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [BitvecMod.Lang S] [KanonBool.Typed S] [CoreMod.Typed S] [BitvecMod.Typed S] (O : Ops S), O.Sound →
  ∀ (signed : Bool) (c2 : Int) (t__2 : S.Ty) (checked : CoreMod.Checked) (x : S.Term) (c1 : Int) (t__7 : S.Ty) (t__9 : S.Ty),
  ((BitvecMod.Bitvec.checked_has signed checked) && (! (decide (c1 = (0 : Int))))) = true →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c1); let z2 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c2); ((BitvecMod.divisible z2 z1)) = true) →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c1); ¬((decide (z1 < (0 : Int)))) = true) →
  S.Refines (BitvecMod.Bitvec.leq.spec signed (BitvecMod.mk (.BitVec c2) t__2) (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__7)) t__9))
  (O.bitvec_leq signed (O.bitvec_div signed (BitvecMod.mk (.BitVec c2) t__2) (BitvecMod.mk (.BitVec c1) t__7)) x) := by
  intros
  dsimp only at *
  cmp_lift
  cmp_halves

theorem cmp_leq_cm_b3 :
  ∀ {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [BitvecMod.Lang S] [KanonBool.Typed S] [CoreMod.Typed S] [BitvecMod.Typed S] (O : Ops S), O.Sound →
  ∀ (signed : Bool) (c2 : Int) (t__2 : S.Ty) (checked : CoreMod.Checked) (x : S.Term) (c1 : Int) (t__7 : S.Ty) (t__9 : S.Ty),
  ((BitvecMod.Bitvec.checked_has signed checked) && (! (decide (c1 = (0 : Int))))) = true →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c1); let z2 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c2); ¬((BitvecMod.divisible z2 z1)) = true) →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c1); ((decide (z1 < (0 : Int)))) = true) →
  (let z2 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c2); ((decide (z2 < (0 : Int)))) = true) →
  S.Refines (BitvecMod.Bitvec.leq.spec signed (BitvecMod.mk (.BitVec c2) t__2) (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__7)) t__9))
  (O.bitvec_leq signed x (O.bitvec_div signed (BitvecMod.mk (.BitVec c2) t__2) (BitvecMod.mk (.BitVec c1) t__7))) := by
  intros
  dsimp only at *
  cmp_lift
  cmp_halves

theorem cmp_leq_cm_b4 :
  ∀ {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [BitvecMod.Lang S] [KanonBool.Typed S] [CoreMod.Typed S] [BitvecMod.Typed S] (O : Ops S), O.Sound →
  ∀ (signed : Bool) (c2 : Int) (t__2 : S.Ty) (checked : CoreMod.Checked) (x : S.Term) (c1 : Int) (t__7 : S.Ty) (t__9 : S.Ty),
  ((BitvecMod.Bitvec.checked_has signed checked) && (! (decide (c1 = (0 : Int))))) = true →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c1); let z2 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c2); ¬((BitvecMod.divisible z2 z1)) = true) →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c1); ((decide (z1 < (0 : Int)))) = true) →
  (let z2 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c2); ¬((decide (z2 < (0 : Int)))) = true) →
  S.Refines (BitvecMod.Bitvec.leq.spec signed (BitvecMod.mk (.BitVec c2) t__2) (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__7)) t__9))
  (O.bitvec_lt signed x (O.bitvec_div signed (BitvecMod.mk (.BitVec c2) t__2) (BitvecMod.mk (.BitVec c1) t__7))) := by
  intros
  dsimp only at *
  cmp_lift
  cmp_halves

theorem cmp_leq_cm_b5 :
  ∀ {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [BitvecMod.Lang S] [KanonBool.Typed S] [CoreMod.Typed S] [BitvecMod.Typed S] (O : Ops S), O.Sound →
  ∀ (signed : Bool) (c2 : Int) (t__2 : S.Ty) (checked : CoreMod.Checked) (x : S.Term) (c1 : Int) (t__7 : S.Ty) (t__9 : S.Ty),
  ((BitvecMod.Bitvec.checked_has signed checked) && (! (decide (c1 = (0 : Int))))) = true →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c1); let z2 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c2); ¬((BitvecMod.divisible z2 z1)) = true) →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c1); ¬((decide (z1 < (0 : Int)))) = true) →
  (let z2 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c2); ((decide (z2 < (0 : Int)))) = true) →
  S.Refines (BitvecMod.Bitvec.leq.spec signed (BitvecMod.mk (.BitVec c2) t__2) (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__7)) t__9))
  (O.bitvec_leq signed (O.bitvec_div signed (BitvecMod.mk (.BitVec c2) t__2) (BitvecMod.mk (.BitVec c1) t__7)) x) := by
  intros
  dsimp only at *
  cmp_lift
  cmp_halves

theorem cmp_leq_cm_b6 :
  ∀ {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [BitvecMod.Lang S] [KanonBool.Typed S] [CoreMod.Typed S] [BitvecMod.Typed S] (O : Ops S), O.Sound →
  ∀ (signed : Bool) (c2 : Int) (t__2 : S.Ty) (checked : CoreMod.Checked) (x : S.Term) (c1 : Int) (t__7 : S.Ty) (t__9 : S.Ty),
  ((BitvecMod.Bitvec.checked_has signed checked) && (! (decide (c1 = (0 : Int))))) = true →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c1); let z2 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c2); ¬((BitvecMod.divisible z2 z1)) = true) →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c1); ¬((decide (z1 < (0 : Int)))) = true) →
  (let z2 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec c2) t__2)) c2); ¬((decide (z2 < (0 : Int)))) = true) →
  S.Refines (BitvecMod.Bitvec.leq.spec signed (BitvecMod.mk (.BitVec c2) t__2) (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__7)) t__9))
  (O.bitvec_lt signed (O.bitvec_div signed (BitvecMod.mk (.BitVec c2) t__2) (BitvecMod.mk (.BitVec c1) t__7)) x) := by
  intros
  dsimp only at *
  cmp_lift
  cmp_halves

@[kanon_arm] theorem Bitvec.leq.r_const_mul.main.proof : Bitvec.leq.r_const_mul.main.Stmt := by
  intro S _ _ _ _ _ _ O hO signed c2 t2 checked x c1 t7 t9 hg
  dsimp only
  repeat' split
  all_goals first
    | exact cmp_leq_cm_b0 O hO signed c2 t2 checked x c1 t7 t9 hg ‹_› ‹_› ‹_›
    | exact cmp_leq_cm_b1 O hO signed c2 t2 checked x c1 t7 t9 hg ‹_› ‹_› ‹_›
    | exact cmp_leq_cm_b2 O hO signed c2 t2 checked x c1 t7 t9 hg ‹_› ‹_›
    | exact cmp_leq_cm_b3 O hO signed c2 t2 checked x c1 t7 t9 hg ‹_› ‹_› ‹_›
    | exact cmp_leq_cm_b4 O hO signed c2 t2 checked x c1 t7 t9 hg ‹_› ‹_› ‹_›
    | exact cmp_leq_cm_b5 O hO signed c2 t2 checked x c1 t7 t9 hg ‹_› ‹_› ‹_›
    | exact cmp_leq_cm_b6 O hO signed c2 t2 checked x c1 t7 t9 hg ‹_› ‹_› ‹_›

@[kanon_arm] theorem Bitvec.leq.r_const_sub1.main.proof : Bitvec.leq.r_const_sub1.main.Stmt := by cmp_rule

@[kanon_arm] theorem Bitvec.leq.r_const_sub2.main.proof : Bitvec.leq.r_const_sub2.main.Stmt := by cmp_rule

@[kanon_arm] theorem Bitvec.leq.r_ite_l.main.proof : Bitvec.leq.r_ite_l.main.Stmt := by
  bv_ite_arm

@[kanon_arm] theorem Bitvec.leq.r_ite_r.main.proof : Bitvec.leq.r_ite_r.main.Stmt := by
  bv_ite_arm

@[kanon_arm] theorem Bitvec.leq.r_lits.main.proof : Bitvec.leq.r_lits.main.Stmt := by cmp_rule

@[kanon_arm] theorem Bitvec.leq.r_max_r.main.proof : Bitvec.leq.r_max_r.main.Stmt := by cmp_rule

@[kanon_arm] theorem Bitvec.leq.r_min_l.main.proof : Bitvec.leq.r_min_l.main.Stmt := by cmp_rule

/-! The arm `leq.r_mul_const`, one lemma per branch of its body (each branch a few goals of
`cmp_rule`, within the default budget). -/

theorem cmp_leq_mc_b0 :
  ∀ {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [BitvecMod.Lang S] [KanonBool.Typed S] [CoreMod.Typed S] [BitvecMod.Typed S] (O : Ops S), O.Sound →
  ∀ (signed : Bool) (checked : CoreMod.Checked) (x : S.Term) (c1 : Int) (t__5 : S.Ty) (t__7 : S.Ty) (c2 : Int) (t__10 : S.Ty),
  ((BitvecMod.Bitvec.checked_has signed checked) && (! (decide (c1 = (0 : Int))))) = true →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c1); let z2 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c2); ((BitvecMod.divisible z2 z1)) = true) →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c1); ((decide (z1 < (0 : Int)))) = true) →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c1); ((signed && ((decide (z1 = (-1 : Int))) && (BitvecMod.Bitvec.is_int_min (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c2)))) = true) →
  S.Refines (BitvecMod.Bitvec.leq.spec signed (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7) (BitvecMod.mk (.BitVec c2) t__10))
  (KanonBool.v_false) := by
  intros
  dsimp only at *
  cmp_lift
  cmp_halves

theorem cmp_leq_mc_b1 :
  ∀ {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [BitvecMod.Lang S] [KanonBool.Typed S] [CoreMod.Typed S] [BitvecMod.Typed S] (O : Ops S), O.Sound →
  ∀ (signed : Bool) (checked : CoreMod.Checked) (x : S.Term) (c1 : Int) (t__5 : S.Ty) (t__7 : S.Ty) (c2 : Int) (t__10 : S.Ty),
  ((BitvecMod.Bitvec.checked_has signed checked) && (! (decide (c1 = (0 : Int))))) = true →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c1); let z2 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c2); ((BitvecMod.divisible z2 z1)) = true) →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c1); ((decide (z1 < (0 : Int)))) = true) →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c1); ¬((signed && ((decide (z1 = (-1 : Int))) && (BitvecMod.Bitvec.is_int_min (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c2)))) = true) →
  S.Refines (BitvecMod.Bitvec.leq.spec signed (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7) (BitvecMod.mk (.BitVec c2) t__10))
  (O.bitvec_leq signed (O.bitvec_div signed (BitvecMod.mk (.BitVec c2) t__10) (BitvecMod.mk (.BitVec c1) t__5)) x) := by
  intros
  dsimp only at *
  cmp_lift
  cmp_halves

theorem cmp_leq_mc_b2 :
  ∀ {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [BitvecMod.Lang S] [KanonBool.Typed S] [CoreMod.Typed S] [BitvecMod.Typed S] (O : Ops S), O.Sound →
  ∀ (signed : Bool) (checked : CoreMod.Checked) (x : S.Term) (c1 : Int) (t__5 : S.Ty) (t__7 : S.Ty) (c2 : Int) (t__10 : S.Ty),
  ((BitvecMod.Bitvec.checked_has signed checked) && (! (decide (c1 = (0 : Int))))) = true →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c1); let z2 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c2); ((BitvecMod.divisible z2 z1)) = true) →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c1); ¬((decide (z1 < (0 : Int)))) = true) →
  S.Refines (BitvecMod.Bitvec.leq.spec signed (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7) (BitvecMod.mk (.BitVec c2) t__10))
  (O.bitvec_leq signed x (O.bitvec_div signed (BitvecMod.mk (.BitVec c2) t__10) (BitvecMod.mk (.BitVec c1) t__5))) := by
  intros
  dsimp only at *
  cmp_lift
  cmp_halves

theorem cmp_leq_mc_b3 :
  ∀ {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [BitvecMod.Lang S] [KanonBool.Typed S] [CoreMod.Typed S] [BitvecMod.Typed S] (O : Ops S), O.Sound →
  ∀ (signed : Bool) (checked : CoreMod.Checked) (x : S.Term) (c1 : Int) (t__5 : S.Ty) (t__7 : S.Ty) (c2 : Int) (t__10 : S.Ty),
  ((BitvecMod.Bitvec.checked_has signed checked) && (! (decide (c1 = (0 : Int))))) = true →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c1); let z2 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c2); ¬((BitvecMod.divisible z2 z1)) = true) →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c1); ((decide (z1 < (0 : Int)))) = true) →
  (let z2 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c2); ((decide (z2 < (0 : Int)))) = true) →
  S.Refines (BitvecMod.Bitvec.leq.spec signed (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7) (BitvecMod.mk (.BitVec c2) t__10))
  (O.bitvec_lt signed (O.bitvec_div signed (BitvecMod.mk (.BitVec c2) t__10) (BitvecMod.mk (.BitVec c1) t__5)) x) := by
  intros
  dsimp only at *
  cmp_lift
  cmp_halves

theorem cmp_leq_mc_b4 :
  ∀ {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [BitvecMod.Lang S] [KanonBool.Typed S] [CoreMod.Typed S] [BitvecMod.Typed S] (O : Ops S), O.Sound →
  ∀ (signed : Bool) (checked : CoreMod.Checked) (x : S.Term) (c1 : Int) (t__5 : S.Ty) (t__7 : S.Ty) (c2 : Int) (t__10 : S.Ty),
  ((BitvecMod.Bitvec.checked_has signed checked) && (! (decide (c1 = (0 : Int))))) = true →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c1); let z2 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c2); ¬((BitvecMod.divisible z2 z1)) = true) →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c1); ((decide (z1 < (0 : Int)))) = true) →
  (let z2 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c2); ¬((decide (z2 < (0 : Int)))) = true) →
  S.Refines (BitvecMod.Bitvec.leq.spec signed (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7) (BitvecMod.mk (.BitVec c2) t__10))
  (O.bitvec_leq signed (O.bitvec_div signed (BitvecMod.mk (.BitVec c2) t__10) (BitvecMod.mk (.BitVec c1) t__5)) x) := by
  intros
  dsimp only at *
  cmp_lift
  cmp_halves

theorem cmp_leq_mc_b5 :
  ∀ {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [BitvecMod.Lang S] [KanonBool.Typed S] [CoreMod.Typed S] [BitvecMod.Typed S] (O : Ops S), O.Sound →
  ∀ (signed : Bool) (checked : CoreMod.Checked) (x : S.Term) (c1 : Int) (t__5 : S.Ty) (t__7 : S.Ty) (c2 : Int) (t__10 : S.Ty),
  ((BitvecMod.Bitvec.checked_has signed checked) && (! (decide (c1 = (0 : Int))))) = true →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c1); let z2 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c2); ¬((BitvecMod.divisible z2 z1)) = true) →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c1); ¬((decide (z1 < (0 : Int)))) = true) →
  (let z2 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c2); ((decide (z2 < (0 : Int)))) = true) →
  S.Refines (BitvecMod.Bitvec.leq.spec signed (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7) (BitvecMod.mk (.BitVec c2) t__10))
  (O.bitvec_lt signed x (O.bitvec_div signed (BitvecMod.mk (.BitVec c2) t__10) (BitvecMod.mk (.BitVec c1) t__5))) := by
  intros
  dsimp only at *
  cmp_lift
  cmp_halves

theorem cmp_leq_mc_b6 :
  ∀ {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [BitvecMod.Lang S] [KanonBool.Typed S] [CoreMod.Typed S] [BitvecMod.Typed S] (O : Ops S), O.Sound →
  ∀ (signed : Bool) (checked : CoreMod.Checked) (x : S.Term) (c1 : Int) (t__5 : S.Ty) (t__7 : S.Ty) (c2 : Int) (t__10 : S.Ty),
  ((BitvecMod.Bitvec.checked_has signed checked) && (! (decide (c1 = (0 : Int))))) = true →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c1); let z2 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c2); ¬((BitvecMod.divisible z2 z1)) = true) →
  (let z1 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c1); ¬((decide (z1 < (0 : Int)))) = true) →
  (let z2 := (BitvecMod.Bitvec.to_z signed (BitvecMod.Bitvec.size (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7)) c2); ¬((decide (z2 < (0 : Int)))) = true) →
  S.Refines (BitvecMod.Bitvec.leq.spec signed (BitvecMod.mk (.Mul checked x (BitvecMod.mk (.BitVec c1) t__5)) t__7) (BitvecMod.mk (.BitVec c2) t__10))
  (O.bitvec_leq signed x (O.bitvec_div signed (BitvecMod.mk (.BitVec c2) t__10) (BitvecMod.mk (.BitVec c1) t__5))) := by
  intros
  dsimp only at *
  cmp_lift
  cmp_halves

@[kanon_arm] theorem Bitvec.leq.r_mul_const.main.proof : Bitvec.leq.r_mul_const.main.Stmt := by
  intro S _ _ _ _ _ _ O hO signed checked x c1 t5 t7 c2 t10 hg
  dsimp only
  repeat' split
  all_goals first
    | exact cmp_leq_mc_b0 O hO signed checked x c1 t5 t7 c2 t10 hg ‹_› ‹_› ‹_›
    | exact cmp_leq_mc_b1 O hO signed checked x c1 t5 t7 c2 t10 hg ‹_› ‹_› ‹_›
    | exact cmp_leq_mc_b2 O hO signed checked x c1 t5 t7 c2 t10 hg ‹_› ‹_›
    | exact cmp_leq_mc_b3 O hO signed checked x c1 t5 t7 c2 t10 hg ‹_› ‹_› ‹_›
    | exact cmp_leq_mc_b4 O hO signed checked x c1 t5 t7 c2 t10 hg ‹_› ‹_› ‹_›
    | exact cmp_leq_mc_b5 O hO signed checked x c1 t5 t7 c2 t10 hg ‹_› ‹_› ‹_›
    | exact cmp_leq_mc_b6 O hO signed checked x c1 t5 t7 c2 t10 hg ‹_› ‹_› ‹_›

/-- The swapped arm of `mul_const`, from the main arm by the commutativity of `Mul`. -/
@[kanon_arm] theorem Bitvec.leq.r_mul_const.swap.proof : Bitvec.leq.r_mul_const.swap.Stmt := by
  intro S _ _ _ _ _ _ O hO signed ck c1 t5 x t7 c2 t10 hg
  have h1 : S.Refines (mk (.Mul ck (mk (.BitVec c1) t5) x) t7) (mk (.Mul ck x (mk (.BitVec c1) t5)) t7) :=
    cmp_mul_comm ..
  refine Kanon.Sem.Refines.trans ?_
    (Kanon.Sem.Refines.trans (Bitvec.leq.r_mul_const.main.proof O hO signed ck x c1 t5 t7 c2 t10 hg) ?_)
  · simp only [Bitvec.leq.spec]
    kanon_congr
  · simp only [Bitvec.size, ty_mk]
    exact Kanon.Sem.Refines.refl

@[kanon_arm] theorem Bitvec.leq.r_mul_mul.main.proof : Bitvec.leq.r_mul_mul.main.Stmt := by cmp_rule

@[kanon_arm] theorem Bitvec.leq.r_neg_l.main.proof : Bitvec.leq.r_neg_l.main.Stmt := by cmp_rule

@[kanon_arm] theorem Bitvec.leq.r_neg_r.main.proof : Bitvec.leq.r_neg_r.main.Stmt := by cmp_rule

@[kanon_arm] theorem Bitvec.leq.r_negs.main.proof : Bitvec.leq.r_negs.main.Stmt := by cmp_rule

@[kanon_arm] theorem Bitvec.leq.r_same.main.proof : Bitvec.leq.r_same.main.Stmt := by cmp_rule

@[kanon_arm] theorem Bitvec.leq.r_self_add_l.main.proof : Bitvec.leq.r_self_add_l.main.Stmt := by cmp_rule

@[kanon_arm] theorem Bitvec.leq.r_self_add_l.swap.proof : Bitvec.leq.r_self_add_l.swap.Stmt := by cmp_rule

@[kanon_arm] theorem Bitvec.leq.r_self_add_r.main.proof : Bitvec.leq.r_self_add_r.main.Stmt := by cmp_rule

@[kanon_arm] theorem Bitvec.leq.r_sub_const1.main.proof : Bitvec.leq.r_sub_const1.main.Stmt := by cmp_rule

@[kanon_arm] theorem Bitvec.leq.r_sub_const2.main.proof : Bitvec.leq.r_sub_const2.main.Stmt := by cmp_rule

@[kanon_arm] theorem Bitvec.leq.r_to_unsigned_l.main.proof : Bitvec.leq.r_to_unsigned_l.main.Stmt := by
  intro S _ _ _ _ _ _ O hO s v c t hg
  obtain rfl : s = true := by revert hg; cases s <;> simp
  clear hg
  simp only [kanon_body, Bool.false_eq_true, ite_false, ite_true]
  cmp_auto

@[kanon_arm] theorem Bitvec.leq.r_to_unsigned_r.main.proof : Bitvec.leq.r_to_unsigned_r.main.Stmt := by
  intro S _ _ _ _ _ _ O hO s v c t hg
  obtain rfl : s = true := by revert hg; cases s <;> simp
  clear hg
  simp only [kanon_body, Bool.false_eq_true, ite_false, ite_true]
  cmp_auto

@[kanon_arm] theorem Bitvec.leq.r_ub_l.main.proof : Bitvec.leq.r_ub_l.main.Stmt := by cmp_rule

@[kanon_arm] theorem Bitvec.leq.r_ub_r.main.proof : Bitvec.leq.r_ub_r.main.Stmt := by cmp_rule

@[kanon_arm] theorem Bitvec.leq.r_udiv_big.main.proof : Bitvec.leq.r_udiv_big.main.Stmt := by cmp_rule

end BitvecMod
