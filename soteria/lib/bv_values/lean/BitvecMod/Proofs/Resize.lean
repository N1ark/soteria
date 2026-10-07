import BitvecMod.Proofs.ResizeLib
import BitvecMod.Proofs.IteLib
import BitvecMod.Statements.Comm
import BitvecMod.Statements.Bitvec.concat
import BitvecMod.Statements.Bitvec.div
import BitvecMod.Statements.Bitvec.extend_
import BitvecMod.Statements.Bitvec.extract
import BitvecMod.Statements.Bitvec.rem

/-!
# The arms of the shifts, resizings, divisions and remainders that the tactics do not prove
-/

namespace BitvecMod

open Classical Kanon

set_option linter.unusedSimpArgs false

attribute [kanon_tactic "rs_auto"] Bitvec.shl.spec Bitvec.lshr.spec Bitvec.ashr.spec
  Bitvec.extract.spec Bitvec.extend_.spec Bitvec.concat.spec Bitvec.div.spec Bitvec.rem.spec
  Bitvec.mod_.spec

/-! ## `mod_` -/

/-! ## `rem` -/

@[kanon_arm] theorem Bitvec.rem.r_add.main.proof : Bitvec.rem.r_add.main.Stmt := by
  rs_auto_sem
  all_goals exact (ResizeLib.umod_add_self (by simp_all)).symm

/-- `rem.r_add` with the sum swapped, from the main arm. -/
@[kanon_arm] theorem Bitvec.rem.r_add.swap.proof : Bitvec.rem.r_add.swap.Stmt := by
  intro S _ _ _ _ _ _ O hO signed ck r d t__4 t__6 d2 t__9 hnz hg
  refine Kanon.Sem.Refines.trans ?_
    (Bitvec.rem.r_add.main.proof O hO signed ck d t__4 r t__6 d2 t__9 hnz hg)
  have := Add.comm.proof ck r (mk (.BitVec d) t__4) t__6
  simp only [Bitvec.rem.spec, ty_mk]
  kanon_congr

@[kanon_arm] theorem Bitvec.rem.r_pow2.main.proof : Bitvec.rem.r_pow2.main.Stmt := by
  rs_auto_fwd
  all_goals first
    | exact ResizeLib.rem_pow2_eq _ (by omega) (by omega) (by assumption)
    | (have := ResizeLib.lt_of_two_pow_lt (k := rs_k) (by assumption)
       simp only [ResizeLib.rs_exists_pos_eq]
       (repeat' (apply And.intro)) <;> omega)

@[kanon_arm] theorem Bitvec.rem.r_rem_rem.main.proof : Bitvec.rem.r_rem_rem.main.Stmt := by
  rs_auto_sem
  all_goals first
    | exact ResizeLib.umod_umod_le_ofInt (by omega) (by omega) (by omega) (by omega)
    | exact ResizeLib.umod_umod_lt_ofInt (by omega) (by omega) (by omega) (by omega) (by assumption)
    | (rw [WT_mk] at kw; obtain ⟨-, kw, -⟩ := kw; rw [WT_mk] at kw; obtain ⟨-, -, kw⟩ := kw
       exact ResizeLib.nonzero_lit_of_wt (by omega) kw)

/-! ## `div` -/

@[kanon_arm] theorem Bitvec.div.r_div_div.main.proof : Bitvec.div.r_div_div.main.Stmt := by
  rs_auto_sem
  rs_div_pre
  all_goals first
    | exact ResizeLib.div_div_ofInt (by omega) (by omega) (by omega) (by omega)
    | exact ResizeLib.nonzero_mk_bv_mul (by omega) rfl (by omega) (by omega) (by omega) (by omega)
        (by omega) (by assumption)

@[kanon_arm] theorem Bitvec.div.r_zext.main.proof : Bitvec.div.r_zext.main.Stmt := by
  rs_auto_fwd
  all_goals first
    | (have hz := ResizeLib.ne_zero_of_nonzero_lit ρ (by assumption)
       simp (disch := omega) only [ResizeLib.msb_of_lit_pos] at *
       exact ResizeLib.zext_div_ofInt _ (by omega)
         (ResizeLib.lt_two_pow_log2_nat (by assumption) (by omega)))
    | (rw [WT_mk] at kw
       obtain ⟨-, k1, k2⟩ := kw
       rw [WT_mk] at k1 k2
       obtain ⟨⟨n, hn, hx, -, -⟩, -⟩ := k1
       obtain ⟨⟨⟨n', -, rfl⟩, hwf⟩, -⟩ := k2
       obtain ⟨hz0, -⟩ := hwf n' (.inl rfl)
       rw [hx, size_of_ty_TBitVector] at *
       exact ResizeLib.nonzero_masked_of hn (by assumption) hz0 (by assumption))

@[kanon_arm] theorem Bitvec.div.r_mul_div.main.proof : Bitvec.div.r_mul_div.main.Stmt := by
  rs_auto_sem
  rs_div_pre
  all_goals simp (disch := first | omega | assumption | simp_all) only [ResizeLib.mul_div_ovf,
    ResizeLib.mul_div_eq, Bool.and_false, Bool.or_false, Bool.false_eq_true, ↓reduceIte, ofBV_some]
  all_goals rfl

/-- `div.r_mul_div` with the product swapped, from the main arm. -/
@[kanon_arm] theorem Bitvec.div.r_mul_div.swap.proof : Bitvec.div.r_mul_div.swap.Stmt := by
  intro S _ _ _ _ _ _ O hO signed s2 x n t__5 t__7 d t__10 hnz hg
  have hm := Bitvec.div.r_mul_div.main.proof O hO signed s2 n t__5 x t__7 d t__10 hnz hg
  simp only [Bitvec.size, ty_mk] at hm ⊢
  refine Kanon.Sem.Refines.trans ?_ hm
  have := Mul.comm.proof ⟨s2, true⟩ x (mk (.BitVec n) t__5) t__7
  simp only [Bitvec.div.spec, ty_mk]
  kanon_congr

@[kanon_arm] theorem Bitvec.div.r_div_mul.main.proof : Bitvec.div.r_div_mul.main.Stmt := by
  rs_auto_sem
  rs_div_pre
  all_goals first
    | exact ResizeLib.div_mul_ofInt (by omega) (by omega) (by omega) (by assumption) (by simp_all)
    | exact ResizeLib.nonzero_mk_bv_udiv (by omega) rfl (by omega) (by omega) (by omega) (by omega)
        (by omega) (by assumption) (by assumption)

/-- `div.r_div_mul` with the product swapped, from the main arm. -/
@[kanon_arm] theorem Bitvec.div.r_div_mul.swap.proof : Bitvec.div.r_div_mul.swap.Stmt := by
  intro S _ _ _ _ _ _ O hO signed s2 x n t__5 t__7 d t__10 hnz hg
  have hm := Bitvec.div.r_div_mul.main.proof O hO signed s2 n t__5 x t__7 d t__10 hnz hg
  simp only [Bitvec.size, ty_mk] at hm ⊢
  refine Kanon.Sem.Refines.trans ?_ hm
  have := Mul.comm.proof ⟨s2, true⟩ x (mk (.BitVec n) t__5) t__7
  simp only [Bitvec.div.spec, ty_mk]
  kanon_congr

/-! ## `extract` -/

@[kanon_arm] theorem Bitvec.extract.r_ite.main.proof : Bitvec.extract.r_ite.main.Stmt := by
  bv_ite_arm

@[kanon_arm] theorem Bitvec.extract.r_add_const.main.proof :
    Bitvec.extract.r_add_const.main.Stmt := by
  rs_auto_sem
  all_goals exact ResizeLib.extract_add_lsb _ (by assumption) (by assumption) (by omega)

@[kanon_arm] theorem Bitvec.extract.r_mul_pow2.main.proof : Bitvec.extract.r_mul_pow2.main.Stmt := by
  rs_auto_sem
  all_goals exact ResizeLib.extract_mul_pow2 _ (by assumption) (by omega)

@[kanon_arm] theorem Bitvec.extract.r_urem.main.proof : Bitvec.extract.r_urem.main.Stmt := by
  rs_auto_sem
  all_goals first
    | exact ResizeLib.extract_umod_pow2 _ (by assumption) (by omega)
    | exact ResizeLib.nonzero_mk_bv (by omega) (ResizeLib.pos_masked_two_pow (by omega))

/-! ## `extend_` -/

@[kanon_arm] theorem Bitvec.extend_.r_ite.main.proof : Bitvec.extend_.r_ite.main.Stmt := by
  bv_ite_arm

/-! ## `concat` -/

/-- The concatenation of two conditionals on the same guard, as the conditional of the
concatenations of their branches: by the typing and values of the nodes, without `rs_auto`
(whose case splits on the values of the six atoms are slow). -/
@[kanon_arm] theorem Bitvec.concat.r_ites.main.proof : Bitvec.concat.r_ites.main.Stmt := by
  kanon_rule_lift
  refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ v _ _ e => ?_)
  · simp only [WT_mk, KanonBool.WT_mk, Node.wt, KanonBool.Node.wt, Node.All, KanonBool.Node.All,
      ty_mk, KanonBool.ty_mk] at w ⊢
    obtain ⟨⟨n, m, hn, hm, h1, h2, -⟩, ⟨⟨hb, hr1, e1⟩, wb, wl1, wr1⟩, ⟨-, hr2, e2⟩, -, wl2, wr2⟩ := w
    subst e1 e2
    simp only [hr1, hr2, h1, h2, hb, wb, wl1, wl2, wr1, wr2, sort, size_of_ty_TBitVector, true_and,
      and_true]
    exact ⟨⟨n, m, hn, hm, rfl, rfl, rfl⟩, ⟨n, m, hn, hm, rfl, rfl, rfl⟩⟩
  · simp only [ev_mk, KanonBool.ev_mk, Node.map, KanonBool.Node.map, Node.eval,
      KanonBool.Node.eval, KanonBool.pite] at e ⊢
    split
    · rename_i h; simpa only [h, ↓reduceIte] using e
    · rename_i h; simp only [h, ↓reduceIte] at e ⊢; split
      · rename_i h'; simpa only [h', ↓reduceIte] using e
      · rename_i h'; simp only [h', ↓reduceIte, withW_none, reduceCtorEq] at e

end BitvecMod
