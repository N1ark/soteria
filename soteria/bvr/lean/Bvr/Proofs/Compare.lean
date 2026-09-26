import Bvr.Proofs.CompareLemmas

/-! Bit-vector comparisons (`bv_lt`, `bv_leq`). -/

namespace Bvr

open Classical CompareL

theorem bv_lt.r_lits.proof : bv_lt.r_lits.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_lits] at h
  split at h <;> simp at h
  subst h
  refine cmp_refines_lt (fun _ _ _ _ => ⟨of_bool_WT, of_bool_ty⟩)
    (fun ρ N n x y hN h1 h2 hn _ e1 e2 => ?_)
  obtain ⟨rfl, rfl, -⟩ := lit_val h1 e1
  simp only [eval_of_bool, size_eq, Term.ty_mk, size_of_ty_bitVector, lit_val' s h1 e1,
    lit_val' s h2 e2]

theorem bv_lt.r_same.proof : bv_lt.r_same.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_same, equal] at h
  by_cases hv : v1 = v2 <;> simp [hv] at h
  subst h hv
  refine cmp_refines_lt (fun _ _ _ _ => TBool_false) (fun ρ N n x y _ _ _ _ _ e1 e2 => ?_)
  rw [e1] at e2; cases e2; simp

theorem bv_lt.r_negs.proof : bv_lt.r_negs.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_negs] at h
  split at h <;> simp at h
  obtain ⟨rfl, rfl⟩ := h
  rename_i a _ b _
  refine cmp_refines_lt (fun N hN h1 h2 => TBool_O_lt hO hN (TB_neg_inv h2).2 (TB_neg_inv h1).2)
    (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  obtain ⟨xa, ea, ha, rfl⟩ := neg_inv e1
  obtain ⟨yb, eb, hb, rfl⟩ := neg_inv e2
  rw [eval_O_lt hO hN (TB_neg_inv h2).2 (TB_neg_inv h1).2 eb ea, bvz_neg (ha rfl), bvz_neg (hb rfl)]
  simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_lt.r_neg_l.proof : bv_lt.r_neg_l.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_neg_l] at h
  split at h <;> simp at h
  obtain ⟨⟨rfl, hc⟩, rfl⟩ := h
  rename_i a _ c _
  refine cmp_refines_lt (fun N hN h1 h2 => TBool_O_lt hO hN (TB_O_neg hO hN h2) (TB_neg_inv h1).2)
    (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  obtain ⟨xa, ea, ha, rfl⟩ := neg_inv e1
  obtain ⟨rfl, -⟩ := lit_val h2 e2
  have hc := of_decide_eq_false hc; rw [TB_mk_size h1, lit_val' true h2 e2] at hc
  rw [eval_O_lt hO hN (TB_O_neg hO hN h2) (TB_neg_inv h1).2 (eval_O_neg hO hN h2 e2 (by simp)) ea,
    bvz_neg (ha rfl), bvz_neg (ne_intMin_of_bvz hn0 hc)]
  simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_lt.r_neg_r.proof : bv_lt.r_neg_r.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_neg_r] at h
  split at h <;> simp at h
  obtain ⟨⟨rfl, hc⟩, rfl⟩ := h
  rename_i c _ a _
  refine cmp_refines_lt (fun N hN h1 h2 => TBool_O_lt hO hN (TB_neg_inv h2).2 (TB_O_neg hO hN h1))
    (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  obtain ⟨yb, eb, hb, rfl⟩ := neg_inv e2
  obtain ⟨rfl, -⟩ := lit_val h1 e1
  have hc := of_decide_eq_false hc; rw [TB_mk_size h1, lit_val' true h1 e1] at hc
  rw [eval_O_lt hO hN (TB_neg_inv h2).2 (TB_O_neg hO hN h1) eb (eval_O_neg hO hN h1 e1 (by simp)),
    bvz_neg (hb rfl), bvz_neg (ne_intMin_of_bvz hn0 hc)]
  simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_lt.r_const_add.proof : bv_lt.r_const_add.Stmt := by
  sorry

theorem bv_lt.r_add_const.proof : bv_lt.r_add_const.Stmt := by
  sorry

theorem bv_lt.r_self_add_r.proof : bv_lt.r_self_add_r.Stmt := by
  sorry

theorem bv_lt.r_self_add_l.proof : bv_lt.r_self_add_l.Stmt := by
  sorry

theorem bv_lt.r_add_add.proof : bv_lt.r_add_add.Stmt := by
  sorry

theorem bv_lt.r_one.proof : bv_lt.r_one.Stmt := by
  sorry

theorem bv_lt.r_of_bool.proof : bv_lt.r_of_bool.Stmt := by
  sorry

theorem bv_lt.r_ite_l.proof : bv_lt.r_ite_l.Stmt := by
  sorry

theorem bv_lt.r_ite_r.proof : bv_lt.r_ite_r.Stmt := by
  sorry

theorem bv_lt.r_lt_zero.proof : bv_lt.r_lt_zero.Stmt := by
  sorry

theorem bv_lt.r_max_l.proof : bv_lt.r_max_l.Stmt := by
  sorry

theorem bv_lt.r_min_r.proof : bv_lt.r_min_r.Stmt := by
  sorry

theorem bv_lt.r_min_l.proof : bv_lt.r_min_l.Stmt := by
  sorry

theorem bv_lt.r_max_r.proof : bv_lt.r_max_r.Stmt := by
  sorry

theorem bv_lt.r_const_mul.proof : bv_lt.r_const_mul.Stmt := by
  sorry

theorem bv_lt.r_mul_const.proof : bv_lt.r_mul_const.Stmt := by
  sorry

theorem bv_lt.r_mul_mul.proof : bv_lt.r_mul_mul.Stmt := by
  sorry

theorem bv_lt.r_const_sub1.proof : bv_lt.r_const_sub1.Stmt := by
  sorry

theorem bv_lt.r_const_sub2.proof : bv_lt.r_const_sub2.Stmt := by
  sorry

theorem bv_lt.r_sub_const1.proof : bv_lt.r_sub_const1.Stmt := by
  sorry

theorem bv_lt.r_sub_const2.proof : bv_lt.r_sub_const2.Stmt := by
  sorry

theorem bv_lt.r_ub_r.proof : bv_lt.r_ub_r.Stmt := by
  sorry

theorem bv_lt.r_ub_l.proof : bv_lt.r_ub_l.Stmt := by
  sorry

theorem bv_lt.r_to_unsigned_l.proof : bv_lt.r_to_unsigned_l.Stmt := by
  sorry

theorem bv_lt.r_to_unsigned_r.proof : bv_lt.r_to_unsigned_r.Stmt := by
  sorry

theorem bv_lt.r_default.proof : bv_lt.r_default.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_default, Option.some.injEq] at h
  subst h; exact Refines.refl

theorem bv_leq.r_same.proof : bv_leq.r_same.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_same, equal] at h
  by_cases hv : v1 = v2 <;> simp [hv] at h
  subst h hv
  refine cmp_refines_leq (fun _ _ _ _ => TBool_true) (fun ρ N n x y _ _ _ _ _ e1 e2 => ?_)
  rw [e1] at e2; cases e2; simp

theorem bv_leq.r_lits.proof : bv_leq.r_lits.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_lits] at h
  split at h <;> simp at h
  subst h
  refine cmp_refines_leq (fun _ _ _ _ => ⟨of_bool_WT, of_bool_ty⟩)
    (fun ρ N n x y hN h1 h2 hn _ e1 e2 => ?_)
  obtain ⟨rfl, rfl, -⟩ := lit_val h1 e1
  simp only [eval_of_bool, size_eq, Term.ty_mk, size_of_ty_bitVector, lit_val' s h1 e1,
    lit_val' s h2 e2]

theorem bv_leq.r_negs.proof : bv_leq.r_negs.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_negs] at h
  split at h <;> simp at h
  obtain ⟨rfl, rfl⟩ := h
  rename_i a _ b _
  refine cmp_refines_leq (fun N hN h1 h2 => TBool_O_leq hO hN (TB_neg_inv h2).2 (TB_neg_inv h1).2)
    (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  obtain ⟨xa, ea, ha, rfl⟩ := neg_inv e1
  obtain ⟨yb, eb, hb, rfl⟩ := neg_inv e2
  rw [eval_O_leq hO hN (TB_neg_inv h2).2 (TB_neg_inv h1).2 eb ea, bvz_neg (ha rfl), bvz_neg (hb rfl)]
  simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_leq.r_neg_l.proof : bv_leq.r_neg_l.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_neg_l] at h
  split at h <;> simp at h
  obtain ⟨⟨rfl, hc⟩, rfl⟩ := h
  rename_i a _ c _
  refine cmp_refines_leq (fun N hN h1 h2 => TBool_O_leq hO hN (TB_O_neg hO hN h2) (TB_neg_inv h1).2)
    (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  obtain ⟨xa, ea, ha, rfl⟩ := neg_inv e1
  obtain ⟨rfl, -⟩ := lit_val h2 e2
  have hc := of_decide_eq_false hc; rw [TB_mk_size h1, lit_val' true h2 e2] at hc
  rw [eval_O_leq hO hN (TB_O_neg hO hN h2) (TB_neg_inv h1).2 (eval_O_neg hO hN h2 e2 (by simp)) ea,
    bvz_neg (ha rfl), bvz_neg (ne_intMin_of_bvz hn0 hc)]
  simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_leq.r_neg_r.proof : bv_leq.r_neg_r.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_neg_r] at h
  split at h <;> simp at h
  obtain ⟨⟨rfl, hc⟩, rfl⟩ := h
  rename_i c _ a _
  refine cmp_refines_leq (fun N hN h1 h2 => TBool_O_leq hO hN (TB_neg_inv h2).2 (TB_O_neg hO hN h1))
    (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  obtain ⟨yb, eb, hb, rfl⟩ := neg_inv e2
  obtain ⟨rfl, -⟩ := lit_val h1 e1
  have hc := of_decide_eq_false hc; rw [TB_mk_size h1, lit_val' true h1 e1] at hc
  rw [eval_O_leq hO hN (TB_neg_inv h2).2 (TB_O_neg hO hN h1) eb (eval_O_neg hO hN h1 e1 (by simp)),
    bvz_neg (hb rfl), bvz_neg (ne_intMin_of_bvz hn0 hc)]
  simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_leq.r_const_add.proof : bv_leq.r_const_add.Stmt := by
  sorry

theorem bv_leq.r_add_const.proof : bv_leq.r_add_const.Stmt := by
  sorry

theorem bv_leq.r_add_add.proof : bv_leq.r_add_add.Stmt := by
  sorry

theorem bv_leq.r_self_add_r.proof : bv_leq.r_self_add_r.Stmt := by
  sorry

theorem bv_leq.r_self_add_l.proof : bv_leq.r_self_add_l.Stmt := by
  sorry

theorem bv_leq.r_min_l.proof : bv_leq.r_min_l.Stmt := by
  sorry

theorem bv_leq.r_max_r.proof : bv_leq.r_max_r.Stmt := by
  sorry

theorem bv_leq.r_const_mul.proof : bv_leq.r_const_mul.Stmt := by
  sorry

theorem bv_leq.r_mul_const.proof : bv_leq.r_mul_const.Stmt := by
  sorry

theorem bv_leq.r_mul_mul.proof : bv_leq.r_mul_mul.Stmt := by
  sorry

theorem bv_leq.r_udiv_big.proof : bv_leq.r_udiv_big.Stmt := by
  sorry

theorem bv_leq.r_ite_l.proof : bv_leq.r_ite_l.Stmt := by
  sorry

theorem bv_leq.r_ite_r.proof : bv_leq.r_ite_r.Stmt := by
  sorry

theorem bv_leq.r_const_sub1.proof : bv_leq.r_const_sub1.Stmt := by
  sorry

theorem bv_leq.r_const_sub2.proof : bv_leq.r_const_sub2.Stmt := by
  sorry

theorem bv_leq.r_sub_const1.proof : bv_leq.r_sub_const1.Stmt := by
  sorry

theorem bv_leq.r_sub_const2.proof : bv_leq.r_sub_const2.Stmt := by
  sorry

theorem bv_leq.r_ub_r.proof : bv_leq.r_ub_r.Stmt := by
  sorry

theorem bv_leq.r_ub_l.proof : bv_leq.r_ub_l.Stmt := by
  sorry

theorem bv_leq.r_to_unsigned_l.proof : bv_leq.r_to_unsigned_l.Stmt := by
  sorry

theorem bv_leq.r_to_unsigned_r.proof : bv_leq.r_to_unsigned_r.Stmt := by
  sorry

theorem bv_leq.r_default.proof : bv_leq.r_default.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_default, Option.some.injEq] at h
  subst h; exact Refines.refl

end Bvr
