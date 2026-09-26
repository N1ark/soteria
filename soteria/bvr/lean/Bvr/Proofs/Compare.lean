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
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_const_add] at h
  replace h := orElse_eq_some h
  rcases h with h | h <;> split at h <;> (try split at h) <;> simp at h <;> rename_i hc <;> subst h
  · refine Refines.ite_split (fun hlt => ?_)
      (fun _ => Refines.ite_split (fun _ => Refines.refl) (fun hov => ?_))
    · obtain ⟨rfl, hlt⟩ := hlt
      refine cmp_refines_lt (fun _ _ _ _ => TBool_true) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv false hc e2
      have := lit_val' false h1 e1; have := lit_val' false (TB_add_inv h2).2.1 ea
      have := bvz_false_range xa; have := bvz_false_range xb
      simp only [bv_to_z_false] at *
      simp; omega
    · simp at hov
      refine cmp_refines_lt (fun N hN h1 h2 =>
          TBool_O_lt hO hN (TB_O_sub hO hN h1 (TB_add_inv h2).2.1) (TB_add_inv h2).2.2)
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv s hc e2
      rsz h1 at hov
      rw [overflows_sub_false, lit_val' s h1 e1, lit_val' s (TB_add_inv h2).2.1 ea] at hov
      obtain ⟨r', er', hr'⟩ := eval_O_sub_rng (s := s) hO hN h1 (TB_add_inv h2).2.1 e1 ea hov.1 hov.2
      rw [eval_O_lt hO hN (TB_O_sub hO hN h1 (TB_add_inv h2).2.1) (TB_add_inv h2).2.2 er' eb, hr', hy]
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega
  · refine Refines.ite_split (fun hlt => ?_)
      (fun _ => Refines.ite_split (fun _ => Refines.refl) (fun hov => ?_))
    · obtain ⟨rfl, hlt⟩ := hlt
      refine cmp_refines_lt (fun _ _ _ _ => TBool_true) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv false hc e2
      have := lit_val' false h1 e1; have := lit_val' false (TB_add_inv h2).2.2 eb
      have := bvz_false_range xa; have := bvz_false_range xb
      simp only [bv_to_z_false] at *
      simp; omega
    · simp at hov
      refine cmp_refines_lt (fun N hN h1 h2 =>
          TBool_O_lt hO hN (TB_O_sub hO hN h1 (TB_add_inv h2).2.2) (TB_add_inv h2).2.1)
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv s hc e2
      rsz h1 at hov
      rw [overflows_sub_false, lit_val' s h1 e1, lit_val' s (TB_add_inv h2).2.2 eb] at hov
      obtain ⟨r', er', hr'⟩ := eval_O_sub_rng (s := s) hO hN h1 (TB_add_inv h2).2.2 e1 eb hov.1 hov.2
      rw [eval_O_lt hO hN (TB_O_sub hO hN h1 (TB_add_inv h2).2.2) (TB_add_inv h2).2.1 er' ea, hr', hy]
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_lt.r_add_const.proof : bv_lt.r_add_const.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_add_const] at h
  replace h := orElse_eq_some h
  rcases h with h | h <;> split at h <;> (try split at h) <;> simp at h <;> rename_i hc <;> subst h
  · refine Refines.ite_split (fun hlt => ?_)
      (fun _ => Refines.ite_split (fun _ => Refines.refl) (fun hov => ?_))
    · obtain ⟨rfl, hlt⟩ := hlt
      refine cmp_refines_lt (fun _ _ _ _ => TBool_false) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv false hc e1
      have := lit_val' false h2 e2; have := lit_val' false (TB_add_inv h1).2.1 ea
      have := bvz_false_range xa; have := bvz_false_range xb
      simp only [bv_to_z_false] at *
      simp; omega
    · simp at hov
      refine cmp_refines_lt (fun N hN h1 h2 =>
          TBool_O_lt hO hN (TB_add_inv h1).2.2 (TB_O_sub hO hN h2 (TB_add_inv h1).2.1))
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv s hc e1
      rsz h1 at hov
      rw [overflows_sub_false, lit_val' s h2 e2, lit_val' s (TB_add_inv h1).2.1 ea] at hov
      obtain ⟨r', er', hr'⟩ := eval_O_sub_rng (s := s) hO hN h2 (TB_add_inv h1).2.1 e2 ea hov.1 hov.2
      rw [eval_O_lt hO hN (TB_add_inv h1).2.2 (TB_O_sub hO hN h2 (TB_add_inv h1).2.1) eb er', hr', hy]
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega
  · refine Refines.ite_split (fun hlt => ?_)
      (fun _ => Refines.ite_split (fun _ => Refines.refl) (fun hov => ?_))
    · obtain ⟨rfl, hlt⟩ := hlt
      refine cmp_refines_lt (fun _ _ _ _ => TBool_false) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv false hc e1
      have := lit_val' false h2 e2; have := lit_val' false (TB_add_inv h1).2.2 eb
      have := bvz_false_range xa; have := bvz_false_range xb
      simp only [bv_to_z_false] at *
      simp; omega
    · simp at hov
      refine cmp_refines_lt (fun N hN h1 h2 =>
          TBool_O_lt hO hN (TB_add_inv h1).2.1 (TB_O_sub hO hN h2 (TB_add_inv h1).2.2))
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv s hc e1
      rsz h1 at hov
      rw [overflows_sub_false, lit_val' s h2 e2, lit_val' s (TB_add_inv h1).2.2 eb] at hov
      obtain ⟨r', er', hr'⟩ := eval_O_sub_rng (s := s) hO hN h2 (TB_add_inv h1).2.2 e2 eb hov.1 hov.2
      rw [eval_O_lt hO hN (TB_add_inv h1).2.1 (TB_O_sub hO hN h2 (TB_add_inv h1).2.2) ea er', hr', hy]
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_lt.r_self_add_r.proof : bv_lt.r_self_add_r.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_self_add_r] at h
  replace h := orElse_eq_some h
  rcases h with h | h <;> split at h <;> (try split at h) <;> simp at h <;>
    rename_i hc <;> simp [equal] at hc <;> obtain ⟨rfl, hc⟩ := hc <;> subst h
  · refine cmp_refines_lt (fun N hN h1 h2 => by
        rsz h1; exact TBool_O_lt hO hN (TB_zero hN) (TB_add_inv h2).2.2)
      (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv s hc e2
    cases eval_val_eq e1 ea
    rsz h1; rw [eval_O_lt hO hN (TB_zero hN) (TB_add_inv h2).2.2 (eval_zero hn0) eb, hy, bvz_zero]
    simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega
  · refine cmp_refines_lt (fun N hN h1 h2 => by
        rsz h1; exact TBool_O_lt hO hN (TB_zero hN) (TB_add_inv h2).2.1)
      (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv s hc e2
    cases eval_val_eq e1 eb
    rsz h1; rw [eval_O_lt hO hN (TB_zero hN) (TB_add_inv h2).2.1 (eval_zero hn0) ea, hy, bvz_zero]
    simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_lt.r_self_add_l.proof : bv_lt.r_self_add_l.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_self_add_l] at h
  replace h := orElse_eq_some h
  rcases h with h | h <;> split at h <;> (try split at h) <;> simp at h <;>
    rename_i hc <;> simp [equal] at hc <;> obtain ⟨rfl, hc⟩ := hc <;> subst h
  · refine cmp_refines_lt (fun N hN h1 h2 => by
        rsz h1; exact TBool_O_lt hO hN (TB_add_inv h1).2.2 (TB_zero hN))
      (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv s hc e1
    cases eval_val_eq e2 ea
    rsz h1; rw [eval_O_lt hO hN (TB_add_inv h1).2.2 (TB_zero hN) eb (eval_zero hn0), hy, bvz_zero]
    simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega
  · refine cmp_refines_lt (fun N hN h1 h2 => by
        rsz h1; exact TBool_O_lt hO hN (TB_add_inv h1).2.1 (TB_zero hN))
      (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv s hc e1
    cases eval_val_eq e2 eb
    rsz h1; rw [eval_O_lt hO hN (TB_add_inv h1).2.1 (TB_zero hN) ea (eval_zero hn0), hy, bvz_zero]
    simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_lt.r_add_add.proof : bv_lt.r_add_add.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_add_add] at h
  replace h := orElse_eq_some h
  rcases h with h | h <;> (try replace h := orElse_eq_some h) <;> (try rcases h with h | h) <;>
    (try replace h := orElse_eq_some h) <;> (try rcases h with h | h) <;>
    split at h <;> (try split at h) <;> simp at h <;> rename_i hc <;> rw [Bool.and_eq_true] at hc <;> obtain ⟨hcl, hcr⟩ := hc <;>
    subst h
  · refine Refines.ite_split (fun hk => ?_)
      (fun _ => Refines.ite_split (fun hk => ?_) (fun _ => Refines.refl))
    · refine cmp_refines_lt (fun N hN h1 h2 => TBool_O_lt hO hN
          (TB_O_add hO hN (TB_add_inv h1).2.2 (TB_O_sub hO hN (TB_add_inv h1).2.1 (TB_add_inv h2).2.1)) (TB_add_inv h2).2.2)
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_add_inv s hcl e1
      obtain ⟨ya, yb, fa, fb, hy', hr1', hr2'⟩ := eval_add_inv s hcr e2
      rw [const_keeps_iff] at hk
      rsz h1 at hk
      rw [lit_val' s (TB_add_inv h1).2.1 ea, lit_val' s (TB_add_inv h2).2.1 fa] at hk
      have := bvz_range hn0 s xa; have := bvz_range hn0 s xb
      have := bvz_range hn0 s ya; have := bvz_range hn0 s yb
      have := min_for_nonpos (N := n) s; have := max_for_nonneg hn0 s
      obtain ⟨d, ed, hd⟩ := eval_O_sub_rng (s := s) hO hN (TB_add_inv h1).2.1 (TB_add_inv h2).2.1 ea fa (by omega) (by omega)
      obtain ⟨t, et, ht⟩ := eval_O_add_rng (s := s) hO hN (TB_add_inv h1).2.2 (TB_O_sub hO hN (TB_add_inv h1).2.1 (TB_add_inv h2).2.1) eb ed
        (by omega) (by omega)
      rw [eval_O_lt hO hN (TB_O_add hO hN (TB_add_inv h1).2.2 (TB_O_sub hO hN (TB_add_inv h1).2.1 (TB_add_inv h2).2.1)) (TB_add_inv h2).2.2 et fb, ht, hd,
        hy, hy']
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega
    · refine cmp_refines_lt (fun N hN h1 h2 => TBool_O_lt hO hN (TB_add_inv h1).2.2
          (TB_O_add hO hN (TB_add_inv h2).2.2 (TB_O_sub hO hN (TB_add_inv h2).2.1 (TB_add_inv h1).2.1)))
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_add_inv s hcl e1
      obtain ⟨ya, yb, fa, fb, hy', hr1', hr2'⟩ := eval_add_inv s hcr e2
      rw [const_keeps_iff] at hk
      rsz h1 at hk
      rw [lit_val' s (TB_add_inv h1).2.1 ea, lit_val' s (TB_add_inv h2).2.1 fa] at hk
      have := bvz_range hn0 s xa; have := bvz_range hn0 s xb
      have := bvz_range hn0 s ya; have := bvz_range hn0 s yb
      have := min_for_nonpos (N := n) s; have := max_for_nonneg hn0 s
      obtain ⟨d, ed, hd⟩ := eval_O_sub_rng (s := s) hO hN (TB_add_inv h2).2.1 (TB_add_inv h1).2.1 fa ea (by omega) (by omega)
      obtain ⟨t, et, ht⟩ := eval_O_add_rng (s := s) hO hN (TB_add_inv h2).2.2 (TB_O_sub hO hN (TB_add_inv h2).2.1 (TB_add_inv h1).2.1) fb ed
        (by omega) (by omega)
      rw [eval_O_lt hO hN (TB_add_inv h1).2.2 (TB_O_add hO hN (TB_add_inv h2).2.2 (TB_O_sub hO hN (TB_add_inv h2).2.1 (TB_add_inv h1).2.1)) eb et, ht, hd,
        hy, hy']
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega
  · refine Refines.ite_split (fun hk => ?_)
      (fun _ => Refines.ite_split (fun hk => ?_) (fun _ => Refines.refl))
    · refine cmp_refines_lt (fun N hN h1 h2 => TBool_O_lt hO hN
          (TB_O_add hO hN (TB_add_inv h1).2.2 (TB_O_sub hO hN (TB_add_inv h1).2.1 (TB_add_inv h2).2.2)) (TB_add_inv h2).2.1)
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_add_inv s hcl e1
      obtain ⟨ya, yb, fa, fb, hy', hr1', hr2'⟩ := eval_add_inv s hcr e2
      rw [const_keeps_iff] at hk
      rsz h1 at hk
      rw [lit_val' s (TB_add_inv h1).2.1 ea, lit_val' s (TB_add_inv h2).2.2 fb] at hk
      have := bvz_range hn0 s xa; have := bvz_range hn0 s xb
      have := bvz_range hn0 s ya; have := bvz_range hn0 s yb
      have := min_for_nonpos (N := n) s; have := max_for_nonneg hn0 s
      obtain ⟨d, ed, hd⟩ := eval_O_sub_rng (s := s) hO hN (TB_add_inv h1).2.1 (TB_add_inv h2).2.2 ea fb (by omega) (by omega)
      obtain ⟨t, et, ht⟩ := eval_O_add_rng (s := s) hO hN (TB_add_inv h1).2.2 (TB_O_sub hO hN (TB_add_inv h1).2.1 (TB_add_inv h2).2.2) eb ed
        (by omega) (by omega)
      rw [eval_O_lt hO hN (TB_O_add hO hN (TB_add_inv h1).2.2 (TB_O_sub hO hN (TB_add_inv h1).2.1 (TB_add_inv h2).2.2)) (TB_add_inv h2).2.1 et fa, ht, hd,
        hy, hy']
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega
    · refine cmp_refines_lt (fun N hN h1 h2 => TBool_O_lt hO hN (TB_add_inv h1).2.2
          (TB_O_add hO hN (TB_add_inv h2).2.1 (TB_O_sub hO hN (TB_add_inv h2).2.2 (TB_add_inv h1).2.1)))
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_add_inv s hcl e1
      obtain ⟨ya, yb, fa, fb, hy', hr1', hr2'⟩ := eval_add_inv s hcr e2
      rw [const_keeps_iff] at hk
      rsz h1 at hk
      rw [lit_val' s (TB_add_inv h1).2.1 ea, lit_val' s (TB_add_inv h2).2.2 fb] at hk
      have := bvz_range hn0 s xa; have := bvz_range hn0 s xb
      have := bvz_range hn0 s ya; have := bvz_range hn0 s yb
      have := min_for_nonpos (N := n) s; have := max_for_nonneg hn0 s
      obtain ⟨d, ed, hd⟩ := eval_O_sub_rng (s := s) hO hN (TB_add_inv h2).2.2 (TB_add_inv h1).2.1 fb ea (by omega) (by omega)
      obtain ⟨t, et, ht⟩ := eval_O_add_rng (s := s) hO hN (TB_add_inv h2).2.1 (TB_O_sub hO hN (TB_add_inv h2).2.2 (TB_add_inv h1).2.1) fa ed
        (by omega) (by omega)
      rw [eval_O_lt hO hN (TB_add_inv h1).2.2 (TB_O_add hO hN (TB_add_inv h2).2.1 (TB_O_sub hO hN (TB_add_inv h2).2.2 (TB_add_inv h1).2.1)) eb et, ht, hd,
        hy, hy']
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega
  · refine Refines.ite_split (fun hk => ?_)
      (fun _ => Refines.ite_split (fun hk => ?_) (fun _ => Refines.refl))
    · refine cmp_refines_lt (fun N hN h1 h2 => TBool_O_lt hO hN
          (TB_O_add hO hN (TB_add_inv h1).2.1 (TB_O_sub hO hN (TB_add_inv h1).2.2 (TB_add_inv h2).2.1)) (TB_add_inv h2).2.2)
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_add_inv s hcl e1
      obtain ⟨ya, yb, fa, fb, hy', hr1', hr2'⟩ := eval_add_inv s hcr e2
      rw [const_keeps_iff] at hk
      rsz h1 at hk
      rw [lit_val' s (TB_add_inv h1).2.2 eb, lit_val' s (TB_add_inv h2).2.1 fa] at hk
      have := bvz_range hn0 s xa; have := bvz_range hn0 s xb
      have := bvz_range hn0 s ya; have := bvz_range hn0 s yb
      have := min_for_nonpos (N := n) s; have := max_for_nonneg hn0 s
      obtain ⟨d, ed, hd⟩ := eval_O_sub_rng (s := s) hO hN (TB_add_inv h1).2.2 (TB_add_inv h2).2.1 eb fa (by omega) (by omega)
      obtain ⟨t, et, ht⟩ := eval_O_add_rng (s := s) hO hN (TB_add_inv h1).2.1 (TB_O_sub hO hN (TB_add_inv h1).2.2 (TB_add_inv h2).2.1) ea ed
        (by omega) (by omega)
      rw [eval_O_lt hO hN (TB_O_add hO hN (TB_add_inv h1).2.1 (TB_O_sub hO hN (TB_add_inv h1).2.2 (TB_add_inv h2).2.1)) (TB_add_inv h2).2.2 et fb, ht, hd,
        hy, hy']
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega
    · refine cmp_refines_lt (fun N hN h1 h2 => TBool_O_lt hO hN (TB_add_inv h1).2.1
          (TB_O_add hO hN (TB_add_inv h2).2.2 (TB_O_sub hO hN (TB_add_inv h2).2.1 (TB_add_inv h1).2.2)))
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_add_inv s hcl e1
      obtain ⟨ya, yb, fa, fb, hy', hr1', hr2'⟩ := eval_add_inv s hcr e2
      rw [const_keeps_iff] at hk
      rsz h1 at hk
      rw [lit_val' s (TB_add_inv h1).2.2 eb, lit_val' s (TB_add_inv h2).2.1 fa] at hk
      have := bvz_range hn0 s xa; have := bvz_range hn0 s xb
      have := bvz_range hn0 s ya; have := bvz_range hn0 s yb
      have := min_for_nonpos (N := n) s; have := max_for_nonneg hn0 s
      obtain ⟨d, ed, hd⟩ := eval_O_sub_rng (s := s) hO hN (TB_add_inv h2).2.1 (TB_add_inv h1).2.2 fa eb (by omega) (by omega)
      obtain ⟨t, et, ht⟩ := eval_O_add_rng (s := s) hO hN (TB_add_inv h2).2.2 (TB_O_sub hO hN (TB_add_inv h2).2.1 (TB_add_inv h1).2.2) fb ed
        (by omega) (by omega)
      rw [eval_O_lt hO hN (TB_add_inv h1).2.1 (TB_O_add hO hN (TB_add_inv h2).2.2 (TB_O_sub hO hN (TB_add_inv h2).2.1 (TB_add_inv h1).2.2)) ea et, ht, hd,
        hy, hy']
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega
  · refine Refines.ite_split (fun hk => ?_)
      (fun _ => Refines.ite_split (fun hk => ?_) (fun _ => Refines.refl))
    · refine cmp_refines_lt (fun N hN h1 h2 => TBool_O_lt hO hN
          (TB_O_add hO hN (TB_add_inv h1).2.1 (TB_O_sub hO hN (TB_add_inv h1).2.2 (TB_add_inv h2).2.2)) (TB_add_inv h2).2.1)
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_add_inv s hcl e1
      obtain ⟨ya, yb, fa, fb, hy', hr1', hr2'⟩ := eval_add_inv s hcr e2
      rw [const_keeps_iff] at hk
      rsz h1 at hk
      rw [lit_val' s (TB_add_inv h1).2.2 eb, lit_val' s (TB_add_inv h2).2.2 fb] at hk
      have := bvz_range hn0 s xa; have := bvz_range hn0 s xb
      have := bvz_range hn0 s ya; have := bvz_range hn0 s yb
      have := min_for_nonpos (N := n) s; have := max_for_nonneg hn0 s
      obtain ⟨d, ed, hd⟩ := eval_O_sub_rng (s := s) hO hN (TB_add_inv h1).2.2 (TB_add_inv h2).2.2 eb fb (by omega) (by omega)
      obtain ⟨t, et, ht⟩ := eval_O_add_rng (s := s) hO hN (TB_add_inv h1).2.1 (TB_O_sub hO hN (TB_add_inv h1).2.2 (TB_add_inv h2).2.2) ea ed
        (by omega) (by omega)
      rw [eval_O_lt hO hN (TB_O_add hO hN (TB_add_inv h1).2.1 (TB_O_sub hO hN (TB_add_inv h1).2.2 (TB_add_inv h2).2.2)) (TB_add_inv h2).2.1 et fa, ht, hd,
        hy, hy']
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega
    · refine cmp_refines_lt (fun N hN h1 h2 => TBool_O_lt hO hN (TB_add_inv h1).2.1
          (TB_O_add hO hN (TB_add_inv h2).2.1 (TB_O_sub hO hN (TB_add_inv h2).2.2 (TB_add_inv h1).2.2)))
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_add_inv s hcl e1
      obtain ⟨ya, yb, fa, fb, hy', hr1', hr2'⟩ := eval_add_inv s hcr e2
      rw [const_keeps_iff] at hk
      rsz h1 at hk
      rw [lit_val' s (TB_add_inv h1).2.2 eb, lit_val' s (TB_add_inv h2).2.2 fb] at hk
      have := bvz_range hn0 s xa; have := bvz_range hn0 s xb
      have := bvz_range hn0 s ya; have := bvz_range hn0 s yb
      have := min_for_nonpos (N := n) s; have := max_for_nonneg hn0 s
      obtain ⟨d, ed, hd⟩ := eval_O_sub_rng (s := s) hO hN (TB_add_inv h2).2.2 (TB_add_inv h1).2.2 fb eb (by omega) (by omega)
      obtain ⟨t, et, ht⟩ := eval_O_add_rng (s := s) hO hN (TB_add_inv h2).2.1 (TB_O_sub hO hN (TB_add_inv h2).2.2 (TB_add_inv h1).2.2) fa ed
        (by omega) (by omega)
      rw [eval_O_lt hO hN (TB_add_inv h1).2.1 (TB_O_add hO hN (TB_add_inv h2).2.1 (TB_O_sub hO hN (TB_add_inv h2).2.2 (TB_add_inv h1).2.2)) ea et, ht, hd,
        hy, hy']
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_lt.r_one.proof : bv_lt.r_one.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_one] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; simp at hc; obtain ⟨rfl, rfl⟩ := hc; subst h
  refine cmp_refines_lt (fun N hN h1 h2 => by rsz h1; exact TBool_O_eq hO h1 (TB_zero hN))
    (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  subst hn
  have hy : (1 : Int) = bvz false y := lit_val' false h2 e2
  rsz h1
  rw [eval_O_eq hO h1.1 (TB_zero hN).1 (h1.2.trans (TB_zero hN).2.symm) e1 (eval_zero hn0)]
  simp only [Option.some.injEq, Val.bool.injEq, val_bv_eq]
  have := bvz_false_range x
  by_cases e : x = 0#n
  · subst e; simp; omega
  · have : bvz false x ≠ bvz false 0#n := fun h => e (bvz_inj.1 h)
    simp at this; simp [e]; omega

theorem bv_lt.r_of_bool.proof : bv_lt.r_of_bool.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_of_bool] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; simp at hc; subst hc h
  refine cmp_refines_lt (fun N hN h1 h2 => by
      obtain ⟨rfl, -, hb⟩ := TB_ofBool_inv h2
      exact TBool_O_and hO hb (TBool_O_eq hO h1 (TB_zero hN)))
    (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  subst hn
  obtain ⟨rfl, -, hb⟩ := TB_ofBool_inv h2
  obtain ⟨bb, eb, hy⟩ := eval_ofBool_eq_some e2
  simp at hy
  refine eval_O_and hO hb (TBool_O_eq hO h1 (TB_zero hN)) _ ?_
  rw [eb, eval_O_eq hO h1.1 (TB_zero hN).1 (h1.2.trans (TB_zero hN).2.symm) e1 (eval_zero hn0),
    pand_bool]
  have := bvz_false_range x
  simp only [Option.some.injEq, Val.bool.injEq, val_bv_eq]
  cases bb <;> simp at hy <;> subst hy
  · simp; omega
  · rw [bvz_false_one hn0]
    by_cases e : x = 0#n
    · subst e; simp
    · have : bvz false x ≠ bvz false 0#n := fun h => e (bvz_inj.1 h)
      simp at this; simp [e]; omega

theorem bv_lt.r_ite_l.proof : bv_lt.r_ite_l.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_ite_l] at h
  split at h <;> simp at h
  subst h
  refine cmp_refines_lt (fun N hN h1 h2 => TBool_O_ite hO (TB_ite_inv h1).1
      (TBool_O_lt hO hN (TB_ite_inv h1).2.1 h2) (TBool_O_lt hO hN (TB_ite_inv h1).2.2 h2))
    (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  obtain ⟨hb, hl, hr⟩ := TB_ite_inv h1
  refine eval_O_ite hO hb (TBool_O_lt hO hN hl h2) (TBool_O_lt hO hN hr h2) _ ?_
  rcases ite_inv e1 with ⟨eg, ex⟩ | ⟨eg, ex⟩ <;> rw [eg] <;> dsimp only
  · exact eval_O_lt hO hN hl h2 ex e2
  · exact eval_O_lt hO hN hr h2 ex e2

theorem bv_lt.r_ite_r.proof : bv_lt.r_ite_r.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_ite_r] at h
  split at h <;> simp at h
  subst h
  refine cmp_refines_lt (fun N hN h1 h2 => TBool_O_ite hO (TB_ite_inv h2).1
      (TBool_O_lt hO hN h1 (TB_ite_inv h2).2.1) (TBool_O_lt hO hN h1 (TB_ite_inv h2).2.2))
    (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  obtain ⟨hb, hl, hr⟩ := TB_ite_inv h2
  refine eval_O_ite hO hb (TBool_O_lt hO hN h1 hl) (TBool_O_lt hO hN h1 hr) _ ?_
  rcases ite_inv e2 with ⟨eg, ex⟩ | ⟨eg, ex⟩ <;> rw [eg] <;> dsimp only
  · exact eval_O_lt hO hN h1 hl e1 ex
  · exact eval_O_lt hO hN h1 hr e1 ex

theorem bv_lt.r_lt_zero.proof : bv_lt.r_lt_zero.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_lt_zero] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; simp at hc; obtain ⟨rfl, rfl, -⟩ := hc; subst h
  have H := fun N (hN : 0 < N) (h1 : TB v1 N) =>
    lt_zero_aux_sound hO (sizeOf v1 + 1) v1 (by omega) hN h1
  refine cmp_refines_lt (fun N hN h1 h2 => (H N hN h1).1)
    (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  rw [(H N hN h1).2 ρ n x e1]
  obtain ⟨-, -, -, -, -, rfl, -⟩ := lit_val h2 e2
  simp [bvz, BitVec.msb_eq_toInt]

theorem bv_lt.r_max_l.proof : bv_lt.r_max_l.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_max_l] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; subst h; have hc := of_decide_eq_true hc
  refine cmp_refines_lt (fun _ _ _ _ => TBool_false) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  obtain ⟨rfl, -⟩ := lit_val h1 e1
  rw [TB_size h1, lit_val' s h1 e1] at hc
  have := bvz_range hn0 s x; have := bvz_range hn0 s y
  simp only [eval_v_true, eval_v_false, Option.some.injEq, Val.bool.injEq]
  symm; simp only [decide_eq_true_eq, decide_eq_false_iff_not]; omega

theorem bv_lt.r_min_r.proof : bv_lt.r_min_r.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_min_r] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; subst h; have hc := of_decide_eq_true hc
  refine cmp_refines_lt (fun _ _ _ _ => TBool_false) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  obtain ⟨rfl, -⟩ := lit_val h2 e2
  rw [TB_size h1, lit_val' s h2 e2] at hc
  have := bvz_range hn0 s x; have := bvz_range hn0 s y
  simp only [eval_v_true, eval_v_false, Option.some.injEq, Val.bool.injEq]
  symm; simp only [decide_eq_true_eq, decide_eq_false_iff_not]; omega

theorem bv_lt.r_min_l.proof : bv_lt.r_min_l.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_min_l] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; subst h; have hc := of_decide_eq_true hc
  refine cmp_refines_lt (fun N hN h1 h2 => TBool_O_not hO (TBool_O_eq hO h1 h2))
    (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  obtain ⟨rfl, -⟩ := lit_val h1 e1
  rw [TB_size h1, lit_val' s h1 e1] at hc
  rw [eval_O_not hO (TBool_O_eq hO h1 h2) (eval_O_eq hO h1.1 h2.1 (h1.2.trans h2.2.symm) e1 e2)]
  have := bvz_range hn0 s x; have := bvz_range hn0 s y
  simp only [Option.some.injEq, Val.bool.injEq, val_bv_eq]
  by_cases e : x = y
  · subst e; simp
  · have : bvz s x ≠ bvz s y := fun h => e (bvz_inj.1 h)
    simp [e]; omega

theorem bv_lt.r_max_r.proof : bv_lt.r_max_r.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_max_r] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; subst h; have hc := of_decide_eq_true hc
  refine cmp_refines_lt (fun N hN h1 h2 => TBool_O_not hO (TBool_O_eq hO h1 h2))
    (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  obtain ⟨rfl, -⟩ := lit_val h2 e2
  rw [TB_size h1, lit_val' s h2 e2] at hc
  rw [eval_O_not hO (TBool_O_eq hO h1 h2) (eval_O_eq hO h1.1 h2.1 (h1.2.trans h2.2.symm) e1 e2)]
  have := bvz_range hn0 s x; have := bvz_range hn0 s y
  simp only [Option.some.injEq, Val.bool.injEq, val_bv_eq]
  by_cases e : x = y
  · subst e; simp
  · have : bvz s x ≠ bvz s y := fun h => e (bvz_inj.1 h)
    simp [e]; omega

-- UNSOUND: when c1 = 0. Take signed = true, 8 bits, v1 = BitVec 0 and v2 = Mul (checked_signed,
-- x, BitVec 0) with x ↦ 0#8. c1 = c2 = 0, so the rule returns bv_lt true (bv_div true v1 vc1) x.
-- The spec evaluates to 0 <s 0 = false, but bv_div true 0 0 is smtSDiv 0 0 = -1, and -1 <s 0 is
-- true.
theorem bv_lt.r_const_mul.proof : bv_lt.r_const_mul.Stmt := by
  sorry

-- UNSOUND: when c1 = 0. Take signed = false, 8 bits, v1 = Mul (checked_unsigned, x, BitVec 0)
-- and v2 = BitVec 0 with x ↦ 0#8. c1 = c2 = 0 (divisible), so the rule returns
-- bv_lt false x (bv_div false v2 vc1). The spec evaluates to 0 <u 0 = false, but
-- bv_div false 0 0 is smtUDiv 0 0 = 255, and 0 <u 255 is true.
theorem bv_lt.r_mul_const.proof : bv_lt.r_mul_const.Stmt := by
  sorry

-- UNSOUND: when a is negative (signed). Take signed = true, 8 bits, v1 = Mul (checked_signed,
-- a, x), v2 = Mul (checked_signed, a, y) with a = BitVec 255 (-1, so sure_neq a 0), x ↦ 1#8 and
-- y ↦ 2#8. Neither product overflows. The spec evaluates to (-1) <s (-2) = false, but the result
-- bv_lt true x y evaluates to 1 <s 2 = true.
theorem bv_lt.r_mul_mul.proof : bv_lt.r_mul_mul.Stmt := by
  sorry

theorem bv_lt.r_const_sub1.proof : bv_lt.r_const_sub1.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_const_sub1] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; subst h
  refine Refines.ite_split (fun hov => Refines.ite_split (fun hs => ?_) (fun _ => Refines.refl))
    (fun hov => ?_)
  · obtain rfl : s = false := by simpa using hs
    refine cmp_refines_lt (fun _ _ _ _ => TBool_false) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_sub_inv false hc e2
    rsz h1 at hov
    simp only [overflows_add, Bool.or_eq_true, decide_eq_true_eq] at hov
    rw [lit_val' false h1 e1, lit_val' false (TB_sub_inv h2).2.2 eb] at hov
    have := bvz_false_range xa; have := bvz_false_range xb
    have := bvz_false_range x; have := bvz_false_range y
    simp only [max_for_false, min_for_false] at *
    simp; omega
  · simp at hov
    refine cmp_refines_lt (fun N hN h1 h2 => TBool_O_lt hO hN (TB_O_add hO hN h1 (TB_sub_inv h2).2.2) (TB_sub_inv h2).2.1)
      (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_sub_inv s hc e2
    rsz h1 at hov
    rw [overflows_add_false, lit_val' s h1 e1, lit_val' s (TB_sub_inv h2).2.2 eb] at hov
    obtain ⟨r', er', hr'⟩ := eval_O_add_rng (s := s) hO hN h1 (TB_sub_inv h2).2.2 e1 eb hov.1 hov.2
    rw [eval_O_lt hO hN (TB_O_add hO hN h1 (TB_sub_inv h2).2.2) (TB_sub_inv h2).2.1 er' ea, hr', hy]
    simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_lt.r_const_sub2.proof : bv_lt.r_const_sub2.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_const_sub2] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; subst h
  refine Refines.ite_split (fun hov => Refines.ite_split (fun hs => ?_) (fun _ => Refines.refl))
    (fun hov => ?_)
  · obtain rfl : s = false := by simpa using hs
    refine cmp_refines_lt (fun _ _ _ _ => TBool_false) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_sub_inv false hc e2
    rsz h1 at hov
    simp only [overflows_sub, Bool.or_eq_true, decide_eq_true_eq] at hov
    rw [lit_val' false (TB_sub_inv h2).2.1 ea, lit_val' false h1 e1] at hov
    have := bvz_false_range xa; have := bvz_false_range xb
    have := bvz_false_range x; have := bvz_false_range y
    simp only [max_for_false, min_for_false] at *
    simp; omega
  · simp at hov
    refine cmp_refines_lt (fun N hN h1 h2 => TBool_O_lt hO hN (TB_sub_inv h2).2.2 (TB_O_sub hO hN (TB_sub_inv h2).2.1 h1))
      (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_sub_inv s hc e2
    rsz h1 at hov
    rw [overflows_sub_false, lit_val' s (TB_sub_inv h2).2.1 ea, lit_val' s h1 e1] at hov
    obtain ⟨r', er', hr'⟩ := eval_O_sub_rng (s := s) hO hN (TB_sub_inv h2).2.1 h1 ea e1 hov.1 hov.2
    rw [eval_O_lt hO hN (TB_sub_inv h2).2.2 (TB_O_sub hO hN (TB_sub_inv h2).2.1 h1) eb er', hr', hy]
    simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_lt.r_sub_const1.proof : bv_lt.r_sub_const1.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_sub_const1] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; subst h
  refine Refines.ite_split (fun hov => Refines.ite_split (fun hs => ?_) (fun _ => Refines.refl))
    (fun hov => ?_)
  · obtain rfl : s = false := by simpa using hs
    refine cmp_refines_lt (fun _ _ _ _ => TBool_true) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_sub_inv false hc e1
    rsz h1 at hov
    simp only [overflows_add, Bool.or_eq_true, decide_eq_true_eq] at hov
    rw [lit_val' false h2 e2, lit_val' false (TB_sub_inv h1).2.2 eb] at hov
    have := bvz_false_range xa; have := bvz_false_range xb
    have := bvz_false_range x; have := bvz_false_range y
    simp only [max_for_false, min_for_false] at *
    simp; omega
  · simp at hov
    refine cmp_refines_lt (fun N hN h1 h2 => TBool_O_lt hO hN (TB_sub_inv h1).2.1 (TB_O_add hO hN h2 (TB_sub_inv h1).2.2))
      (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_sub_inv s hc e1
    rsz h1 at hov
    rw [overflows_add_false, lit_val' s h2 e2, lit_val' s (TB_sub_inv h1).2.2 eb] at hov
    obtain ⟨r', er', hr'⟩ := eval_O_add_rng (s := s) hO hN h2 (TB_sub_inv h1).2.2 e2 eb hov.1 hov.2
    rw [eval_O_lt hO hN (TB_sub_inv h1).2.1 (TB_O_add hO hN h2 (TB_sub_inv h1).2.2) ea er', hr', hy]
    simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_lt.r_sub_const2.proof : bv_lt.r_sub_const2.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_sub_const2] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; subst h
  refine Refines.ite_split (fun hov => Refines.ite_split (fun hs => ?_) (fun _ => Refines.refl))
    (fun hov => ?_)
  · obtain rfl : s = false := by simpa using hs
    refine cmp_refines_lt (fun _ _ _ _ => TBool_true) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_sub_inv false hc e1
    rsz h1 at hov
    simp only [overflows_sub, Bool.or_eq_true, decide_eq_true_eq] at hov
    rw [lit_val' false (TB_sub_inv h1).2.1 ea, lit_val' false h2 e2] at hov
    have := bvz_false_range xa; have := bvz_false_range xb
    have := bvz_false_range x; have := bvz_false_range y
    simp only [max_for_false, min_for_false] at *
    simp; omega
  · simp at hov
    refine cmp_refines_lt (fun N hN h1 h2 => TBool_O_lt hO hN (TB_O_sub hO hN (TB_sub_inv h1).2.1 h2) (TB_sub_inv h1).2.2)
      (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_sub_inv s hc e1
    rsz h1 at hov
    rw [overflows_sub_false, lit_val' s (TB_sub_inv h1).2.1 ea, lit_val' s h2 e2] at hov
    obtain ⟨r', er', hr'⟩ := eval_O_sub_rng (s := s) hO hN (TB_sub_inv h1).2.1 h2 ea e2 hov.1 hov.2
    rw [eval_O_lt hO hN (TB_O_sub hO hN (TB_sub_inv h1).2.1 h2) (TB_sub_inv h1).2.2 er' eb, hr', hy]
    simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_lt.r_ub_r.proof : bv_lt.r_ub_r.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_ub_r] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; simp at hc; obtain ⟨rfl, hc⟩ := hc; subst h
  refine cmp_refines_lt (fun _ _ _ _ => TBool_true) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  have := le_unsigned_ub h1 e1; have := lit_val' false h2 e2
  simp only [bv_to_z_false] at *
  simp; omega

theorem bv_lt.r_ub_l.proof : bv_lt.r_ub_l.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_ub_l] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; simp at hc; obtain ⟨rfl, hc⟩ := hc; subst h
  refine cmp_refines_lt (fun _ _ _ _ => TBool_false) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  have := le_unsigned_ub h2 e2; have := lit_val' false h1 e1
  simp only [bv_to_z_false] at *
  simp; omega

theorem bv_lt.r_to_unsigned_l.proof : bv_lt.r_to_unsigned_l.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_to_unsigned_l] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; simp at hc; obtain ⟨rfl, -⟩ := hc; subst h
  exact signed_to_unsigned_left hO false _ _ v2

theorem bv_lt.r_to_unsigned_r.proof : bv_lt.r_to_unsigned_r.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_lt.r_to_unsigned_r] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; simp at hc; obtain ⟨rfl, -⟩ := hc; subst h
  exact signed_to_unsigned_right hO false _ _ v1

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
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_const_add] at h
  replace h := orElse_eq_some h
  rcases h with h | h <;> split at h <;> (try split at h) <;> simp at h <;> rename_i hc <;> subst h
  · refine Refines.ite_split (fun hlt => ?_)
      (fun _ => Refines.ite_split (fun _ => Refines.refl) (fun hov => ?_))
    · obtain ⟨rfl, hlt⟩ := hlt
      refine cmp_refines_leq (fun _ _ _ _ => TBool_true) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv false hc e2
      have := lit_val' false h1 e1; have := lit_val' false (TB_add_inv h2).2.1 ea
      have := bvz_false_range xa; have := bvz_false_range xb
      simp only [bv_to_z_false] at *
      simp; omega
    · simp at hov
      refine cmp_refines_leq (fun N hN h1 h2 =>
          TBool_O_leq hO hN (TB_O_sub hO hN h1 (TB_add_inv h2).2.1) (TB_add_inv h2).2.2)
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv s hc e2
      rsz h1 at hov
      rw [overflows_sub_false, lit_val' s h1 e1, lit_val' s (TB_add_inv h2).2.1 ea] at hov
      obtain ⟨r', er', hr'⟩ := eval_O_sub_rng (s := s) hO hN h1 (TB_add_inv h2).2.1 e1 ea hov.1 hov.2
      rw [eval_O_leq hO hN (TB_O_sub hO hN h1 (TB_add_inv h2).2.1) (TB_add_inv h2).2.2 er' eb, hr', hy]
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega
  · refine Refines.ite_split (fun hlt => ?_)
      (fun _ => Refines.ite_split (fun _ => Refines.refl) (fun hov => ?_))
    · obtain ⟨rfl, hlt⟩ := hlt
      refine cmp_refines_leq (fun _ _ _ _ => TBool_true) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv false hc e2
      have := lit_val' false h1 e1; have := lit_val' false (TB_add_inv h2).2.2 eb
      have := bvz_false_range xa; have := bvz_false_range xb
      simp only [bv_to_z_false] at *
      simp; omega
    · simp at hov
      refine cmp_refines_leq (fun N hN h1 h2 =>
          TBool_O_leq hO hN (TB_O_sub hO hN h1 (TB_add_inv h2).2.2) (TB_add_inv h2).2.1)
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv s hc e2
      rsz h1 at hov
      rw [overflows_sub_false, lit_val' s h1 e1, lit_val' s (TB_add_inv h2).2.2 eb] at hov
      obtain ⟨r', er', hr'⟩ := eval_O_sub_rng (s := s) hO hN h1 (TB_add_inv h2).2.2 e1 eb hov.1 hov.2
      rw [eval_O_leq hO hN (TB_O_sub hO hN h1 (TB_add_inv h2).2.2) (TB_add_inv h2).2.1 er' ea, hr', hy]
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_leq.r_add_const.proof : bv_leq.r_add_const.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_add_const] at h
  replace h := orElse_eq_some h
  rcases h with h | h <;> split at h <;> (try split at h) <;> simp at h <;> rename_i hc <;> subst h
  · refine Refines.ite_split (fun hlt => ?_)
      (fun _ => Refines.ite_split (fun _ => Refines.refl) (fun hov => ?_))
    · obtain ⟨rfl, hlt⟩ := hlt
      refine cmp_refines_leq (fun _ _ _ _ => TBool_false) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv false hc e1
      have := lit_val' false h2 e2; have := lit_val' false (TB_add_inv h1).2.1 ea
      have := bvz_false_range xa; have := bvz_false_range xb
      simp only [bv_to_z_false] at *
      simp; omega
    · simp at hov
      refine cmp_refines_leq (fun N hN h1 h2 =>
          TBool_O_leq hO hN (TB_add_inv h1).2.2 (TB_O_sub hO hN h2 (TB_add_inv h1).2.1))
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv s hc e1
      rsz h1 at hov
      rw [overflows_sub_false, lit_val' s h2 e2, lit_val' s (TB_add_inv h1).2.1 ea] at hov
      obtain ⟨r', er', hr'⟩ := eval_O_sub_rng (s := s) hO hN h2 (TB_add_inv h1).2.1 e2 ea hov.1 hov.2
      rw [eval_O_leq hO hN (TB_add_inv h1).2.2 (TB_O_sub hO hN h2 (TB_add_inv h1).2.1) eb er', hr', hy]
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega
  · refine Refines.ite_split (fun hlt => ?_)
      (fun _ => Refines.ite_split (fun _ => Refines.refl) (fun hov => ?_))
    · obtain ⟨rfl, hlt⟩ := hlt
      refine cmp_refines_leq (fun _ _ _ _ => TBool_false) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv false hc e1
      have := lit_val' false h2 e2; have := lit_val' false (TB_add_inv h1).2.2 eb
      have := bvz_false_range xa; have := bvz_false_range xb
      simp only [bv_to_z_false] at *
      simp; omega
    · simp at hov
      refine cmp_refines_leq (fun N hN h1 h2 =>
          TBool_O_leq hO hN (TB_add_inv h1).2.1 (TB_O_sub hO hN h2 (TB_add_inv h1).2.2))
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv s hc e1
      rsz h1 at hov
      rw [overflows_sub_false, lit_val' s h2 e2, lit_val' s (TB_add_inv h1).2.2 eb] at hov
      obtain ⟨r', er', hr'⟩ := eval_O_sub_rng (s := s) hO hN h2 (TB_add_inv h1).2.2 e2 eb hov.1 hov.2
      rw [eval_O_leq hO hN (TB_add_inv h1).2.1 (TB_O_sub hO hN h2 (TB_add_inv h1).2.2) ea er', hr', hy]
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_leq.r_add_add.proof : bv_leq.r_add_add.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_add_add] at h
  replace h := orElse_eq_some h
  rcases h with h | h <;> (try replace h := orElse_eq_some h) <;> (try rcases h with h | h) <;>
    (try replace h := orElse_eq_some h) <;> (try rcases h with h | h) <;>
    split at h <;> (try split at h) <;> simp at h <;> rename_i hc <;> rw [Bool.and_eq_true] at hc <;> obtain ⟨hcl, hcr⟩ := hc <;>
    subst h
  · refine Refines.ite_split (fun hk => ?_)
      (fun _ => Refines.ite_split (fun hk => ?_) (fun _ => Refines.refl))
    · refine cmp_refines_leq (fun N hN h1 h2 => TBool_O_leq hO hN
          (TB_O_add hO hN (TB_add_inv h1).2.2 (TB_O_sub hO hN (TB_add_inv h1).2.1 (TB_add_inv h2).2.1)) (TB_add_inv h2).2.2)
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_add_inv s hcl e1
      obtain ⟨ya, yb, fa, fb, hy', hr1', hr2'⟩ := eval_add_inv s hcr e2
      rw [const_keeps_iff] at hk
      rsz h1 at hk
      rw [lit_val' s (TB_add_inv h1).2.1 ea, lit_val' s (TB_add_inv h2).2.1 fa] at hk
      have := bvz_range hn0 s xa; have := bvz_range hn0 s xb
      have := bvz_range hn0 s ya; have := bvz_range hn0 s yb
      have := min_for_nonpos (N := n) s; have := max_for_nonneg hn0 s
      obtain ⟨d, ed, hd⟩ := eval_O_sub_rng (s := s) hO hN (TB_add_inv h1).2.1 (TB_add_inv h2).2.1 ea fa (by omega) (by omega)
      obtain ⟨t, et, ht⟩ := eval_O_add_rng (s := s) hO hN (TB_add_inv h1).2.2 (TB_O_sub hO hN (TB_add_inv h1).2.1 (TB_add_inv h2).2.1) eb ed
        (by omega) (by omega)
      rw [eval_O_leq hO hN (TB_O_add hO hN (TB_add_inv h1).2.2 (TB_O_sub hO hN (TB_add_inv h1).2.1 (TB_add_inv h2).2.1)) (TB_add_inv h2).2.2 et fb, ht, hd,
        hy, hy']
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega
    · refine cmp_refines_leq (fun N hN h1 h2 => TBool_O_leq hO hN (TB_add_inv h1).2.2
          (TB_O_add hO hN (TB_add_inv h2).2.2 (TB_O_sub hO hN (TB_add_inv h2).2.1 (TB_add_inv h1).2.1)))
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_add_inv s hcl e1
      obtain ⟨ya, yb, fa, fb, hy', hr1', hr2'⟩ := eval_add_inv s hcr e2
      rw [const_keeps_iff] at hk
      rsz h1 at hk
      rw [lit_val' s (TB_add_inv h1).2.1 ea, lit_val' s (TB_add_inv h2).2.1 fa] at hk
      have := bvz_range hn0 s xa; have := bvz_range hn0 s xb
      have := bvz_range hn0 s ya; have := bvz_range hn0 s yb
      have := min_for_nonpos (N := n) s; have := max_for_nonneg hn0 s
      obtain ⟨d, ed, hd⟩ := eval_O_sub_rng (s := s) hO hN (TB_add_inv h2).2.1 (TB_add_inv h1).2.1 fa ea (by omega) (by omega)
      obtain ⟨t, et, ht⟩ := eval_O_add_rng (s := s) hO hN (TB_add_inv h2).2.2 (TB_O_sub hO hN (TB_add_inv h2).2.1 (TB_add_inv h1).2.1) fb ed
        (by omega) (by omega)
      rw [eval_O_leq hO hN (TB_add_inv h1).2.2 (TB_O_add hO hN (TB_add_inv h2).2.2 (TB_O_sub hO hN (TB_add_inv h2).2.1 (TB_add_inv h1).2.1)) eb et, ht, hd,
        hy, hy']
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega
  · refine Refines.ite_split (fun hk => ?_)
      (fun _ => Refines.ite_split (fun hk => ?_) (fun _ => Refines.refl))
    · refine cmp_refines_leq (fun N hN h1 h2 => TBool_O_leq hO hN
          (TB_O_add hO hN (TB_add_inv h1).2.2 (TB_O_sub hO hN (TB_add_inv h1).2.1 (TB_add_inv h2).2.2)) (TB_add_inv h2).2.1)
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_add_inv s hcl e1
      obtain ⟨ya, yb, fa, fb, hy', hr1', hr2'⟩ := eval_add_inv s hcr e2
      rw [const_keeps_iff] at hk
      rsz h1 at hk
      rw [lit_val' s (TB_add_inv h1).2.1 ea, lit_val' s (TB_add_inv h2).2.2 fb] at hk
      have := bvz_range hn0 s xa; have := bvz_range hn0 s xb
      have := bvz_range hn0 s ya; have := bvz_range hn0 s yb
      have := min_for_nonpos (N := n) s; have := max_for_nonneg hn0 s
      obtain ⟨d, ed, hd⟩ := eval_O_sub_rng (s := s) hO hN (TB_add_inv h1).2.1 (TB_add_inv h2).2.2 ea fb (by omega) (by omega)
      obtain ⟨t, et, ht⟩ := eval_O_add_rng (s := s) hO hN (TB_add_inv h1).2.2 (TB_O_sub hO hN (TB_add_inv h1).2.1 (TB_add_inv h2).2.2) eb ed
        (by omega) (by omega)
      rw [eval_O_leq hO hN (TB_O_add hO hN (TB_add_inv h1).2.2 (TB_O_sub hO hN (TB_add_inv h1).2.1 (TB_add_inv h2).2.2)) (TB_add_inv h2).2.1 et fa, ht, hd,
        hy, hy']
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega
    · refine cmp_refines_leq (fun N hN h1 h2 => TBool_O_leq hO hN (TB_add_inv h1).2.2
          (TB_O_add hO hN (TB_add_inv h2).2.1 (TB_O_sub hO hN (TB_add_inv h2).2.2 (TB_add_inv h1).2.1)))
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_add_inv s hcl e1
      obtain ⟨ya, yb, fa, fb, hy', hr1', hr2'⟩ := eval_add_inv s hcr e2
      rw [const_keeps_iff] at hk
      rsz h1 at hk
      rw [lit_val' s (TB_add_inv h1).2.1 ea, lit_val' s (TB_add_inv h2).2.2 fb] at hk
      have := bvz_range hn0 s xa; have := bvz_range hn0 s xb
      have := bvz_range hn0 s ya; have := bvz_range hn0 s yb
      have := min_for_nonpos (N := n) s; have := max_for_nonneg hn0 s
      obtain ⟨d, ed, hd⟩ := eval_O_sub_rng (s := s) hO hN (TB_add_inv h2).2.2 (TB_add_inv h1).2.1 fb ea (by omega) (by omega)
      obtain ⟨t, et, ht⟩ := eval_O_add_rng (s := s) hO hN (TB_add_inv h2).2.1 (TB_O_sub hO hN (TB_add_inv h2).2.2 (TB_add_inv h1).2.1) fa ed
        (by omega) (by omega)
      rw [eval_O_leq hO hN (TB_add_inv h1).2.2 (TB_O_add hO hN (TB_add_inv h2).2.1 (TB_O_sub hO hN (TB_add_inv h2).2.2 (TB_add_inv h1).2.1)) eb et, ht, hd,
        hy, hy']
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega
  · refine Refines.ite_split (fun hk => ?_)
      (fun _ => Refines.ite_split (fun hk => ?_) (fun _ => Refines.refl))
    · refine cmp_refines_leq (fun N hN h1 h2 => TBool_O_leq hO hN
          (TB_O_add hO hN (TB_add_inv h1).2.1 (TB_O_sub hO hN (TB_add_inv h1).2.2 (TB_add_inv h2).2.1)) (TB_add_inv h2).2.2)
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_add_inv s hcl e1
      obtain ⟨ya, yb, fa, fb, hy', hr1', hr2'⟩ := eval_add_inv s hcr e2
      rw [const_keeps_iff] at hk
      rsz h1 at hk
      rw [lit_val' s (TB_add_inv h1).2.2 eb, lit_val' s (TB_add_inv h2).2.1 fa] at hk
      have := bvz_range hn0 s xa; have := bvz_range hn0 s xb
      have := bvz_range hn0 s ya; have := bvz_range hn0 s yb
      have := min_for_nonpos (N := n) s; have := max_for_nonneg hn0 s
      obtain ⟨d, ed, hd⟩ := eval_O_sub_rng (s := s) hO hN (TB_add_inv h1).2.2 (TB_add_inv h2).2.1 eb fa (by omega) (by omega)
      obtain ⟨t, et, ht⟩ := eval_O_add_rng (s := s) hO hN (TB_add_inv h1).2.1 (TB_O_sub hO hN (TB_add_inv h1).2.2 (TB_add_inv h2).2.1) ea ed
        (by omega) (by omega)
      rw [eval_O_leq hO hN (TB_O_add hO hN (TB_add_inv h1).2.1 (TB_O_sub hO hN (TB_add_inv h1).2.2 (TB_add_inv h2).2.1)) (TB_add_inv h2).2.2 et fb, ht, hd,
        hy, hy']
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega
    · refine cmp_refines_leq (fun N hN h1 h2 => TBool_O_leq hO hN (TB_add_inv h1).2.1
          (TB_O_add hO hN (TB_add_inv h2).2.2 (TB_O_sub hO hN (TB_add_inv h2).2.1 (TB_add_inv h1).2.2)))
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_add_inv s hcl e1
      obtain ⟨ya, yb, fa, fb, hy', hr1', hr2'⟩ := eval_add_inv s hcr e2
      rw [const_keeps_iff] at hk
      rsz h1 at hk
      rw [lit_val' s (TB_add_inv h1).2.2 eb, lit_val' s (TB_add_inv h2).2.1 fa] at hk
      have := bvz_range hn0 s xa; have := bvz_range hn0 s xb
      have := bvz_range hn0 s ya; have := bvz_range hn0 s yb
      have := min_for_nonpos (N := n) s; have := max_for_nonneg hn0 s
      obtain ⟨d, ed, hd⟩ := eval_O_sub_rng (s := s) hO hN (TB_add_inv h2).2.1 (TB_add_inv h1).2.2 fa eb (by omega) (by omega)
      obtain ⟨t, et, ht⟩ := eval_O_add_rng (s := s) hO hN (TB_add_inv h2).2.2 (TB_O_sub hO hN (TB_add_inv h2).2.1 (TB_add_inv h1).2.2) fb ed
        (by omega) (by omega)
      rw [eval_O_leq hO hN (TB_add_inv h1).2.1 (TB_O_add hO hN (TB_add_inv h2).2.2 (TB_O_sub hO hN (TB_add_inv h2).2.1 (TB_add_inv h1).2.2)) ea et, ht, hd,
        hy, hy']
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega
  · refine Refines.ite_split (fun hk => ?_)
      (fun _ => Refines.ite_split (fun hk => ?_) (fun _ => Refines.refl))
    · refine cmp_refines_leq (fun N hN h1 h2 => TBool_O_leq hO hN
          (TB_O_add hO hN (TB_add_inv h1).2.1 (TB_O_sub hO hN (TB_add_inv h1).2.2 (TB_add_inv h2).2.2)) (TB_add_inv h2).2.1)
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_add_inv s hcl e1
      obtain ⟨ya, yb, fa, fb, hy', hr1', hr2'⟩ := eval_add_inv s hcr e2
      rw [const_keeps_iff] at hk
      rsz h1 at hk
      rw [lit_val' s (TB_add_inv h1).2.2 eb, lit_val' s (TB_add_inv h2).2.2 fb] at hk
      have := bvz_range hn0 s xa; have := bvz_range hn0 s xb
      have := bvz_range hn0 s ya; have := bvz_range hn0 s yb
      have := min_for_nonpos (N := n) s; have := max_for_nonneg hn0 s
      obtain ⟨d, ed, hd⟩ := eval_O_sub_rng (s := s) hO hN (TB_add_inv h1).2.2 (TB_add_inv h2).2.2 eb fb (by omega) (by omega)
      obtain ⟨t, et, ht⟩ := eval_O_add_rng (s := s) hO hN (TB_add_inv h1).2.1 (TB_O_sub hO hN (TB_add_inv h1).2.2 (TB_add_inv h2).2.2) ea ed
        (by omega) (by omega)
      rw [eval_O_leq hO hN (TB_O_add hO hN (TB_add_inv h1).2.1 (TB_O_sub hO hN (TB_add_inv h1).2.2 (TB_add_inv h2).2.2)) (TB_add_inv h2).2.1 et fa, ht, hd,
        hy, hy']
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega
    · refine cmp_refines_leq (fun N hN h1 h2 => TBool_O_leq hO hN (TB_add_inv h1).2.1
          (TB_O_add hO hN (TB_add_inv h2).2.1 (TB_O_sub hO hN (TB_add_inv h2).2.2 (TB_add_inv h1).2.2)))
        (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
      subst hn
      obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_add_inv s hcl e1
      obtain ⟨ya, yb, fa, fb, hy', hr1', hr2'⟩ := eval_add_inv s hcr e2
      rw [const_keeps_iff] at hk
      rsz h1 at hk
      rw [lit_val' s (TB_add_inv h1).2.2 eb, lit_val' s (TB_add_inv h2).2.2 fb] at hk
      have := bvz_range hn0 s xa; have := bvz_range hn0 s xb
      have := bvz_range hn0 s ya; have := bvz_range hn0 s yb
      have := min_for_nonpos (N := n) s; have := max_for_nonneg hn0 s
      obtain ⟨d, ed, hd⟩ := eval_O_sub_rng (s := s) hO hN (TB_add_inv h2).2.2 (TB_add_inv h1).2.2 fb eb (by omega) (by omega)
      obtain ⟨t, et, ht⟩ := eval_O_add_rng (s := s) hO hN (TB_add_inv h2).2.1 (TB_O_sub hO hN (TB_add_inv h2).2.2 (TB_add_inv h1).2.2) fa ed
        (by omega) (by omega)
      rw [eval_O_leq hO hN (TB_add_inv h1).2.1 (TB_O_add hO hN (TB_add_inv h2).2.1 (TB_O_sub hO hN (TB_add_inv h2).2.2 (TB_add_inv h1).2.2)) ea et, ht, hd,
        hy, hy']
      simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_leq.r_self_add_r.proof : bv_leq.r_self_add_r.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_self_add_r] at h
  replace h := orElse_eq_some h
  rcases h with h | h <;> split at h <;> (try split at h) <;> simp at h <;>
    rename_i hc <;> simp [equal] at hc <;> obtain ⟨rfl, hc⟩ := hc <;> subst h
  · refine cmp_refines_leq (fun N hN h1 h2 => by
        rsz h1; exact TBool_O_leq hO hN (TB_zero hN) (TB_add_inv h2).2.2)
      (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv s hc e2
    cases eval_val_eq e1 ea
    rsz h1; rw [eval_O_leq hO hN (TB_zero hN) (TB_add_inv h2).2.2 (eval_zero hn0) eb, hy, bvz_zero]
    simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega
  · refine cmp_refines_leq (fun N hN h1 h2 => by
        rsz h1; exact TBool_O_leq hO hN (TB_zero hN) (TB_add_inv h2).2.1)
      (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv s hc e2
    cases eval_val_eq e1 eb
    rsz h1; rw [eval_O_leq hO hN (TB_zero hN) (TB_add_inv h2).2.1 (eval_zero hn0) ea, hy, bvz_zero]
    simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_leq.r_self_add_l.proof : bv_leq.r_self_add_l.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_self_add_l] at h
  replace h := orElse_eq_some h
  rcases h with h | h <;> split at h <;> (try split at h) <;> simp at h <;>
    rename_i hc <;> simp [equal] at hc <;> obtain ⟨rfl, hc⟩ := hc <;> subst h
  · refine cmp_refines_leq (fun N hN h1 h2 => by
        rsz h1; exact TBool_O_leq hO hN (TB_add_inv h1).2.2 (TB_zero hN))
      (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv s hc e1
    cases eval_val_eq e2 ea
    rsz h1; rw [eval_O_leq hO hN (TB_add_inv h1).2.2 (TB_zero hN) eb (eval_zero hn0), hy, bvz_zero]
    simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega
  · refine cmp_refines_leq (fun N hN h1 h2 => by
        rsz h1; exact TBool_O_leq hO hN (TB_add_inv h1).2.1 (TB_zero hN))
      (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_add_inv s hc e1
    cases eval_val_eq e2 eb
    rsz h1; rw [eval_O_leq hO hN (TB_add_inv h1).2.1 (TB_zero hN) ea (eval_zero hn0), hy, bvz_zero]
    simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_leq.r_min_l.proof : bv_leq.r_min_l.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_min_l] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; subst h; have hc := of_decide_eq_true hc
  refine cmp_refines_leq (fun _ _ _ _ => TBool_true) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  obtain ⟨rfl, -⟩ := lit_val h1 e1
  rw [TB_size h1, lit_val' s h1 e1] at hc
  have := bvz_range hn0 s x; have := bvz_range hn0 s y
  simp only [eval_v_true, eval_v_false, Option.some.injEq, Val.bool.injEq]
  symm; simp only [decide_eq_true_eq, decide_eq_false_iff_not]; omega

theorem bv_leq.r_max_r.proof : bv_leq.r_max_r.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_max_r] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; subst h; have hc := of_decide_eq_true hc
  refine cmp_refines_leq (fun _ _ _ _ => TBool_true) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  obtain ⟨rfl, -⟩ := lit_val h2 e2
  rw [TB_size h1, lit_val' s h2 e2] at hc
  have := bvz_range hn0 s x; have := bvz_range hn0 s y
  simp only [eval_v_true, eval_v_false, Option.some.injEq, Val.bool.injEq]
  symm; simp only [decide_eq_true_eq, decide_eq_false_iff_not]; omega

-- UNSOUND: when c1 = 0. Take signed = false, 8 bits, v1 = BitVec 0 and v2 = Mul
-- (checked_unsigned, x, BitVec 0) with x ↦ 0#8. c1 = c2 = 0 (divisible), so the rule returns
-- bv_leq false (bv_div false v1 vc1) x. The spec evaluates to 0 ≤u 0 = true, but
-- bv_div false 0 0 is smtUDiv 0 0 = 255, and 255 ≤u 0 is false.
theorem bv_leq.r_const_mul.proof : bv_leq.r_const_mul.Stmt := by
  sorry

-- UNSOUND: when c1 = 0. Take signed = true, 8 bits, v1 = Mul (checked_signed, x, BitVec 0) and
-- v2 = BitVec 0 with x ↦ 0#8. c1 = c2 = 0 (divisible), so the rule returns
-- bv_leq true x (bv_div true v2 vc1). The spec evaluates to 0 ≤s 0 = true, but
-- bv_div true 0 0 is smtSDiv 0 0 = -1, and 0 ≤s -1 is false.
theorem bv_leq.r_mul_const.proof : bv_leq.r_mul_const.Stmt := by
  sorry

-- UNSOUND: when a is negative (signed). Take signed = true, 8 bits, v1 = Mul (checked_signed,
-- a, x), v2 = Mul (checked_signed, a, y) with a = BitVec 255 (-1, so sure_neq a 0), x ↦ 1#8 and
-- y ↦ 2#8. Neither product overflows. The spec evaluates to (-1) ≤s (-2) = false, but the result
-- bv_leq true x y evaluates to 1 ≤s 2 = true.
theorem bv_leq.r_mul_mul.proof : bv_leq.r_mul_mul.Stmt := by
  sorry

theorem bv_leq.r_udiv_big.proof : bv_leq.r_udiv_big.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_udiv_big] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; subst h
  simp at hc; obtain ⟨rfl, hc⟩ := hc
  refine cmp_refines_leq (fun _ _ _ _ => TBool_true) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  subst hn
  obtain ⟨m, xa, xb, ea, eb, hv⟩ := eval_div_eq_some e1
  simp at hv; obtain ⟨rfl, hv⟩ := hv; cases hv
  have hd := lit_val' false (TB_div_inv h1).2.2 eb
  have hy := lit_val' false h2 e2
  rsz h1 at hc
  simp only [bv_to_z_false] at hd hy
  rw [hd, hy, max_for_false] at hc
  simp only [bvz, Bool.false_eq_true, ite_false] at hc ⊢
  have hc' : 2 ^ n ≤ y.toNat * xb.toNat := by
    have : (2 : Int) ^ n ≤ (y.toNat : Int) * xb.toNat := by omega
    exact_mod_cast this
  have hpos : 0 < xb.toNat := by
    rcases Nat.eq_zero_or_pos xb.toNat with h | h
    · rw [h] at hc'; have := Nat.two_pow_pos n; omega
    · exact h
  have hxb : xb ≠ 0 := fun e => by subst e; simp at hpos
  have hlt : xa.toNat / xb.toNat < y.toNat :=
    (Nat.div_lt_iff_lt_mul hpos).2 (by have := xa.isLt; omega)
  simp only [BitVec.smtUDiv, hxb, ite_false, eval_v_true, Option.some.injEq, Val.bool.injEq]
  simp; omega

theorem bv_leq.r_ite_l.proof : bv_leq.r_ite_l.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_ite_l] at h
  split at h <;> simp at h
  subst h
  refine cmp_refines_leq (fun N hN h1 h2 => TBool_O_ite hO (TB_ite_inv h1).1
      (TBool_O_leq hO hN (TB_ite_inv h1).2.1 h2) (TBool_O_leq hO hN (TB_ite_inv h1).2.2 h2))
    (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  obtain ⟨hb, hl, hr⟩ := TB_ite_inv h1
  refine eval_O_ite hO hb (TBool_O_leq hO hN hl h2) (TBool_O_leq hO hN hr h2) _ ?_
  rcases ite_inv e1 with ⟨eg, ex⟩ | ⟨eg, ex⟩ <;> rw [eg] <;> dsimp only
  · exact eval_O_leq hO hN hl h2 ex e2
  · exact eval_O_leq hO hN hr h2 ex e2

theorem bv_leq.r_ite_r.proof : bv_leq.r_ite_r.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_ite_r] at h
  split at h <;> simp at h
  subst h
  refine cmp_refines_leq (fun N hN h1 h2 => TBool_O_ite hO (TB_ite_inv h2).1
      (TBool_O_leq hO hN h1 (TB_ite_inv h2).2.1) (TBool_O_leq hO hN h1 (TB_ite_inv h2).2.2))
    (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  obtain ⟨hb, hl, hr⟩ := TB_ite_inv h2
  refine eval_O_ite hO hb (TBool_O_leq hO hN h1 hl) (TBool_O_leq hO hN h1 hr) _ ?_
  rcases ite_inv e2 with ⟨eg, ex⟩ | ⟨eg, ex⟩ <;> rw [eg] <;> dsimp only
  · exact eval_O_leq hO hN h1 hl e1 ex
  · exact eval_O_leq hO hN h1 hr e1 ex

theorem bv_leq.r_const_sub1.proof : bv_leq.r_const_sub1.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_const_sub1] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; subst h
  refine Refines.ite_split (fun hov => Refines.ite_split (fun hs => ?_) (fun _ => Refines.refl))
    (fun hov => ?_)
  · obtain rfl : s = false := by simpa using hs
    refine cmp_refines_leq (fun _ _ _ _ => TBool_false) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_sub_inv false hc e2
    rsz h1 at hov
    simp only [overflows_add, Bool.or_eq_true, decide_eq_true_eq] at hov
    rw [lit_val' false h1 e1, lit_val' false (TB_sub_inv h2).2.2 eb] at hov
    have := bvz_false_range xa; have := bvz_false_range xb
    have := bvz_false_range x; have := bvz_false_range y
    simp only [max_for_false, min_for_false] at *
    simp; omega
  · simp at hov
    refine cmp_refines_leq (fun N hN h1 h2 => TBool_O_leq hO hN (TB_O_add hO hN h1 (TB_sub_inv h2).2.2) (TB_sub_inv h2).2.1)
      (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_sub_inv s hc e2
    rsz h1 at hov
    rw [overflows_add_false, lit_val' s h1 e1, lit_val' s (TB_sub_inv h2).2.2 eb] at hov
    obtain ⟨r', er', hr'⟩ := eval_O_add_rng (s := s) hO hN h1 (TB_sub_inv h2).2.2 e1 eb hov.1 hov.2
    rw [eval_O_leq hO hN (TB_O_add hO hN h1 (TB_sub_inv h2).2.2) (TB_sub_inv h2).2.1 er' ea, hr', hy]
    simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_leq.r_const_sub2.proof : bv_leq.r_const_sub2.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_const_sub2] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; subst h
  refine Refines.ite_split (fun hov => Refines.ite_split (fun hs => ?_) (fun _ => Refines.refl))
    (fun hov => ?_)
  · obtain rfl : s = false := by simpa using hs
    refine cmp_refines_leq (fun _ _ _ _ => TBool_false) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_sub_inv false hc e2
    rsz h1 at hov
    simp only [overflows_sub, Bool.or_eq_true, decide_eq_true_eq] at hov
    rw [lit_val' false (TB_sub_inv h2).2.1 ea, lit_val' false h1 e1] at hov
    have := bvz_false_range xa; have := bvz_false_range xb
    have := bvz_false_range x; have := bvz_false_range y
    simp only [max_for_false, min_for_false] at *
    simp; omega
  · simp at hov
    refine cmp_refines_leq (fun N hN h1 h2 => TBool_O_leq hO hN (TB_sub_inv h2).2.2 (TB_O_sub hO hN (TB_sub_inv h2).2.1 h1))
      (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_sub_inv s hc e2
    rsz h1 at hov
    rw [overflows_sub_false, lit_val' s (TB_sub_inv h2).2.1 ea, lit_val' s h1 e1] at hov
    obtain ⟨r', er', hr'⟩ := eval_O_sub_rng (s := s) hO hN (TB_sub_inv h2).2.1 h1 ea e1 hov.1 hov.2
    rw [eval_O_leq hO hN (TB_sub_inv h2).2.2 (TB_O_sub hO hN (TB_sub_inv h2).2.1 h1) eb er', hr', hy]
    simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_leq.r_sub_const1.proof : bv_leq.r_sub_const1.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_sub_const1] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; subst h
  refine Refines.ite_split (fun hov => Refines.ite_split (fun hs => ?_) (fun _ => Refines.refl))
    (fun hov => ?_)
  · obtain rfl : s = false := by simpa using hs
    refine cmp_refines_leq (fun _ _ _ _ => TBool_true) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_sub_inv false hc e1
    rsz h1 at hov
    simp only [overflows_add, Bool.or_eq_true, decide_eq_true_eq] at hov
    rw [lit_val' false h2 e2, lit_val' false (TB_sub_inv h1).2.2 eb] at hov
    have := bvz_false_range xa; have := bvz_false_range xb
    have := bvz_false_range x; have := bvz_false_range y
    simp only [max_for_false, min_for_false] at *
    simp; omega
  · simp at hov
    refine cmp_refines_leq (fun N hN h1 h2 => TBool_O_leq hO hN (TB_sub_inv h1).2.1 (TB_O_add hO hN h2 (TB_sub_inv h1).2.2))
      (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_sub_inv s hc e1
    rsz h1 at hov
    rw [overflows_add_false, lit_val' s h2 e2, lit_val' s (TB_sub_inv h1).2.2 eb] at hov
    obtain ⟨r', er', hr'⟩ := eval_O_add_rng (s := s) hO hN h2 (TB_sub_inv h1).2.2 e2 eb hov.1 hov.2
    rw [eval_O_leq hO hN (TB_sub_inv h1).2.1 (TB_O_add hO hN h2 (TB_sub_inv h1).2.2) ea er', hr', hy]
    simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_leq.r_sub_const2.proof : bv_leq.r_sub_const2.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_sub_const2] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; subst h
  refine Refines.ite_split (fun hov => Refines.ite_split (fun hs => ?_) (fun _ => Refines.refl))
    (fun hov => ?_)
  · obtain rfl : s = false := by simpa using hs
    refine cmp_refines_leq (fun _ _ _ _ => TBool_true) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, hr1, hr2⟩ := eval_sub_inv false hc e1
    rsz h1 at hov
    simp only [overflows_sub, Bool.or_eq_true, decide_eq_true_eq] at hov
    rw [lit_val' false (TB_sub_inv h1).2.1 ea, lit_val' false h2 e2] at hov
    have := bvz_false_range xa; have := bvz_false_range xb
    have := bvz_false_range x; have := bvz_false_range y
    simp only [max_for_false, min_for_false] at *
    simp; omega
  · simp at hov
    refine cmp_refines_leq (fun N hN h1 h2 => TBool_O_leq hO hN (TB_O_sub hO hN (TB_sub_inv h1).2.1 h2) (TB_sub_inv h1).2.2)
      (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
    subst hn
    obtain ⟨xa, xb, ea, eb, hy, -⟩ := eval_sub_inv s hc e1
    rsz h1 at hov
    rw [overflows_sub_false, lit_val' s (TB_sub_inv h1).2.1 ea, lit_val' s h2 e2] at hov
    obtain ⟨r', er', hr'⟩ := eval_O_sub_rng (s := s) hO hN (TB_sub_inv h1).2.1 h2 ea e2 hov.1 hov.2
    rw [eval_O_leq hO hN (TB_O_sub hO hN (TB_sub_inv h1).2.1 h2) (TB_sub_inv h1).2.2 er' eb, hr', hy]
    simp only [Option.some.injEq, Val.bool.injEq, decide_eq_decide]; omega

theorem bv_leq.r_ub_r.proof : bv_leq.r_ub_r.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_ub_r] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; simp at hc; obtain ⟨rfl, hc⟩ := hc; subst h
  refine cmp_refines_leq (fun _ _ _ _ => TBool_true) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  have := le_unsigned_ub h1 e1; have := lit_val' false h2 e2
  simp only [bv_to_z_false] at *
  simp; omega

theorem bv_leq.r_ub_l.proof : bv_leq.r_ub_l.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_ub_l] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; simp at hc; obtain ⟨rfl, hc⟩ := hc; subst h
  refine cmp_refines_leq (fun _ _ _ _ => TBool_false) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  have := le_unsigned_ub h2 e2; have := lit_val' false h1 e1
  simp only [bv_to_z_false] at *
  simp; omega

theorem bv_leq.r_to_unsigned_l.proof : bv_leq.r_to_unsigned_l.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_to_unsigned_l] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; simp at hc; obtain ⟨rfl, -⟩ := hc; subst h
  exact signed_to_unsigned_left hO true _ _ v2

theorem bv_leq.r_to_unsigned_r.proof : bv_leq.r_to_unsigned_r.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_to_unsigned_r] at h
  split at h <;> (try split at h) <;> simp at h
  rename_i hc; simp at hc; obtain ⟨rfl, -⟩ := hc; subst h
  exact signed_to_unsigned_right hO true _ _ v1

theorem bv_leq.r_default.proof : bv_leq.r_default.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_leq.r_default, Option.some.injEq] at h
  subst h; exact Refines.refl

end Bvr
