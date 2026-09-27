import Bvr.Proofs.ArithLemmas

/-! Bit-vector arithmetic and overflow checks. -/

namespace Bvr

open Classical ArithL

set_option linter.unusedSimpArgs false

theorem bv_neg.r_lit.proof : bv_neg.r_lit.Stmt := by
  intro FS O hO c v res h
  simp only [bv_neg.r_lit] at h; split at h <;> simp at h; subst h
  refine Refines.neg_intro (fun n wa hT => ?_) (fun n wa hT ρ x v hx e => ?_)
  · rw [size_ty_lit wa]; exact BV_mk_masked wa.2.2
  · rw [size_ty_lit wa, eval_mk_masked wa.2.2]
    rw [lit_eval_eq wa hx] at e
    simp [evUnop] at e
    rw [← e.2, BitVec.ofInt_neg]

theorem bv_neg.r_neg.proof : bv_neg.r_neg.Stmt := by
  intro FS O hO c v res h
  simp only [bv_neg.r_neg] at h; split at h <;> simp at h; subst h
  rename_i ck T
  refine Refines.neg_intro (fun n wa hT => (BV_neg_inv wa).1) (fun n wa hT ρ x v hx e => ?_)
  obtain ⟨wx, rfl⟩ := BV_neg_inv wa
  rw [eval_neg wx rfl] at hx
  obtain ⟨X, hX, hx⟩ := evUnop_inv wx hx
  simp [evUnop] at hx e
  obtain ⟨-, rfl⟩ := hx; obtain ⟨-, rfl⟩ := e
  rw [hX]; simp

theorem bv_neg.r_ite.proof : bv_neg.r_ite.Stmt := by
  intro FS O hO c v res h
  simp only [bv_neg.r_ite] at h; split at h <;> simp at h; subst h
  rename_i g l r T
  refine Refines.neg_intro (fun n wa hT => ?_) (fun n wa hT ρ x v hx e => ?_)
  all_goals obtain ⟨wg, hg, wl, wr, rfl⟩ := BV_ite_inv wa
  all_goals have hA := O_neg (hO.bv_neg c l) wl
  all_goals have hB := O_neg (hO.bv_neg c r) wr
  all_goals have hres := O_ite hO wg hg hA.1 hB.1
  · exact hres.1
  · refine hres.2 ρ v ?_
    rcases eval_ite_inv hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1, hA.2 ρ x v h2 e⟩
    · exact .inr ⟨h1, hB.2 ρ x v h2 e⟩

theorem bv_neg.r_of_bool.proof : bv_neg.r_of_bool.Stmt := by
  intro FS O hO c v res h
  simp only [bv_neg.r_of_bool] at h; split at h <;> simp at h; subst h
  rename_i m g T
  refine Refines.neg_intro (fun n wa hT => ?_) (fun n wa hT ρ x v hx e => ?_)
  all_goals obtain ⟨rfl, wg, hg, rfl⟩ := BV_ofBool_inv wa
  all_goals have hA := O_neg (hO.bv_neg false (bv_one m)) (BV_bv_one wa.2.2)
  all_goals have hres := O_ite hO wg hg hA.1 (BV_bv_zero wa.2.2)
  · exact hres.1
  · refine hres.2 ρ v ?_
    obtain ⟨b, hb, rfl⟩ := eval_ofBool_inv wa hx
    cases b
    · refine .inr ⟨hb, ?_⟩
      simp [evUnop] at e; rw [eval_bv_zero wa.2.2, ← e.2]; simp
    · refine .inl ⟨hb, hA.2 ρ 1 v (eval_bv_one wa.2.2) ?_⟩
      simp [evUnop] at e ⊢; exact e.2

theorem bv_neg.r_default.proof : bv_neg.r_default.Stmt := by
  intro FS O hO c v res h
  simp only [bv_neg.r_default] at h; simp at h; subst h
  exact Refines.refl

theorem bv_mod.r_lits.proof : bv_mod.r_lits.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_mod.r_lits] at h; split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h; subst h
  refine Refines.arith_intro .mod_ (fun n wa wb hT => ?_) (fun n wa wb hT ρ x y v hx hy e => ?_)
  · rw [size_eq, Term.ty_mk, size_ty_lit wa]; exact BV_mk_masked wa.2.2
  · obtain ⟨-, hz1⟩ := BV_lit wa
    obtain ⟨-, hz2⟩ := BV_lit wb
    rw [size_eq, Term.ty_mk, size_ty_lit wa, eval_mk_masked wa.2.2]
    rw [lit_eval_eq wa hx, lit_eval_eq wb hy] at e
    simp [evBinop, bvBin] at e; subst e
    rw [bv_to_z_lit wa.2.2 hz1.1 hz1.2, bv_to_z_lit wa.2.2 hz2.1 hz2.2]
    rw [← BitVec.ofInt_toInt (x := BitVec.smod _ _), BitVec.toInt_smod]
    simp only [↓reduceIte, trem, ← smod_formula]
    congr 4 <;> simp

theorem bv_mod.r_default.proof : bv_mod.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_mod.r_default] at h; simp at h; subst h
  exact Refines.refl

theorem bv_rem.r_lits.proof : bv_rem.r_lits.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_rem.r_lits] at h; split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h; subst h
  refine Refines.arith_intro (.rem s) (fun n wa wb hT => ?_) (fun n wa wb hT ρ x y v hx hy e => ?_)
  · rw [size_eq, Term.ty_mk, size_ty_lit wa]; exact BV_mk_masked wa.2.2
  · obtain ⟨-, hz1⟩ := BV_lit wa
    obtain ⟨-, hz2⟩ := BV_lit wb
    rw [size_eq, Term.ty_mk, size_ty_lit wa, eval_mk_masked wa.2.2]
    rw [lit_eval_eq wa hx, lit_eval_eq wb hy] at e
    simp [evBinop, bvBin] at e; subst e
    rw [bv_to_z_lit wa.2.2 hz1.1 hz1.2, bv_to_z_lit wa.2.2 hz2.1 hz2.2]
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte, trem]
      rw [← Int.ofNat_tmod, BitVec.ofInt_natCast]
      congr 2; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, BitVec.toNat_umod]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) (BitVec.isLt _))
    · simp only [↓reduceIte, trem]
      rw [← BitVec.toInt_srem, BitVec.ofInt_toInt]

theorem bv_rem.r_zero_l.proof : bv_rem.r_zero_l.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_rem.r_zero_l] at h; split at h <;> simp at h; obtain ⟨rfl, rfl⟩ := h
  refine Refines.arith_intro (.rem s) (fun n wa wb hT => ?_) (fun n wa wb hT ρ x y v hx hy e => ?_)
  · rw [size_ty_lit wa]; exact BV_bv_zero wa.2.2
  · rw [size_ty_lit wa, eval_bv_zero wa.2.2]
    rw [lit_eval_eq wa hx] at e
    simp [evBinop, bvBin] at e; subst e
    cases s <;> simp

theorem bv_rem.r_one_r.proof : bv_rem.r_one_r.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_rem.r_one_r] at h; split at h <;> simp at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  refine Refines.arith_intro (.rem false) (fun n wa wb hT => ?_)
    (fun n wa wb hT ρ x y v hx hy e => ?_)
  · simp only [wa.2.1, size_of_ty_bitVector]; exact BV_bv_zero wa.2.2
  · simp only [wa.2.1, size_of_ty_bitVector]; rw [eval_bv_zero wa.2.2]
    rw [lit_eval_eq wb hy] at e
    simp [evBinop, bvBin] at e; subst e
    congr 2

theorem bv_rem.r_pow2.proof : bv_rem.r_pow2.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_rem.r_pow2] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i r T hc
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at hc
  obtain ⟨rfl, hp, hr⟩ := hc
  obtain ⟨hz, hl⟩ := is_pow2_eq hp
  generalize hk : log2 r = k at hz hl
  have hE := hO.bv_extract 0 (k - 1) v1
  refine Refines.trans ?_ (hO.bv_extend _ _ _)
  have key : ∀ n, BV v1 n → BV (.mk (.bitVec r) T) n → 1 ≤ k ∧ k < n := by
    intro n wa wb
    obtain ⟨-, -, z1⟩ := BV_lit wb
    have e1 : ((2 ^ k.toNat : Nat) : Int) = (2 : Int) ^ k.toNat := by push_cast; rfl
    have e2 : ((2 ^ n.toNat : Nat) : Int) = (2 : Int) ^ n.toNat := by push_cast; rfl
    have h1 : 2 ^ k.toNat < 2 ^ n.toNat := by omega
    have h2 := (Nat.pow_lt_pow_iff_right (by omega)).1 h1
    have h3 : k.toNat ≠ 0 := by intro h0; rw [h0] at hz; simp at hz; omega
    have := wa.2.2
    omega
  refine Refines.arith_intro (.rem false) (fun n wa wb hT => ?_)
    (fun n wa wb hT ρ x y v hx hy e => ?_)
  all_goals obtain ⟨k1, k2⟩ := key n wa wb
  all_goals have wE := BV_extract hE wa (by omega) (by omega) (by omega)
  · refine ⟨WT_extend.2 ⟨_, wE, by rw [size_BV wa]; omega, by rw [size_BV wE]⟩, ?_, wa.2.2⟩
    simp only [bv_extend.spec, size_BV wE, size_BV wa, Term.ty_mk]; congr 1; omega
  · have hX := hE.sem ρ _ (eval_extract_spec wa (by omega) (by omega) (by omega) hx)
    rw [eval_extend wE (by rw [size_BV wa]; omega) hX]
    rw [lit_eval_eq wb hy] at e
    simp [evBinop, bvBin] at e; subst e
    rw [size_BV wa]
    congr 1; apply Val.bv_congr (by omega)
    rw [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, BitVec.toNat_umod, hz,
      ← natCast_two_pow, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
    have hK : (k - 1 - 0 + 1).toNat = k.toNat := by omega
    have hKN : 2 ^ k.toNat < 2 ^ n.toNat := Nat.pow_lt_pow_right (by omega) (by omega)
    rw [hK, Int.toNat_zero, Nat.shiftRight_zero, Nat.mod_eq_of_lt hKN,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
        (Nat.pow_le_pow_right (by omega) (Nat.le_add_right _ _)))]

theorem bv_rem.r_add.proof : bv_rem.r_add.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_rem.r_add] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;>
    obtain ⟨⟨rfl, rfl, hu⟩, rfl⟩ := h
  · rename_i ck d T1 r T _
    refine Refines.arith_intro (.rem false) (fun n wa wb hT => ?_)
      (fun n wa wb hT ρ x y v hx hy e => ?_)
    all_goals obtain ⟨wd, wr, rfl⟩ := BV_arith_inv (.add ck) wa
    · exact BV_arith (.rem _) (hO.bv_rem false r _) wr wb
    · rw [eval_arith (.add ck) wd wr rfl] at hx
      obtain ⟨D, R, hD, hR, hx2⟩ := evBinop_inv (.inl (.add ck)) wd wr hx
      obtain ⟨rfl, -⟩ := BV_lit wd
      obtain ⟨rfl, -⟩ := BV_lit wb
      rw [hD] at hy; simp at hy; subst hy
      refine O_eval (.rem _) (hO.bv_rem _ _ _) wr wb hR hD ?_
      simp [evBinop, checkedOp, bvBin] at hx2 e ⊢
      obtain ⟨⟨-, h2⟩, rfl⟩ := hx2; subst e
      congr 1; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_umod, BitVec.toNat_umod, toNat_add_ok (h2 hu), Nat.add_mod_left]
  · rename_i ck r d T1 T _
    refine Refines.arith_intro (.rem false) (fun n wa wb hT => ?_)
      (fun n wa wb hT ρ x y v hx hy e => ?_)
    all_goals obtain ⟨wr, wd, rfl⟩ := BV_arith_inv (.add ck) wa
    · exact BV_arith (.rem _) (hO.bv_rem false r _) wr wb
    · rw [eval_arith (.add ck) wr wd rfl] at hx
      obtain ⟨R, D, hR, hD, hx2⟩ := evBinop_inv (.inl (.add ck)) wr wd hx
      obtain ⟨rfl, -⟩ := BV_lit wd
      obtain ⟨rfl, -⟩ := BV_lit wb
      rw [hD] at hy; simp at hy; subst hy
      refine O_eval (.rem _) (hO.bv_rem _ _ _) wr wb hR hD ?_
      simp [evBinop, checkedOp, bvBin] at hx2 e ⊢
      obtain ⟨⟨-, h2⟩, rfl⟩ := hx2; subst e
      congr 1; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_umod, BitVec.toNat_umod, toNat_add_ok (h2 hu), Nat.add_mod_right]

theorem bv_rem.r_rem_rem.proof : bv_rem.r_rem_rem.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_rem.r_rem_rem] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i r r1 T1 T r2 T2 hc
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_true_eq] at hc
  obtain ⟨rfl, h1, h2, hd⟩ := hc
  refine Refines.trans ?_ (hO.bv_rem false r _)
  refine Refines.arith_intro (.rem false) (fun n wa wb hT => ?_)
    (fun n wa wb hT ρ x y v hx hy e => ?_)
  all_goals obtain ⟨wr, wc, rfl⟩ := BV_arith_inv (.rem false) wa
  all_goals have wrhs : BV (if decide (zmin r1 r2 = r1) = true then Term.mk (Kind.bitVec r1) T1
      else Term.mk (Kind.bitVec r2) T2) n := by split <;> assumption
  · exact ⟨(WT_arith (.rem false)).2 ⟨n, wr, wrhs, wr.2.1⟩, wr.2.1, wr.2.2⟩
  · rw [eval_arith (.rem false) wr wc rfl] at hx
    obtain ⟨R, C, hR, hC, hx⟩ := evBinop_inv (.inl (.rem false)) wr wc hx
    obtain ⟨-, z1⟩ := BV_lit wc
    obtain ⟨-, z2⟩ := BV_lit wb
    rw [lit_eval_eq wc hC] at hx
    rw [lit_eval_eq wb hy] at e
    rw [bv_rem.spec, ty_eq, eval_arith (.rem false) wr wrhs wr.2.1, hR]
    simp [evBinop, bvBin] at hx e; subst hx; subst e
    have hmm := mod_mod_min (x := R.toNat) (a := r1.toNat) (b := r2.toNat) (by omega) (by omega)
      (hd.imp (dvd_of_trem (by omega) (by omega)) (dvd_of_trem (by omega) (by omega)))
    have e1 : (BitVec.ofInt n.toNat r1).toNat = r1.toNat := by
      have := toNat_ofInt_lit (w := n.toNat) z1.1 z1.2; omega
    have e2 : (BitVec.ofInt n.toNat r2).toNat = r2.toNat := by
      have := toNat_ofInt_lit (w := n.toNat) z2.1 z2.2; omega
    by_cases hle : r1 ≤ r2
    · have : zmin r1 r2 = r1 := by simp [zmin, hle]
      simp only [this, decide_true, ↓reduceIte, eval_lit wc]
      simp [evBinop, bvBin]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_umod, BitVec.toNat_umod, BitVec.toNat_umod, e1, e2, hmm]
      simp [show r1.toNat ≤ r2.toNat by omega]
    · have : zmin r1 r2 ≠ r1 := by simp [zmin, hle]; omega
      simp only [this, decide_false, Bool.false_eq_true, ↓reduceIte, eval_lit wb]
      simp [evBinop, bvBin]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_umod, BitVec.toNat_umod, BitVec.toNat_umod, e1, e2, hmm]
      simp [show ¬ r1.toNat ≤ r2.toNat by omega]

theorem bv_rem.r_default.proof : bv_rem.r_default.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_rem.r_default] at h; simp at h; subst h
  exact Refines.refl

theorem bv_add_overflows.r_lits.proof : bv_add_overflows.r_lits.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_add_overflows.r_lits] at h; split at h <;> simp at h; subst h
  refine Refines.cmp_intro (.addOvf s) (fun n wa wb hT => of_bool_BoolT _)
    (fun n wa wb hT ρ x y v hx hy e => ?_)
  obtain ⟨rfl, hz1⟩ := BV_lit wa; obtain ⟨-, hz2⟩ := BV_lit wb
  rw [lit_eval_eq wa hx, lit_eval_eq wb hy] at e
  simp [evBinop, bvBin] at e; subst e
  rw [size_of_ty_bitVector, overflows_add_lit wa.2.2 hz1.1 hz1.2 hz2.1 hz2.2, eval_of_bool]

theorem bv_add_overflows.r_zero.proof : bv_add_overflows.r_zero.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_add_overflows.r_zero] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    refine Refines.cmp_intro (.addOvf s) (fun n wa wb hT => ⟨v_false_WT, rfl⟩)
      (fun n wa wb hT ρ x y v hx hy e => ?_)
  · rw [lit_eval_eq wa hx] at e
    simp [evBinop, bvBin] at e; subst e
    cases s <;> simp [saddOverflow_zero_left, uaddOverflow_zero_left]
  · rw [lit_eval_eq wb hy] at e
    simp [evBinop, bvBin] at e; subst e
    cases s <;> simp [saddOverflow_comm x, uaddOverflow_comm x, saddOverflow_zero_left,
      uaddOverflow_zero_left]

theorem bv_add_overflows.r_size1.proof : bv_add_overflows.r_size1.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_add_overflows.r_size1] at h; split at h <;> simp at h; subst h
  rename_i h1
  refine Refines.cmp_intro (.addOvf s) (fun n wa wb hT => ?_)
    (fun n wa wb hT ρ x y v hx hy e => ?_)
  all_goals obtain rfl : n = 1 := by simpa [wa.2.1] using h1
  all_goals have e1 := O_sem_eq hO wa (BV_bv_one (n := 1) (by omega))
  all_goals have e2 := O_sem_eq hO wb (BV_bv_one (n := 1) (by omega))
  all_goals have hr := O_b_and hO e1.1 e2.1
  · exact hr.1
  · rw [hr.2 ρ _ _ (e1.2 ρ x 1 hx (eval_bv_one (by omega))) (e2.2 ρ y 1 hy (eval_bv_one (by omega)))]
    simp [evBinop, bvBin] at e; subst e
    congr 2
    clear hx hy
    revert x y
    show ∀ x y : BitVec 1, _
    cases s <;> decide

theorem bv_add_overflows.r_unsigned.proof : bv_add_overflows.r_unsigned.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_add_overflows.r_unsigned] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    refine Refines.cmp_intro (.addOvf false) (fun n wa wb hT => ?_)
      (fun n wa wb hT ρ x y v hx hy e => ?_)
  · obtain ⟨rfl, hz⟩ := BV_lit wa
    simp only [size_of_ty_bitVector, max_for_eq wa.2.2, Bool.false_eq_true, ↓reduceIte]
    exact (O_bv_lt hO (BV_mk_bv wa.2.2) wb).1
  · obtain ⟨rfl, hz⟩ := BV_lit wa
    simp only [size_of_ty_bitVector, max_for_eq wa.2.2, Bool.false_eq_true, ↓reduceIte]
    rw [(O_bv_lt hO (BV_mk_bv wa.2.2) wb).2 ρ _ y (by rw [mk_bv, eval_mk_masked wa.2.2]) hy]
    obtain rfl := lit_eval_eq wa hx
    simp [evBinop, bvBin] at e; subst e
    rw [uaddOverflow_eq_ult, toNat_ofInt_lit hz.1 hz.2]; simp
  · simp only [wa.2.1, size_of_ty_bitVector, max_for_eq wa.2.2, Bool.false_eq_true, ↓reduceIte]
    exact (O_bv_lt hO (BV_mk_bv wa.2.2) wa).1
  · simp only [wa.2.1, size_of_ty_bitVector, max_for_eq wa.2.2, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨rfl, hz⟩ := BV_lit wb
    rw [(O_bv_lt hO (BV_mk_bv wa.2.2) wa).2 ρ _ x (by rw [mk_bv, eval_mk_masked wa.2.2]) hx]
    obtain rfl := lit_eval_eq wb hy
    simp [evBinop, bvBin] at e; subst e
    rw [uaddOverflow_comm, uaddOverflow_eq_ult, toNat_ofInt_lit hz.1 hz.2]; simp

theorem bv_add_overflows.r_signed.proof : bv_add_overflows.r_signed.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_add_overflows.r_signed] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    refine Refines.cmp_intro (.addOvf true) (fun n wa wb hT => ?_)
      (fun n wa wb hT ρ x y v hx hy e => ?_)
  · obtain ⟨rfl, hz⟩ := BV_lit wa
    simp only [size_of_ty_bitVector]
    exact BoolT_ite (O_bv_lt hO (BV_mk_bv wa.2.2) wb).1 (O_bv_lt hO wb (BV_mk_masked wa.2.2)).1
  · obtain ⟨rfl, hz⟩ := BV_lit wa
    obtain rfl := lit_eval_eq wa hx
    simp [evBinop, bvBin] at e; subst e
    simp only [size_of_ty_bitVector, bv_to_z_lit wa.2.2 hz.1 hz.2, max_for_eq wa.2.2,
      min_for_eq wa.2.2, ↓reduceIte]
    split
    · rename_i hp
      rw [(O_bv_lt hO (BV_mk_bv wa.2.2) wb).2 ρ _ y (by rw [mk_bv, eval_mk_masked wa.2.2]) hy,
        saddOverflow_pos _ _ hp]
      simp
    · rename_i hp
      rw [(O_bv_lt hO wb (BV_mk_masked wa.2.2)).2 ρ y _ hy (eval_mk_masked wa.2.2),
        saddOverflow_nonpos (by have := wa.2.2; omega) _ _ (by omega)]
      simp
  · simp only [wa.2.1, size_of_ty_bitVector]
    exact BoolT_ite (O_bv_lt hO (BV_mk_bv wa.2.2) wa).1 (O_bv_lt hO wa (BV_mk_masked wa.2.2)).1
  · obtain ⟨rfl, hz⟩ := BV_lit wb
    obtain rfl := lit_eval_eq wb hy
    simp [evBinop, bvBin] at e; subst e
    simp only [wa.2.1, size_of_ty_bitVector, bv_to_z_lit wa.2.2 hz.1 hz.2, max_for_eq wa.2.2,
      min_for_eq wa.2.2, ↓reduceIte]
    rw [saddOverflow_comm]
    split
    · rename_i hp
      rw [(O_bv_lt hO (BV_mk_bv wa.2.2) wa).2 ρ _ x (by rw [mk_bv, eval_mk_masked wa.2.2]) hx,
        saddOverflow_pos _ _ hp]
      simp
    · rename_i hp
      rw [(O_bv_lt hO wa (BV_mk_masked wa.2.2)).2 ρ x _ hx (eval_mk_masked wa.2.2),
        saddOverflow_nonpos (by have := wa.2.2; omega) _ _ (by omega)]
      simp

theorem bv_add_overflows.r_of_bools.proof : bv_add_overflows.r_of_bools.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_add_overflows.r_of_bools] at h; split at h <;> simp at h; obtain ⟨hm, rfl⟩ := h
  rename_i m g1 T1 m2 g2 T2
  refine Refines.cmp_intro (.addOvf s) (fun n wa wb hT => ?_)
    (fun n wa wb hT ρ x y v hx hy e => ?_)
  all_goals obtain ⟨rfl, wg1, hg1, rfl⟩ := BV_ofBool_inv wa
  all_goals obtain ⟨rfl, wg2, hg2, -⟩ := BV_ofBool_inv wb
  all_goals have hr := O_b_and hO ⟨wg1, hg1⟩ ⟨wg2, hg2⟩
  · split
    · exact hr.1
    · exact ⟨v_false_WT, rfl⟩
  · obtain ⟨b1, hb1, rfl⟩ := eval_ofBool_inv wa hx
    obtain ⟨b2, hb2, rfl⟩ := eval_ofBool_inv wb hy
    simp [evBinop, bvBin] at e; subst e
    split
    · rename_i hs
      obtain ⟨rfl, rfl⟩ : s = true ∧ m2 = 2 := by simpa using hs
      rw [hr.2 ρ b1 b2 hb1 hb2]
      congr 2; cases b1 <;> cases b2 <;> decide
    · rename_i hs
      have hs' : s = true → ¬m2 = 2 := by simpa using hs
      rw [eval_v_false, ofBools_addOvf (by omega) s b1 b2 (fun h => hs' h.1 (by omega))]

theorem bv_add_overflows.of_bool_aux {FS : FloatSem} {O : Ops} (hO : O.Sound FS)
    {s m g T other N} (hN : ∀ n, T = .bitVector n → other.ty = .bitVector n → N = n)
    (h1 : 1 < N) :
    Refines FS (.mk (.binop (.addOvf s) (.mk (.unop (.bvOfBool m) g) T) other) .bool)
      (O.b_and g (O.sem_eq (.mk other.kind (.bitVector N)) (mk_bv N (max_for s N)))) := by
  refine Refines.cmp_intro (.addOvf s) (fun n wa wb hT => ?_)
    (fun n wa wb hT ρ x y v hx hy e => ?_)
  all_goals obtain ⟨rfl, wg, hg, hT'⟩ := BV_ofBool_inv wa
  all_goals obtain rfl := hN _ hT' wb.2.1
  all_goals rw [Term.mk_kind_of_ty wb.2.1]
  all_goals have hq := O_sem_eq hO wb (BV_mk_bv (z := max_for s N) wb.2.2)
  all_goals have hr := O_b_and hO ⟨wg, hg⟩ hq.1
  · exact hr.1
  · obtain ⟨b, hb, rfl⟩ := eval_ofBool_inv wa hx
    simp [evBinop, bvBin] at e; subst e
    rw [hr.2 ρ b _ hb (hq.2 ρ y _ hy (by rw [mk_bv, eval_mk_masked wb.2.2])),
      ofBool_addOvf (by omega), max_for_eq wb.2.2]

theorem bv_add_overflows.r_of_bool.proof : bv_add_overflows.r_of_bool.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_add_overflows.r_of_bool] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> obtain ⟨hn, rfl⟩ := h <;>
    simp only [bv_add_overflows.spec]
  · exact bv_add_overflows.of_bool_aux hO (fun n h _ => by simp [h]) hn
  · exact Refines.trans (Refines.comm (.addOvf s))
      (bv_add_overflows.of_bool_aux hO (fun n _ h => by simp [h]) hn)

theorem bv_add_overflows.r_default.proof : bv_add_overflows.r_default.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_add_overflows.r_default] at h; simp at h; subst h
  exact Refines.commut_binop (.addOvf s)

theorem bv_mul_overflows.r_lits.proof : bv_mul_overflows.r_lits.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_mul_overflows.r_lits] at h; split at h <;> simp at h; subst h
  refine Refines.cmp_intro (.mulOvf s) (fun n wa wb hT => of_bool_BoolT _)
    (fun n wa wb hT ρ x y v hx hy e => ?_)
  obtain ⟨rfl, hz1⟩ := BV_lit wa; obtain ⟨-, hz2⟩ := BV_lit wb
  rw [lit_eval_eq wa hx, lit_eval_eq wb hy] at e
  simp [evBinop, bvBin] at e; subst e
  rw [size_of_ty_bitVector, overflows_mul_lit wa.2.2 hz1.1 hz1.2 hz2.1 hz2.2, eval_of_bool]

theorem bv_mul_overflows.r_size1.proof : bv_mul_overflows.r_size1.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_mul_overflows.r_size1] at h; split at h <;> simp at h; subst h
  rename_i h1
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1; obtain ⟨rfl, h1⟩ := h1
  refine Refines.cmp_intro (.mulOvf true) (fun n wa wb hT => ?_)
    (fun n wa wb hT ρ x y v hx hy e => ?_)
  all_goals obtain rfl : n = 1 := by simpa [wa.2.1] using h1
  all_goals have e1 := O_sem_eq hO wa (BV_bv_one (n := 1) (by omega))
  all_goals have e2 := O_sem_eq hO wb (BV_bv_one (n := 1) (by omega))
  all_goals have hr := O_b_and hO e1.1 e2.1
  · exact hr.1
  · rw [hr.2 ρ _ _ (e1.2 ρ x 1 hx (eval_bv_one (by omega))) (e2.2 ρ y 1 hy (eval_bv_one (by omega)))]
    simp [evBinop, bvBin] at e; subst e
    congr 2
    clear hx hy
    revert x y
    show ∀ x y : BitVec 1, _
    decide

theorem bv_mul_overflows.r_msb.proof : bv_mul_overflows.r_msb.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_mul_overflows.r_msb] at h
  cases s <;> simp at h <;> obtain ⟨hc, rfl⟩ := h <;>
    refine Refines.cmp_intro (.mulOvf _) (fun n wa wb hT => ⟨v_false_WT, rfl⟩)
      (fun n wa wb hT ρ x y v hx hy e => ?_) <;>
    have ha := msb_bound (FS := FS) (ρ := ρ) wa <;>
    have hb := msb_bound (FS := FS) (ρ := ρ) wb <;>
    simp [evBinop, bvBin] at e <;> subst e <;>
    have hn : ((n.toNat : Nat) : Int) = n := (by have := wa.2.2; omega) <;>
    simp only [size_eq, wa.2.1, size_of_ty_bitVector, decide_eq_true_eq] at hc
  · have := mulOvf_of_msb false ha.1 hb.1 (ha.2 x hx) (hb.2 y hy) (by simp; omega)
    simp at this; rw [this, eval_v_false]
  · have := mulOvf_of_msb true ha.1 hb.1 (ha.2 x hx) (hb.2 y hy) (by simp; omega)
    simp at this; rw [this, eval_v_false]

theorem bv_mul_overflows.const_aux {FS : FloatSem} {O : Ops} (hO : O.Sound FS) {s z T x N Tx}
    (hN : ∀ n, T = .bitVector n → x.ty = .bitVector n → N = n ∧ Tx = .bitVector n)
    (hc : s = true → 1 < N) :
    Refines FS (.mk (.binop (.mulOvf s) (.mk (.bitVec z) T) x) .bool)
      (mulOvfConst O s N z (.mk x.kind Tx)) := by
  refine Refines.cmp_intro (.mulOvf s) (fun n wa wb hT => ?_)
    (fun n wa wb hT ρ Z Y v hx hy e => ?_)
  all_goals obtain ⟨rfl, rfl⟩ := hN n (BV_lit wa).1 wb.2.1
  all_goals rw [Term.mk_kind_of_ty wb.2.1]
  all_goals have hm := mulOvfConst_sound hO wa wb hc
  · exact hm.1
  · rw [lit_eval_eq wa hx] at e
    simp [evBinop, bvBin] at e; subst e
    exact hm.2 ρ Y hy

theorem bv_mul_overflows.r_const.proof : bv_mul_overflows.r_const.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_mul_overflows.r_const] at h
  rcases orElse_eq_some h with h | h <;> split at h
  all_goals try (simp at h; done)
  all_goals split at h
  all_goals try (simp at h; done)
  all_goals simp only [Option.some.injEq] at h; subst h
  all_goals rename_i hc
  all_goals simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_true_eq] at hc
  all_goals simp only [bv_mul_overflows.spec]
  · exact bv_mul_overflows.const_aux hO (fun n h _ => by simp [h])
      (fun h => by subst h; simpa [size] using hc)
  · exact Refines.trans (Refines.comm (.mulOvf s))
      (bv_mul_overflows.const_aux hO (fun n _ h => by simp [h])
        (fun h => by subst h; simpa [size] using hc))

theorem bv_mul_overflows.r_div.proof : bv_mul_overflows.r_div.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_mul_overflows.r_div] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp [equal] at h <;>
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h <;>
    refine Refines.cmp_intro (.mulOvf false) (fun n wa wb hT => ⟨v_false_WT, rfl⟩)
      (fun n wa wb hT ρ x y v hx hy e => ?_)
  · rename_i y' _
    obtain ⟨wy, wx, rfl⟩ := BV_arith_inv (.div false) wb
    rw [eval_arith (.div false) wy wx rfl] at hy
    obtain ⟨Y, X, hY, hX, hy⟩ := evBinop_inv (.inl (.div false)) wy wx hy
    rw [hx] at hX; simp at hX; subst hX
    simp [evBinop, bvBin] at hy e; subst hy; subst e
    rw [umul_mulOvf_div]; exact eval_v_false
  · rename_i y' _
    obtain ⟨wy, wx, rfl⟩ := BV_arith_inv (.div false) wa
    rw [eval_arith (.div false) wy wx rfl] at hx
    obtain ⟨Y, X, hY, hX, hx⟩ := evBinop_inv (.inl (.div false)) wy wx hx
    rw [hy] at hX; simp at hX; subst hX
    simp [evBinop, bvBin] at hx e; subst hx; subst e
    rw [umulOverflow_comm, umul_mulOvf_div]; exact eval_v_false

theorem bv_mul_overflows.r_default.proof : bv_mul_overflows.r_default.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_mul_overflows.r_default] at h; simp at h; subst h
  exact Refines.commut_binop (.mulOvf s)

theorem bv_neg_overflows.r_main.proof : bv_neg_overflows.r_main.Stmt := by
  intro FS O hO v res h
  simp only [bv_neg_overflows.r_main] at h; simp at h; subst h
  exact hO.sem_eq _ _

theorem bv_sub_overflows.r_lits.proof : bv_sub_overflows.r_lits.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_sub_overflows.r_lits] at h; split at h <;> simp at h; subst h
  refine Refines.cmp_intro (.subOvf s) (fun n wa wb hT => of_bool_BoolT _)
    (fun n wa wb hT ρ x y v hx hy e => ?_)
  obtain ⟨rfl, hz1⟩ := BV_lit wa; obtain ⟨-, hz2⟩ := BV_lit wb
  rw [lit_eval_eq wa hx, lit_eval_eq wb hy] at e
  simp [evBinop, bvBin] at e; subst e
  rw [size_of_ty_bitVector, overflows_sub_lit wa.2.2 hz1.1 hz1.2 hz2.1 hz2.2, eval_of_bool]

theorem bv_sub_overflows.r_same.proof : bv_sub_overflows.r_same.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_sub_overflows.r_same] at h; split at h <;> simp at h; subst h
  rename_i he; simp [equal] at he; subst he
  refine Refines.cmp_intro (.subOvf s) (fun n wa wb hT => ⟨v_false_WT, rfl⟩)
    (fun n wa wb hT ρ x y v hx hy e => ?_)
  rw [hx] at hy; simp at hy; subst hy
  simp [evBinop, bvBin] at e; subst e
  have := two_pow_pos' (n.toNat - 1)
  cases s <;> simp [ssub_ok, usub_ok] <;> omega

theorem bv_sub_overflows.r_unsigned.proof : bv_sub_overflows.r_unsigned.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_sub_overflows.r_unsigned] at h; split at h <;> simp at h; subst h
  rename_i hs; simp at hs; subst hs
  refine Refines.cmp_intro (.subOvf false) (fun n wa wb hT => (O_bv_lt hO wa wb).1)
    (fun n wa wb hT ρ x y v hx hy e => ?_)
  rw [(O_bv_lt hO wa wb).2 ρ x y hx hy]
  simp [evBinop, bvBin] at e; subst e
  simp [BitVec.usubOverflow, BitVec.ult]

theorem bv_sub_overflows.r_default.proof : bv_sub_overflows.r_default.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_sub_overflows.r_default] at h; simp at h; subst h
  exact Refines.refl

end Bvr
