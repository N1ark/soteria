import Bvr.Proofs.BitwiseLemmas

/-! Bitwise operations, extraction, extension, concatenation, shifts and conversions. -/

namespace Bvr

open Classical BitwiseL

theorem bv_of_bool.r_true_.proof : bv_of_bool.r_true_.Stmt := by
  intro FS O hO n b res h
  simp only [bv_of_bool.r_true_] at h
  split at h <;> simp at h; subst h
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · have := (WT_unop.1 w).1; simp [Unop.WT] at this
    exact ⟨bv_one_WT this.1, by simp [bv_of_bool.spec]⟩
  · have := (WT_unop.1 w).1; simp [Unop.WT] at this
    rw [bv_of_bool.spec, eval_unop w, eval_bool this.2] at e
    simp [evUnop] at e; subst e; exact eval_bv_one this.1

theorem bv_of_bool.r_false_.proof : bv_of_bool.r_false_.Stmt := by
  intro FS O hO n b res h
  simp only [bv_of_bool.r_false_] at h
  split at h <;> simp at h; subst h
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · have := (WT_unop.1 w).1; simp [Unop.WT] at this
    exact ⟨bv_zero_WT this.1, by simp [bv_of_bool.spec]⟩
  · have := (WT_unop.1 w).1; simp [Unop.WT] at this
    rw [bv_of_bool.spec, eval_unop w, eval_bool this.2] at e
    simp [evUnop] at e; subst e; exact eval_bv_zero this.1

theorem bv_of_bool.r_default.proof : bv_of_bool.r_default.Stmt := by
  intro FS O hO n b res h
  simp [bv_of_bool.r_default] at h; subst h
  exact Refines.refl

theorem bv_to_bool.r_lit.proof : bv_to_bool.r_lit.Stmt := by
  intro FS O hO v res h
  simp only [bv_to_bool.r_lit] at h
  split at h <;> simp at h; subst h
  rename_i z T
  refine Refines.intro (fun w => ⟨of_bool_WT, by simp [bv_to_bool.spec]⟩) (fun ρ v w w' e => ?_)
  simp only [bv_to_bool.spec] at w e
  obtain ⟨_, w1⟩ := WT_unop.1 w
  obtain ⟨w2, w3, w4⟩ := WT_binop.1 w1
  obtain ⟨k, hk, hT, h0, h1⟩ := WT_bitVec.1 w3
  simp [Binop.WT] at w2
  rw [eval_unop w, eval_binop w1, eval_bitVec' w3 hT, eval_bv_zero' w4] at e
  rcases hT with rfl | rfl <;> simp [size_of_ty] at w2 e
  simp [evBinop, evUnop] at e
  subst e; simp; exact (ofInt_eq_zero_iff h0 h1).symm

theorem bv_to_bool.r_of_bool.proof : bv_to_bool.r_of_bool.Stmt := by
  intro FS O hO v res h
  simp only [bv_to_bool.r_of_bool] at h
  split at h <;> simp at h; subst h
  rename_i m b T
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · simp only [bv_to_bool.spec] at w
    have w1 := (WT_binop.1 (WT_unop.1 w).2).2.1
    have := WT_unop.1 w1; simp [Unop.WT] at this
    exact ⟨this.2, by simp [this.1.2.1, bv_to_bool.spec]⟩
  · simp only [bv_to_bool.spec] at w e
    obtain ⟨_, w1⟩ := WT_unop.1 w
    obtain ⟨_, w3, w4⟩ := WT_binop.1 w1
    have := (WT_unop.1 w3).1; simp [Unop.WT] at this
    obtain ⟨hm, -, rfl⟩ := this
    rw [eval_unop w, eval_binop w1, eval_unop w3, eval_bv_zero' w4] at e
    try simp only [ty_eq, Term.ty_mk, size_of_ty_bitVector] at e
    rcases eb : eval FS ρ b with _ | ⟨b | _ | _ | _ | _ | _⟩ <;> rw [eb] at e <;>
      simp [evUnop, evBinop] at e
    subst e; cases b <;> simp; omega

theorem bv_to_bool.r_default.proof : bv_to_bool.r_default.Stmt := by
  intro FS O hO v res h
  simp [bv_to_bool.r_default] at h; subst h
  refine Refines.trans ?_ (hO.b_not _)
  refine Refines.unop (hO.sem_eq _ _) (fun _ => rfl)

theorem bv_not_bool.r_lit.proof : bv_not_bool.r_lit.Stmt := by
  intro FS O hO v res h
  simp only [bv_not_bool.r_lit] at h
  split at h <;> simp at h; subst h
  rename_i z T
  have key : (bv_not_bool.spec (.mk (.bitVec z) T)).WT →
      ∃ k : Nat, 0 < k ∧ T = .bitVector k ∧ 0 ≤ z ∧ z < 2 ^ k := by
    intro w
    simp only [bv_not_bool.spec] at w
    obtain ⟨_, w1⟩ := WT_unop.1 w
    obtain ⟨w2, w3, _⟩ := WT_binop.1 w1
    obtain ⟨k, hk, hT, h0, h1⟩ := WT_bitVec.1 w3
    simp [Binop.WT] at w2
    rcases hT with rfl | rfl <;> simp [size_of_ty] at w2
    exact ⟨k, hk, rfl, h0, h1⟩
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨k, hk, rfl, _⟩ := key w
    split <;> simp [bv_not_bool.spec, size_of_ty, bv_one_WT, bv_zero_WT, hk]
  · obtain ⟨k, hk, rfl, h0, h1⟩ := key w
    rw [eval_eq_ev w] at e
    simp [bv_not_bool.spec, ev, size_of_ty, evBinop, evUnop, bv_zero, Ty.width] at e
    subst e
    split <;> simp_all [size_of_ty, eval_bv_one, eval_bv_zero, ofInt_eq_zero_iff' h0 h1]

theorem bv_not_bool.r_of_bool.proof : bv_not_bool.r_of_bool.Stmt := by
  intro FS O hO v res h
  simp only [bv_not_bool.r_of_bool] at h
  split at h <;> simp at h; subst h
  rename_i m g T
  refine Refines.trans ?_ (hO.bv_of_bool _ _)
  refine Refines.trans ?_ (Refines.unop (hO.b_not g) (fun _ => rfl))
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · simp only [bv_not_bool.spec] at w
    obtain ⟨_, w1⟩ := WT_unop.1 w
    obtain ⟨w2, w3, _⟩ := WT_binop.1 w1
    obtain ⟨w4, w5⟩ := WT_unop.1 w3
    simp [Unop.WT] at w4
    obtain ⟨hm, hg, rfl⟩ := w4
    refine ⟨WT_unop.2 ⟨?_, WT_unop.2 ⟨?_, w5⟩⟩, ?_⟩ <;>
      simp [Unop.WT, bv_of_bool.spec, b_not.spec, bv_not_bool.spec, hm, hg, size_of_ty]
  · simp only [bv_not_bool.spec] at w e
    obtain ⟨_, w1⟩ := WT_unop.1 w
    obtain ⟨w2, w3, _⟩ := WT_binop.1 w1
    obtain ⟨w4, w5⟩ := WT_unop.1 w3
    simp [Unop.WT] at w4
    obtain ⟨hm, hg, rfl⟩ := w4
    rw [eval_eq_ev w] at e; rw [eval_eq_ev w']
    simp [b_not.spec, ev, size_of_ty, bv_zero,
      Ty.width] at e ⊢
    rcases eg : ev FS ρ g with _ | ⟨b | _ | _ | _ | _ | _⟩ <;> rw [eg] at e <;>
      simp [evUnop, evBinop] at e
    subst e; cases b <;> simp [evUnop] <;> omega

theorem bv_not_bool.r_default.proof : bv_not_bool.r_default.Stmt := by
  intro FS O hO v res h
  simp [bv_not_bool.r_default] at h; subst h
  refine Refines.trans ?_ (hO.bv_of_bool _ _)
  exact Refines.unop (hO.sem_eq _ _) (fun _ => rfl)

theorem bv_not.r_lit.proof : bv_not.r_lit.Stmt := by
  intro FS O hO v res h
  simp only [bv_not.r_lit] at h
  split at h <;> simp at h
  subst h
  rename_i z T
  have key : (Term.mk (.unop .bvNot (.mk (.bitVec z) T)) T).WT →
      ∃ n : Nat, 0 < n ∧ T = .bitVector n ∧ 0 ≤ z ∧ z < 2 ^ n := by
    intro w
    have ⟨w1, w2⟩ := WT_unop.1 w
    obtain ⟨n, hn, hT, h1, h2⟩ := WT_bitVec.1 w2
    simp [Unop.WT] at w1
    rcases hT with rfl | rfl
    · exact ⟨n, hn, rfl, h1, h2⟩
    · simp at w1
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨n, hn, rfl, _, _⟩ := key (by simpa [bv_not.spec] using w)
    exact ⟨mk_masked_WT (by simp [size_of_ty]; omega), by simp [bv_not.spec, size_of_ty]⟩
  · simp only [bv_not.spec, ty_eq, Term.ty_mk] at w e
    obtain ⟨n, hn, rfl, _, _⟩ := key w
    rw [eval_unop w, eval_bitVec' (WT_unop.1 w).2 (Or.inl rfl)] at e
    simp only [size_of_ty]
    rw [eval_mk_masked (by omega)]
    simp [evUnop] at e; subst e
    simp [BitVec.ofInt_zlognot]

theorem bv_not.r_ite.proof : bv_not.r_ite.Stmt := by
  intro FS O hO v r h
  simp only [bv_not.r_ite] at h
  split at h <;> simp at h
  subst h
  rename_i b l r0 T
  have hl : ∀ t, Refines FS (.mk (.unop .bvNot l) t) (O.bv_not l) := fun t =>
    Refines.trans (Refines.unop Refines.refl (fun w => by
      have := (WT_unop.1 w).1; simp [Unop.WT] at this ⊢; grind)) (hO.bv_not l)
  have hr : ∀ t, Refines FS (.mk (.unop .bvNot r0) t) (O.bv_not r0) := fun t =>
    Refines.trans (Refines.unop Refines.refl (fun w => by
      have := (WT_unop.1 w).1; simp [Unop.WT] at this ⊢; grind)) (hO.bv_not r0)
  refine Refines.trans Refines.unop_ite ?_
  refine Refines.trans ?_ (hO.b_ite _ _ _)
  refine Refines.ite Refines.refl (hl _) (hr _) (fun w => ?_)
  have ⟨h1, _, wa, _⟩ := WT_triop.1 w
  have := ((hl _).syn wa).2
  simp_all [b_ite.spec]

theorem bv_not.r_default.proof : bv_not.r_default.Stmt := by
  intro FS O hO v r h
  simp [bv_not.r_default] at h; subst h
  exact Refines.refl

theorem bv_and.r_lits.proof : bv_and.r_lits.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_and.r_lits] at h
  split at h <;> simp at h; subst h
  exact BitOp.and.lits (fun k _ l0 _ r0 _ => ofInt_zland l0 r0)

theorem bv_and.r_zero_l.proof : bv_and.r_zero_l.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_and.r_zero_l] at h
  split at h <;> simp at h
  obtain ⟨rfl, rfl⟩ := h
  exact BitOp.and.lit_l_abs (fun n y _ _ _ => by simp)

theorem bv_and.r_zero_r.proof : bv_and.r_zero_r.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_and.r_zero_r] at h
  split at h <;> simp at h
  obtain ⟨rfl, rfl⟩ := h
  exact BitOp.and.lit_r_abs (fun n y _ _ _ => by simp)

theorem bv_and.r_ones_l.proof : bv_and.r_ones_l.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_and.r_ones_l] at h
  split at h <;> (try split at h) <;> simp at h
  subst h; rename_i hm
  refine BitOp.and.lit_l (fun n y _ h1 _ => ?_)
  rw [covers_bitwidth_eq hm]; subst h1
  simp [ofInt_two_pow_sub_one]

theorem bv_and.r_ones_r.proof : bv_and.r_ones_r.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_and.r_ones_r] at h
  split at h <;> (try split at h) <;> simp at h
  subst h; rename_i hm
  refine BitOp.and.lit_r (fun n y _ h1 _ => ?_)
  rw [covers_bitwidth_eq hm]; simp only [size_eq, h1, size_of_ty_bitVector]
  simp [ofInt_two_pow_sub_one]

theorem bv_and.r_lshr_mask.proof : bv_and.r_lshr_mask.Stmt := by
  sorry

theorem bv_and.r_ite_r.proof : bv_and.r_ite_r.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_and.r_ite_r] at h
  split at h <;> simp at h; subst h
  exact Refines.trans BitOp.and.ite_r (Refines.ite_O hO (hO.bv_and _ _) (hO.bv_and _ _))

theorem bv_and.r_ite_l.proof : bv_and.r_ite_l.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_and.r_ite_l] at h
  split at h <;> simp at h; subst h
  have rt : ∀ {a c : Term} {t}, Refines FS (.mk (.binop .bitAnd a c) t) (O.bv_and a c) :=
    fun {a c t} => Refines.trans (Refines.retype (fun w => by
      obtain ⟨n, _, h1, _, ht, _⟩ := (@BitOp.and FS).WT.1 w; simp [h1, ht])) (hO.bv_and a c)
  exact Refines.trans BitOp.and.ite_l (Refines.ite_O hO rt rt)

theorem bv_and.r_masks.proof : bv_and.r_masks.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_and.r_masks] at h
  rcases orElse_eq_some4 h with h | h | h | h <;> split at h <;> simp at h <;> subst h
  all_goals
    refine Refines.trans ?_ (hO.bv_and _ _)
    have C := fun {n} (x y : BitVec n) => BitVec.and_comm x y
    first
      | exact (BitOp.and.lit_assoc (fun x y z => BitVec.and_assoc x y z) C
          (fun n ht => by simp_all) (fun n hx => by simp_all)
          (fun k c10 c20 => ofInt_zland c10 c20))
      | exact Refines.trans (BitOp.and.congr Refines.refl (BitOp.and.comm C)) (BitOp.and.lit_assoc (fun x y z => BitVec.and_assoc x y z) C
          (fun n ht => by simp_all) (fun n hx => by simp_all)
          (fun k c10 c20 => ofInt_zland c10 c20))
      | exact Refines.trans (BitOp.and.comm C) (BitOp.and.lit_assoc (fun x y z => BitVec.and_assoc x y z) C
          (fun n ht => by simp_all) (fun n hx => by simp_all)
          (fun k c10 c20 => ofInt_zland c10 c20))
      | exact Refines.trans (BitOp.and.comm C)
          (Refines.trans (BitOp.and.congr Refines.refl (BitOp.and.comm C)) (BitOp.and.lit_assoc (fun x y z => BitVec.and_assoc x y z) C
          (fun n ht => by simp_all) (fun n hx => by simp_all)
          (fun k c10 c20 => ofInt_zland c10 c20)))

theorem bv_and.r_mask_or_mask.proof : bv_and.r_mask_or_mask.Stmt := by
  sorry

theorem bv_and.r_mask_or.proof : bv_and.r_mask_or.Stmt := by
  sorry

theorem bv_and.r_right_mask.proof : bv_and.r_right_mask.Stmt := by
  sorry

theorem bv_and.r_of_bool_r.proof : bv_and.r_of_bool_r.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_and.r_of_bool_r] at h
  split at h <;> (try split at h) <;> simp at h
  subst h; rename_i h1; simp only [decide_eq_true_eq] at h1; subst h1
  refine BitOp.and.lit_l_of (fun ρ n y hn _ _ eb => ?_)
  rcases eval_bvOfBool_val eb with rfl | rfl <;> simp

theorem bv_and.r_of_bool_l.proof : bv_and.r_of_bool_l.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_and.r_of_bool_l] at h
  split at h <;> (try split at h) <;> simp at h
  subst h; rename_i h1; simp only [decide_eq_true_eq] at h1; subst h1
  refine BitOp.and.lit_r_of (fun ρ n y hn _ _ eb => ?_)
  rcases eval_bvOfBool_val eb with rfl | rfl <;> simp

theorem bv_and.r_of_bools.proof : bv_and.r_of_bools.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_and.r_of_bools] at h
  split at h <;> simp at h; subst h
  refine Refines.trans ?_ (hO.bv_of_bool _ _)
  refine Refines.trans ?_ (Refines.unop (hO.b_and _ _) (fun _ => rfl))
  refine BitOp.and.of_bools (fun a b => a && b) (fun n h1 _ => by simp [h1])
    (fun w1 w2 g1 g2 => ⟨WT_and.2 ⟨g1, g2, rfl, w1, w2⟩, rfl⟩)
    (fun ρ x1 x2 g1 g2 e1 e2 => ?_) (fun k x1 x2 _ => by cases x1 <;> cases x2 <;> simp)
  rw [b_and.spec, eval_binop (WT_and.2 ⟨g1, g2, rfl, eval_WT e1, eval_WT e2⟩), e1, e2]
  cases x1 <;> cases x2 <;> rfl

theorem bv_and.r_ites.proof : bv_and.r_ites.Stmt := by
  sorry

theorem bv_and.r_default.proof : bv_and.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp [bv_and.r_default] at h; subst h
  exact BitOp.and.commut BitVec.and_comm

theorem bv_or.r_lits.proof : bv_or.r_lits.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_or.r_lits] at h
  split at h <;> simp at h; subst h
  exact BitOp.or.lits (fun k _ l0 _ r0 _ => ofInt_zlor l0 r0)

theorem bv_or.r_zero_l.proof : bv_or.r_zero_l.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_or.r_zero_l] at h
  split at h <;> simp at h
  obtain ⟨rfl, rfl⟩ := h
  exact BitOp.or.lit_l (fun n y _ _ _ => by simp)

theorem bv_or.r_zero_r.proof : bv_or.r_zero_r.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_or.r_zero_r] at h
  split at h <;> simp at h
  obtain ⟨rfl, rfl⟩ := h
  exact BitOp.or.lit_r (fun n y _ _ _ => by simp)

theorem bv_or.r_same.proof : bv_or.r_same.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_or.r_same] at h
  split at h <;> simp at h
  rename_i he; simp only [equal, decide_eq_true_eq] at he; subst he h
  exact BitOp.or.same (fun _ => BitVec.or_self)

theorem bv_or.r_mask_and.proof : bv_or.r_mask_and.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_or.r_mask_and] at h
  have key : ∀ {m1 m2 : Int}, zland m1 m2 = m2 → ∀ {k} (y z : BitVec k), 0 ≤ m1 → 0 ≤ m2 →
      (y = z &&& BitVec.ofInt k m2 ∨ y = BitVec.ofInt k m2 &&& z) →
      BitVec.ofInt k m1 ||| y = BitVec.ofInt k m1 := by
    intro m1 m2 hm k y z h0 h1 hy
    have := BitVec.or_and_absorb (by rw [← ofInt_zland h0 h1, hm]) z
    rcases hy with rfl | rfl
    · exact this.1
    · exact this.2
  rcases orElse_eq_some4 h with h | h | h | h <;>
    split at h <;> (try split at h) <;> simp at h <;> subst h <;> rename_i hm
  all_goals
    simp only [decide_eq_true_eq] at hm
    first
      | refine BitOp.or.lit_l_abs_of (fun n h1 h2 h3 => by simp_all)
          (fun ρ n y hn h0 h1 h2 eb => ?_)
      | refine Refines.trans (BitOp.or.comm (fun x y => BitVec.or_comm x y))
          (BitOp.or.lit_l_abs_of (fun n h1 h2 h3 => by simp_all) (fun ρ n y hn h0 h1 h2 eb => ?_))
    obtain ⟨k, z, u, ez, eu, hy⟩ := BitOp.and.eval_eq_some eb
    simp at hy; obtain ⟨rfl, hy⟩ := hy; subst hy
    first
      | (obtain ⟨rfl, u0, _⟩ := lit_val₀ eu; exact key hm _ z h0 u0 (Or.inl rfl))
      | (obtain ⟨rfl, u0, _⟩ := lit_val₀ ez; exact key hm _ u h0 u0 (Or.inr rfl))

theorem bv_or.r_masks.proof : bv_or.r_masks.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_or.r_masks] at h
  rcases orElse_eq_some4 h with h | h | h | h <;> split at h <;> simp at h <;> subst h
  all_goals
    refine Refines.trans ?_ (hO.bv_or _ _)
    have C := fun {n} (x y : BitVec n) => BitVec.or_comm x y
    first
      | exact (BitOp.or.lit_assoc (fun x y z => BitVec.or_assoc x y z) C
          (fun n ht => by simp_all) (fun n hx => by simp_all)
          (fun k c10 c20 => ofInt_zlor c10 c20))
      | exact Refines.trans (BitOp.or.congr Refines.refl (BitOp.or.comm C)) (BitOp.or.lit_assoc (fun x y z => BitVec.or_assoc x y z) C
          (fun n ht => by simp_all) (fun n hx => by simp_all)
          (fun k c10 c20 => ofInt_zlor c10 c20))
      | exact Refines.trans (BitOp.or.comm C) (BitOp.or.lit_assoc (fun x y z => BitVec.or_assoc x y z) C
          (fun n ht => by simp_all) (fun n hx => by simp_all)
          (fun k c10 c20 => ofInt_zlor c10 c20))
      | exact Refines.trans (BitOp.or.comm C)
          (Refines.trans (BitOp.or.congr Refines.refl (BitOp.or.comm C)) (BitOp.or.lit_assoc (fun x y z => BitVec.or_assoc x y z) C
          (fun n ht => by simp_all) (fun n hx => by simp_all)
          (fun k c10 c20 => ofInt_zlor c10 c20)))

theorem bv_or.r_extend_shl.proof : bv_or.r_extend_shl.Stmt := by
  sorry

theorem bv_or.r_of_bools.proof : bv_or.r_of_bools.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_or.r_of_bools] at h
  split at h <;> simp at h; subst h
  refine Refines.trans ?_ (hO.bv_of_bool _ _)
  refine Refines.trans ?_ (Refines.unop (hO.b_or _ _) (fun _ => rfl))
  refine BitOp.or.of_bools (fun a b => a || b) (fun n _ h => h)
    (fun w1 w2 g1 g2 => ⟨?_, rfl⟩)
    (fun ρ x1 x2 g1 g2 e1 e2 => ?_) (fun k x1 x2 _ => by cases x1 <;> cases x2 <;> simp)
  · simp [b_or.spec, WT_binop, Binop.WT, g1, g2, w1, w2]
  · rw [b_or.spec, eval_binop (by simp [WT_binop, Binop.WT, g1, g2, eval_WT e1, eval_WT e2]),
      e1, e2]
    cases x1 <;> cases x2 <;> rfl

theorem bv_or.r_default.proof : bv_or.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp [bv_or.r_default] at h; subst h
  exact BitOp.or.commut BitVec.or_comm

theorem bv_xor.r_lits.proof : bv_xor.r_lits.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_xor.r_lits] at h
  split at h <;> simp at h; subst h
  exact BitOp.xor.lits (fun k _ l0 _ r0 _ => ofInt_zlxor l0 r0)

theorem bv_xor.r_zero_l.proof : bv_xor.r_zero_l.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_xor.r_zero_l] at h
  split at h <;> simp at h
  obtain ⟨rfl, rfl⟩ := h
  exact BitOp.xor.lit_l (fun n y _ _ _ => by simp)

theorem bv_xor.r_zero_r.proof : bv_xor.r_zero_r.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_xor.r_zero_r] at h
  split at h <;> simp at h
  obtain ⟨rfl, rfl⟩ := h
  exact BitOp.xor.lit_r (fun n y _ _ _ => by simp)

theorem bv_xor.r_of_bools.proof : bv_xor.r_of_bools.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_xor.r_of_bools] at h
  split at h <;> simp at h; subst h
  rename_i n b1 T1 m b2 T2
  refine Refines.trans ?_ (hO.bv_of_bool _ _)
  refine Refines.trans ?_ (Refines.unop (Refines.trans
    (Refines.unop (hO.sem_eq _ _) (fun _ => rfl)) (hO.b_not _)) (fun _ => rfl))
  refine BitOp.xor.of_bools (fun a b => !(a == b)) (fun n _ h => h)
    (fun w1 w2 g1 g2 => ⟨?_, rfl⟩)
    (fun ρ x1 x2 g1 g2 e1 e2 => ?_) (fun k x1 x2 hk => ?_)
  · simp [sem_eq.spec, WT_unop, WT_binop, Unop.WT, Binop.WT, g1, g2, w1, w2]
  · have wb : (sem_eq.spec b1 b2).WT := by
      simp [sem_eq.spec, WT_binop, Binop.WT, g1, g2, eval_WT e1, eval_WT e2]
    have wn : (b_not.spec (sem_eq.spec b1 b2)).WT := by
      simp only [b_not.spec]; exact WT_unop.2 ⟨by simp [Unop.WT, sem_eq.spec], wb⟩
    show eval FS ρ (b_not.spec (sem_eq.spec b1 b2)) = _
    simp only [b_not.spec] at wn ⊢
    rw [eval_unop wn]
    simp only [sem_eq.spec] at wb ⊢
    rw [eval_binop wb, e1, e2]
    cases x1 <;> cases x2 <;> simp [evUnop, evBinop]
  · cases x1 <;> cases x2 <;> simp

theorem bv_xor.r_default.proof : bv_xor.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp [bv_xor.r_default] at h; subst h
  exact BitOp.xor.commut BitVec.xor_comm

theorem bv_extract.r_lit.proof : bv_extract.r_lit.Stmt := by
  sorry

theorem bv_extract.r_full.proof : bv_extract.r_full.Stmt := by
  intro FS O hO i j v res h
  simp only [bv_extract.r_full] at h
  split at h <;> simp at h
  rename_i hij; simp only [Bool.and_eq_true, decide_eq_true_eq] at hij
  obtain ⟨rfl, rfl⟩ := hij; subst h
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨n, hv, _, _, _, _, wv⟩ := WT_extract.1 w
    refine ⟨wv, ?_⟩
    simp only [bv_extract.spec, size_eq, hv, size_of_ty_bitVector, Term.ty_mk, Ty.sort_eq]
    congr 1; omega
  · obtain ⟨n, x, hv, _, _, h2, _, ev, rfl⟩ := eval_extract e
    rw [ev]; congr 1
    have hs : size v = n := by simp [hv]
    apply Val.bv_ext (by omega)
    intro t ht; simp (disch := omega) only [BitVec.getLsbD_extractLsb', decide_eq_true, Bool.true_and, Nat.zero_add, Int.toNat_zero]

theorem bv_extract.r_and_.proof : bv_extract.r_and_.Stmt := by
  intro FS O hO i j v res h
  simp only [bv_extract.r_and_] at h
  split at h <;> simp at h; subst h
  rename_i a b T
  refine Refines.trans (BitOp.and.extract (fun _ _ _ _ => BitVec.extractLsb'_and)
    (T' := .bitVector (size (bv_extract.spec i j a))) rfl) ?_
  refine Refines.trans (Refines.binop_ty (fun x => .bitVector (size x)) (fun x y h => by simp [h])
    (hO.bv_extract _ _ _) (hO.bv_extract _ _ _)) (hO.bv_and _ _)

theorem bv_extract.r_or_.proof : bv_extract.r_or_.Stmt := by
  intro FS O hO i j v res h
  simp only [bv_extract.r_or_] at h
  split at h <;> simp at h; subst h
  rename_i a b T
  refine Refines.trans (BitOp.or.extract (fun _ _ _ _ => BitVec.extractLsb'_or)
    (T' := ty (bv_extract.spec i j a)) rfl) ?_
  refine Refines.trans (Refines.binop_ty (fun x => ty x) (fun x y h => by simp [h])
    (hO.bv_extract _ _ _) (hO.bv_extract _ _ _)) (hO.bv_or _ _)

theorem bv_extract.r_xor.proof : bv_extract.r_xor.Stmt := by
  intro FS O hO i j v res h
  simp only [bv_extract.r_xor] at h
  split at h <;> simp at h; subst h
  rename_i a b T
  refine Refines.trans (BitOp.xor.extract (fun _ _ _ _ => BitVec.extractLsb'_xor)
    (T' := ty (bv_extract.spec i j a)) rfl) ?_
  refine Refines.trans (Refines.binop_ty (fun x => ty x) (fun x y h => by simp [h])
    (hO.bv_extract _ _ _) (hO.bv_extract _ _ _)) (hO.bv_xor _ _)

theorem bv_extract.r_shl.proof : bv_extract.r_shl.Stmt := by
  intro FS O hO i j v res h
  simp only [bv_extract.r_shl] at h
  split at h <;> simp at h; subst h
  rename_i a s T2 T
  -- the shape of a well-typed spec
  have key : (bv_extract.spec i j (.mk (.binop .shl a (.mk (.bitVec s) T2)) T)).WT →
      ∃ n : Int, 0 < n ∧ a.ty = .bitVector n ∧ T2 = .bitVector n ∧ T = .bitVector n ∧
        0 ≤ i ∧ i ≤ j ∧ j < n ∧ a.WT ∧ 0 ≤ s ∧ s < 2 ^ n.toNat := by
    intro w
    obtain ⟨n, hb, h0, h1, h2, -, wb⟩ := WT_extract.1 w
    obtain ⟨n', hn', ha, h2', ht, wa, w2⟩ := (BitOp.shl (FS := FS)).WT.1 wb
    simp only [Term.ty_mk] at hb h2'; subst hb
    simp only [Ty.bitVector.injEq] at ht; subst ht
    exact ⟨n, hn', ha, h2', rfl, h0, h1, h2, wa, (lit_inv w2 n h2').2⟩
  have sem : ∀ ρ u, eval FS ρ (bv_extract.spec i j (.mk (.binop .shl a (.mk (.bitVec s) T2)) T)) =
      some u → ∃ n : Int, ∃ x : BitVec n.toNat, eval FS ρ a = some (.bv n.toNat x) ∧
        0 < n ∧ a.ty = .bitVector n ∧ 0 ≤ i ∧ i ≤ j ∧ j < n ∧ 0 ≤ s ∧ s < 2 ^ n.toNat ∧
        u = .bv (j - i + 1).toNat ((x <<< s.toNat).extractLsb' i.toNat _) := by
    intro ρ u e
    obtain ⟨n, x, hb, h0, h1, h2, -, eb, rfl⟩ := eval_extract e
    obtain ⟨k, y, ea, hx, s0, s1⟩ := BitOp.shl.eval_lit_r eb
    obtain ⟨rfl, rfl⟩ := Val.bv_inj hx
    obtain ⟨n', hn, ha, _, hT, _⟩ := key (eval_WT e)
    simp only [Term.ty_mk] at hb; rw [hT] at hb; simp only [Ty.bitVector.injEq] at hb; subst hb
    refine ⟨n', y, ea, hn, ha, h0, h1, h2, s0, s1, ?_⟩
    simp only [BitVec.shiftLeft_eq', toNat_ofInt_lit s0 s1]
  split
  · rename_i hs
    refine Refines.trans ?_ (hO.bv_extract _ _ _)
    refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
    · obtain ⟨n, hn, ha, -, -, h0, h1, h2, wa, s0, s1⟩ := key w
      refine ⟨WT_extract.2 ⟨n, ha, by omega, by omega, by omega, rfl, wa⟩, ?_⟩
      simp only [bv_extract.spec, Term.ty_mk, Ty.sort_eq]; congr 1; omega
    · obtain ⟨n, x, ea, hn, ha, h0, h1, h2, s0, s1, rfl⟩ := sem ρ u e
      simp only [bv_extract.spec] at w' ⊢
      rw [eval_extract_of w' ea]; congr 1
      apply Val.bv_ext (by omega)
      intro t ht
      bitw_simp
      congr 1; omega
  split
  · refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
    · obtain ⟨n, hn, ha, -, -, h0, h1, h2, wa, s0, s1⟩ := key w
      exact ⟨bv_zero_WT (by omega), rfl⟩
    · obtain ⟨n, x, ea, hn, ha, h0, h1, h2, s0, s1, rfl⟩ := sem ρ u e
      rw [eval_bv_zero (by omega)]; congr 1
      apply Val.bv_ext rfl
      intro t ht
      bitw_simp
  · rename_i hs1 hs2
    refine Refines.trans ?_ (Refines.trans (Refines.binop_ty2 (op := .bvConcat)
      (fun x y => .bitVector (size x + size y)) (fun x x' y y' h1 h2 => by simp [h1, h2])
      (hO.bv_extract _ _ _) Refines.refl) (hO.bv_concat _ _))
    refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
    · obtain ⟨n, hn, ha, -, -, h0, h1, h2, wa, s0, s1⟩ := key w
      refine ⟨WT_concat.2 ⟨j - s + 1, s - i, by omega, by omega, by simp [bv_extract.spec], rfl,
        by simp [bv_extract.spec] <;> omega,
        WT_extract.2 ⟨n, ha, by omega, by omega, by omega, by simp, wa⟩, bv_zero_WT (by omega)⟩, ?_⟩
      simp only [bv_extract.spec, Term.ty_mk, Ty.sort_eq, size_eq, bv_zero_ty, size_of_ty_bitVector]
      congr 1; omega
    · obtain ⟨n, x, ea, hn, ha, h0, h1, h2, s0, s1, rfl⟩ := sem ρ u e
      obtain ⟨_, w1, w2⟩ := WT_binop.1 w'
      simp only [bv_extract.spec] at w1 w' ⊢
      rw [eval_concat_of w' (eval_extract_of w1 ea) (eval_bv_zero (by omega))]; congr 1
      apply Val.bv_ext (by omega)
      intro t ht
      by_cases hts : t < (s - i).toNat
      · bitw_simp
      · bitw_simp; congr 1; omega

theorem bv_extract.r_lshr.proof : bv_extract.r_lshr.Stmt := by
  intro FS O hO i j v res h
  simp only [bv_extract.r_lshr] at h
  split at h
  case h_2 => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i a s T2 T
  have key : (bv_extract.spec i j (.mk (.binop .lShr a (.mk (.bitVec s) T2)) T)).WT →
      ∃ n : Int, 0 < n ∧ a.ty = .bitVector n ∧ T2 = .bitVector n ∧ T = .bitVector n ∧
        0 ≤ i ∧ i ≤ j ∧ j < n ∧ a.WT ∧ 0 ≤ s ∧ s < 2 ^ n.toNat := by
    intro w
    obtain ⟨n, hb, h0, h1, h2, -, wb⟩ := WT_extract.1 w
    obtain ⟨n', hn', ha, h2', ht, wa, w2⟩ := (BitOp.lshr (FS := FS)).WT.1 wb
    simp only [Term.ty_mk] at hb h2'; subst hb
    simp only [Ty.bitVector.injEq] at ht; subst ht
    exact ⟨n, hn', ha, h2', rfl, h0, h1, h2, wa, (lit_inv w2 n h2').2⟩
  have sem : ∀ ρ u, eval FS ρ (bv_extract.spec i j (.mk (.binop .lShr a (.mk (.bitVec s) T2)) T)) =
      some u → ∃ n : Int, ∃ x : BitVec n.toNat, eval FS ρ a = some (.bv n.toNat x) ∧
        0 < n ∧ a.ty = .bitVector n ∧ T = .bitVector n ∧ 0 ≤ i ∧ i ≤ j ∧ j < n ∧ 0 ≤ s ∧
        s < 2 ^ n.toNat ∧
        u = .bv (j - i + 1).toNat ((x >>> s.toNat).extractLsb' i.toNat _) := by
    intro ρ u e
    obtain ⟨n, x, hb, h0, h1, h2, -, eb, rfl⟩ := eval_extract e
    obtain ⟨k, y, ea, hx, s0, s1⟩ := BitOp.lshr.eval_lit_r eb
    obtain ⟨rfl, rfl⟩ := Val.bv_inj hx
    obtain ⟨n', hn, ha, _, hT, _⟩ := key (eval_WT e)
    simp only [Term.ty_mk] at hb; rw [hT] at hb; simp only [Ty.bitVector.injEq] at hb; subst hb
    refine ⟨n', y, ea, hn, ha, hT, h0, h1, h2, s0, s1, ?_⟩
    simp only [BitVec.ushiftRight_eq', toNat_ofInt_lit s0 s1]
  split
  · rename_i hs
    simp only [decide_eq_true_eq, ge_iff_le] at hs
    refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
    · obtain ⟨n, hn, ha, -, -, h0, h1, h2, wa, s0, s1⟩ := key w
      exact ⟨bv_zero_WT (by omega), rfl⟩
    · obtain ⟨n, x, ea, hn, ha, rfl, h0, h1, h2, s0, s1, rfl⟩ := sem ρ u e
      simp only [size_eq, Term.ty_mk, size_of_ty_bitVector] at hs
      rw [eval_bv_zero (by omega)]; congr 1
      apply Val.bv_ext rfl
      intro t ht
      bitw_simp
  rename_i hs1
  simp only [decide_eq_true_eq, ge_iff_le] at hs1
  by_cases hs2 : j + s < size (Term.mk (.binop .lShr a (.mk (.bitVec s) T2)) T)
  · simp only [decide_eq_true hs2, ↓reduceIte]
    refine Refines.trans ?_ (hO.bv_extract _ _ _)
    refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
    · obtain ⟨n, hn, ha, -, rfl, h0, h1, h2, wa, s0, s1⟩ := key w
      simp only [size_eq, Term.ty_mk, size_of_ty_bitVector] at hs1 hs2
      refine ⟨WT_extract.2 ⟨n, ha, by omega, by omega, by omega, rfl, wa⟩, ?_⟩
      simp only [bv_extract.spec, Term.ty_mk, Ty.sort_eq]; congr 1; omega
    · obtain ⟨n, x, ea, hn, ha, rfl, h0, h1, h2, s0, s1, rfl⟩ := sem ρ u e
      simp only [size_eq, Term.ty_mk, size_of_ty_bitVector] at hs1 hs2
      simp only [bv_extract.spec] at w' ⊢
      rw [eval_extract_of w' ea]; congr 1
      apply Val.bv_ext (by omega)
      intro t ht
      bitw_simp
      congr 1; omega
  · simp only [decide_eq_false hs2, Bool.false_eq_true, ↓reduceIte]
    refine Refines.trans ?_ (Refines.trans (Refines.binop_ty2 (op := .bvConcat)
      (fun x y => .bitVector (size x + size y)) (fun x x' y y' h1 h2 => by simp [h1, h2])
      Refines.refl (hO.bv_extract _ _ _)) (hO.bv_concat _ _))
    refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
    · obtain ⟨n, hn, ha, -, rfl, h0, h1, h2, wa, s0, s1⟩ := key w
      simp only [size_eq, Term.ty_mk, size_of_ty_bitVector] at hs1 hs2 ⊢
      refine ⟨WT_concat.2 ⟨j - (n - s - 1), n - 1 - (i + s) + 1, by omega, by omega, rfl,
        by simp [bv_extract.spec], by simp [bv_extract.spec] <;> omega,
        bv_zero_WT (by omega), WT_extract.2 ⟨n, ha, by omega, by omega, by omega, by simp, wa⟩⟩, ?_⟩
      simp only [bv_extract.spec, Term.ty_mk, Ty.sort_eq, size_eq, bv_zero_ty, size_of_ty_bitVector]
      congr 1; omega
    · obtain ⟨n, x, ea, hn, ha, rfl, h0, h1, h2, s0, s1, rfl⟩ := sem ρ u e
      simp only [size_eq, Term.ty_mk, size_of_ty_bitVector] at hs1 hs2 w' ⊢
      obtain ⟨_, w1, w2⟩ := WT_binop.1 w'
      simp only [bv_extract.spec] at w2 w' ⊢
      rw [eval_concat_of w' (eval_bv_zero (by omega)) (eval_extract_of w2 ea)]; congr 1
      apply Val.bv_ext (by omega)
      intro t ht
      by_cases hts : t < (n - 1 - (i + s) + 1).toNat
      · bitw_simp; congr 1; omega
      · bitw_simp

theorem bv_extract.r_ite.proof : bv_extract.r_ite.Stmt := by
  intro FS O hO i j v res h
  simp only [bv_extract.r_ite] at h
  split at h <;> simp at h; subst h
  exact Refines.trans Refines.unop_ite (Refines.ite_O hO (hO.bv_extract _ _ _) (hO.bv_extract _ _ _))

theorem bv_extract.r_zext_high.proof : bv_extract.r_zext_high.Stmt := by
  sorry

theorem bv_extract.r_sext_bit.proof : bv_extract.r_sext_bit.Stmt := by
  sorry

theorem bv_extract.r_ext_low.proof : bv_extract.r_ext_low.Stmt := by
  sorry

theorem bv_extract.r_ext_orig.proof : bv_extract.r_ext_orig.Stmt := by
  sorry

theorem bv_extract.r_extract.proof : bv_extract.r_extract.Stmt := by
  intro FS O hO i j v res h
  simp only [bv_extract.r_extract] at h
  split at h <;> simp at h; subst h
  rename_i pi pj a T
  refine Refines.trans ?_ (hO.bv_extract _ _ _)
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨m, hv, h0, h1, h2, -, wv⟩ := WT_extract.1 w
    obtain ⟨n, ha, h3, h4, h5, hT, wa⟩ := WT_extract.1 wv
    simp only [Term.ty_mk] at hv; subst hv; simp only [Ty.bitVector.injEq] at hT; subst hT
    refine ⟨WT_extract.2 ⟨n, ha, by omega, by omega, by omega, rfl, wa⟩, ?_⟩
    simp only [bv_extract.spec, Term.ty_mk, Ty.sort_eq]; congr 1; omega
  · obtain ⟨m, x, hv, h0, h1, h2, -, ev, rfl⟩ := eval_extract e
    obtain ⟨n, y, ha, h3, h4, h5, hT, ea, hx⟩ := eval_extract ev
    simp only [Term.ty_mk] at hv; subst hv; simp only [Ty.bitVector.injEq] at hT; subst hT
    obtain ⟨hw, rfl⟩ := Val.bv_inj hx
    simp only [bv_extract.spec] at w' ⊢
    rw [eval_extract_of w' ea]; congr 1
    apply Val.bv_ext (by omega)
    intro t ht
    simp only [BitVec.getLsbD_extractLsb']
    have e1 : (pi + i).toNat + t = pi.toNat + (i.toNat + t) := by omega
    rw [e1]
    simp (disch := omega) only [decide_eq_true, Bool.true_and]

theorem bv_extract.r_concat.proof : bv_extract.r_concat.Stmt := by
  sorry

theorem bv_extract.r_add_low.proof : bv_extract.r_add_low.Stmt := by
  sorry

theorem bv_extract.r_add_const.proof : bv_extract.r_add_const.Stmt := by
  sorry

theorem bv_extract.r_mul_pow2.proof : bv_extract.r_mul_pow2.Stmt := by
  sorry

theorem bv_extract.r_mul_low.proof : bv_extract.r_mul_low.Stmt := by
  sorry

theorem bv_extract.r_urem.proof : bv_extract.r_urem.Stmt := by
  sorry

theorem bv_extract.r_default.proof : bv_extract.r_default.Stmt := by
  intro FS O hO i j v res h
  simp [bv_extract.r_default] at h; subst h; exact Refines.refl

theorem bv_extend.r_lit.proof : bv_extend.r_lit.Stmt := by
  sorry

theorem bv_extend.r_extend.proof : bv_extend.r_extend.Stmt := by
  sorry

theorem bv_extend.r_ite.proof : bv_extend.r_ite.Stmt := by
  intro FS O hO s k v res h
  simp only [bv_extend.r_ite] at h
  split at h <;> simp at h; subst h
  have rt : ∀ {a : Term} {t}, Refines FS (.mk (.unop (.bvExtend s k) a) t) (O.bv_extend s k a) :=
    fun {a t} => Refines.trans (Refines.retype (fun w => by
      obtain ⟨n, _, h1, _, ht, _⟩ := WT_extend.1 w; simp [h1, ht])) (hO.bv_extend s k a)
  exact Refines.trans Refines.unop_ite (Refines.ite_O hO rt rt)

theorem bv_extend.r_of_bool.proof : bv_extend.r_of_bool.Stmt := by
  sorry

theorem bv_extend.r_default.proof : bv_extend.r_default.Stmt := by
  intro FS O hO s k v res h
  simp [bv_extend.r_default] at h; subst h; exact Refines.refl

theorem bv_concat.r_lits.proof : bv_concat.r_lits.Stmt := by
  sorry

theorem bv_concat.r_extracts.proof : bv_concat.r_extracts.Stmt := by
  sorry

theorem bv_concat.r_extract_extracts.proof : bv_concat.r_extract_extracts.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_concat.r_extract_extracts] at h
  split at h <;> simp at h; subst h; exact Refines.refl

theorem bv_concat.r_assoc_l.proof : bv_concat.r_assoc_l.Stmt := by
  sorry

theorem bv_concat.r_assoc_r.proof : bv_concat.r_assoc_r.Stmt := by
  sorry

theorem bv_concat.r_ites.proof : bv_concat.r_ites.Stmt := by
  sorry

theorem bv_concat.r_default.proof : bv_concat.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp [bv_concat.r_default] at h; subst h; exact Refines.refl

theorem bv_shl.r_lits.proof : bv_shl.r_lits.Stmt := by
  sorry

theorem bv_shl.r_zero.proof : bv_shl.r_zero.Stmt := by
  sorry

theorem bv_shl.r_big.proof : bv_shl.r_big.Stmt := by
  sorry

theorem bv_shl.r_shl.proof : bv_shl.r_shl.Stmt := by
  sorry

theorem bv_shl.r_lshr.proof : bv_shl.r_lshr.Stmt := by
  sorry

theorem bv_shl.r_and_mask.proof : bv_shl.r_and_mask.Stmt := by
  sorry

theorem bv_shl.r_or_mask.proof : bv_shl.r_or_mask.Stmt := by
  sorry

theorem bv_shl.r_default.proof : bv_shl.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp [bv_shl.r_default] at h; subst h; exact Refines.refl

theorem bv_lshr.r_lits.proof : bv_lshr.r_lits.Stmt := by
  sorry

theorem bv_lshr.r_zero.proof : bv_lshr.r_zero.Stmt := by
  sorry

theorem bv_lshr.r_big.proof : bv_lshr.r_big.Stmt := by
  sorry

theorem bv_lshr.r_lshr.proof : bv_lshr.r_lshr.Stmt := by
  sorry

theorem bv_lshr.r_and_mask.proof : bv_lshr.r_and_mask.Stmt := by
  sorry

theorem bv_lshr.r_or_mask.proof : bv_lshr.r_or_mask.Stmt := by
  sorry

theorem bv_lshr.r_default.proof : bv_lshr.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp [bv_lshr.r_default] at h; subst h; exact Refines.refl

theorem bv_ashr.r_lits.proof : bv_ashr.r_lits.Stmt := by
  sorry

theorem bv_ashr.r_zero.proof : bv_ashr.r_zero.Stmt := by
  sorry

theorem bv_ashr.r_big.proof : bv_ashr.r_big.Stmt := by
  sorry

theorem bv_ashr.r_ashr.proof : bv_ashr.r_ashr.Stmt := by
  sorry

theorem bv_ashr.r_default.proof : bv_ashr.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp [bv_ashr.r_default] at h; subst h; exact Refines.refl

theorem bv_of_float.r_lit.proof : bv_of_float.r_lit.Stmt := by
  intro FS O hO rm s n v res h
  simp only [bv_of_float.r_lit] at h
  split at h <;> simp at h; subst h
  rename_i f T
  rcases ez : O.orc.f_to_int rm s n f with _ | z
  · simp [firstSome]; exact Refines.refl
  · simp [firstSome]
    refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
    · have := (WT_unop.1 w).1; simp [Unop.WT] at this
      exact ⟨mk_masked_WT this.1, by simp [bv_of_float.spec]⟩
    · have ⟨w1, w2⟩ := WT_unop.1 w
      simp [Unop.WT] at w1
      have w3 := w2
      simp [Term.WT] at w3
      rw [bv_of_float.spec, eval_unop w, eval_eq_ev w2, ev] at e
      rw [eval_mk_masked w1.1]
      rw [hO.orc.to_int rm s n f z w3.2 w1.1 ez] at e
      exact e

theorem bv_of_float.r_default.proof : bv_of_float.r_default.Stmt := by
  intro FS O hO rm s n v res h
  simp [bv_of_float.r_default] at h; subst h; exact Refines.refl

theorem bv_to_float.r_lit.proof : bv_to_float.r_lit.Stmt := by
  intro FS O hO rm s p v res h
  simp only [bv_to_float.r_lit] at h
  split at h <;> simp at h; subst h
  rename_i z T
  rcases ez : O.orc.f_of_int rm s p (size_of_ty T) z with _ | f
  · simp [firstSome]; exact Refines.refl
  · simp [firstSome]
    have key : (bv_to_float.spec rm s p (.mk (.bitVec z) T)).WT →
        ∃ n : Int, 0 < n ∧ T = .bitVector n ∧ 0 ≤ z ∧ z < 2 ^ n.toNat := by
      intro w
      have ⟨w1, w2⟩ := WT_unop.1 w
      simp [Unop.WT] at w1
      obtain ⟨n, hn, rfl⟩ := w1
      exact ⟨n, hn, rfl, lit_inv w2 n rfl |>.2⟩
    refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
    · obtain ⟨n, hn, rfl, h0, h1⟩ := key w
      obtain ⟨hp, hf, _⟩ := hO.orc.of_int rm s p n z f hn h0 h1 ez
      refine ⟨?_, by simp [bv_to_float.spec, hp]⟩
      simp only [Term.WT, hp]; exact ⟨trivial, by simpa [FloatLit.WF, hp] using hf⟩
    · obtain ⟨n, hn, rfl, h0, h1⟩ := key w
      obtain ⟨hp, hf, he⟩ := hO.orc.of_int rm s p n z f hn h0 h1 ez
      rw [bv_to_float.spec, eval_unop w, eval_lit' (WT_unop.1 w).2 rfl, he] at e
      rw [eval_eq_ev w']; simp only [ev]; exact e

theorem bv_to_float.r_default.proof : bv_to_float.r_default.Stmt := by
  intro FS O hO rm s p v res h
  simp [bv_to_float.r_default] at h; subst h; exact Refines.refl

theorem bv_to_float_raw.r_lit.proof : bv_to_float_raw.r_lit.Stmt := by
  intro FS O hO v res h
  simp only [bv_to_float_raw.r_lit] at h
  split at h <;> simp at h; subst h
  rename_i z T
  simp only [bv_to_float_raw.spec, size_eq, Term.ty_mk]
  generalize fp_of_size (size_of_ty T) = p
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · refine ⟨?_, rfl⟩
    simp only [Term.WT, f_of_bits]
    refine ⟨trivial, ?_⟩
    have := emod_two_pow_lt z p.size
    have := emod_two_pow_nonneg z p.size
    have e1 : ((2 ^ p.size : Nat) : Int) = (2 : Int) ^ p.size := by push_cast; rfl
    omega
  · have ⟨w1, w2⟩ := WT_unop.1 w
    simp only [Unop.WT] at w1
    rw [eval_unop w, eval_lit' w2 w1.1] at e
    simp [evUnop] at e
    rw [eval_eq_ev w']; simp only [ev]; rw [← e]
    simp [FloatLit.sem, FloatLit.val, f_of_bits]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    have := emod_two_pow_lt z p.size
    have := emod_two_pow_nonneg z p.size
    have e1 : ((2 ^ p.size : Nat) : Int) = (2 : Int) ^ p.size := by push_cast; rfl
    rw [Nat.mod_eq_of_lt (by omega)]; simp

theorem bv_to_float_raw.r_default.proof : bv_to_float_raw.r_default.Stmt := by
  intro FS O hO v res h
  simp [bv_to_float_raw.r_default] at h; subst h; exact Refines.refl

end Bvr
