import Bvr.Proofs.BitwiseLemmas

/-! Bitwise operations, extraction, extension, concatenation, shifts and conversions. -/

namespace Bvr

open Classical BitwiseL

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
  intro FS O hO v1 v2 res h
  simp only [bv_and.r_lshr_mask] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> obtain ⟨hc, rfl⟩ := h
  · rename_i X s T1 T mask T2
    obtain ⟨s0, s1, hm⟩ := hc
    refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
    · obtain ⟨n, hn, h1, h2, -, w1, w2⟩ := (BitOp.and (FS := FS)).WT.1 w
      simp only [Term.ty_mk] at h1; subst h1
      exact ⟨w1, by simp [bv_and.spec]⟩
    · obtain ⟨n, hn, h1, h2, -, w1, w2⟩ := (BitOp.and (FS := FS)).WT.1 w
      simp only [Term.ty_mk] at h1; subst h1
      obtain ⟨k, b, eb, rfl, m0, m1⟩ := BitOp.and.eval_lit_r e
      obtain ⟨k', Y, ey, hb, -, -⟩ := BitOp.lshr.eval_lit_r eb
      obtain ⟨rfl, rfl⟩ := Val.bv_inj hb
      obtain ⟨Y', hY⟩ := eval_bv eb (show (Term.mk _ (Ty.bitVector n)).ty = _ from rfl)
      have hk : n = k := by obtain ⟨h, -⟩ := Val.bv_inj hY; omega
      have s1' : s < n := by have := of_decide_eq_true s1; simpa using this
      have sk : s < 2 ^ k := by
        have := Nat.lt_two_pow_self (n := k); have := int_two_pow_cast k; omega
      simp only [size_of_ty_bitVector]
      rw [eb, BitVec.ushiftRight_eq', toNat_ofInt_lit s0 sk,
        lshr_mask_bits s0 m0 hk (of_decide_eq_true hm)]
  · rename_i mask T2 X s T1 T
    obtain ⟨s0, s1, hm⟩ := hc
    refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
    · obtain ⟨n, hn, h1, h2, -, w1, w2⟩ := (BitOp.and (FS := FS)).WT.1 w
      simp only [Term.ty_mk] at h1 h2; subst h1 h2
      exact ⟨w2, by simp [bv_and.spec]⟩
    · obtain ⟨n, hn, h1, h2, -, w1, w2⟩ := (BitOp.and (FS := FS)).WT.1 w
      simp only [Term.ty_mk] at h1 h2; subst h1 h2
      obtain ⟨k, b, eb, rfl, m0, m1⟩ := BitOp.and.eval_lit_l e
      obtain ⟨k', Y, ey, hb, -, -⟩ := BitOp.lshr.eval_lit_r eb
      obtain ⟨rfl, rfl⟩ := Val.bv_inj hb
      obtain ⟨Y', hY⟩ := eval_bv eb (show (Term.mk _ (Ty.bitVector n)).ty = _ from rfl)
      have hk : n = k := by obtain ⟨h, -⟩ := Val.bv_inj hY; omega
      have s1' : s < n := by have := of_decide_eq_true s1; simpa using this
      have sk : s < 2 ^ k := by
        have := Nat.lt_two_pow_self (n := k); have := int_two_pow_cast k; omega
      simp only [size_of_ty_bitVector]
      rw [eb, BitVec.ushiftRight_eq', toNat_ofInt_lit s0 sk, BitVec.and_comm,
        lshr_mask_bits s0 m0 hk (of_decide_eq_true hm)]

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
  intro FS O hO v1 v2 res h
  simp only [bv_and.r_mask_or_mask] at h
  have C := fun {n} (x y : BitVec n) => BitVec.and_comm x y
  have Co := fun {n} (x y : BitVec n) => BitVec.or_comm x y
  have chain : ∀ M N P X : Term,
      Refines FS (bv_or.spec (bv_and.spec M N) (bv_and.spec X (bv_and.spec M P)))
        (O.bv_or (O.bv_and M N) (O.bv_and X (O.bv_and M P))) := fun M N P X =>
    Refines.trans (Refines.binop_ty (fun a => ty a) (fun a b h => h) (hO.bv_and _ _)
      (Refines.trans (Refines.binop_ty (fun a => .bitVector (size a))
        (fun a b h => by simp [size, ty, h]) Refines.refl (hO.bv_and _ _)) (hO.bv_and _ _)))
      (hO.bv_or _ _)
  rcases orElse_eq_some8 h with h | h | h | h | h | h | h | h <;> split at h <;>
    (try simp at h) <;> (try simp only [Option.some.injEq] at h) <;> subst h <;>
    refine Refines.trans ?_ (chain _ _ _ _)
  · exact and_mask_or_mask (fun k h1 _ => h1)
  · exact Refines.trans (BitOp.and.congr Refines.refl
      (BitOp.or.congr Refines.refl (BitOp.and.comm C))) (and_mask_or_mask (fun k h1 _ => h1))
  · exact Refines.trans (BitOp.and.congr Refines.refl (BitOp.or.comm Co)) (and_mask_or_mask (fun k h1 _ => h1))
  · exact Refines.trans (BitOp.and.congr Refines.refl (Refines.trans (BitOp.or.comm Co)
      (BitOp.or.congr Refines.refl (BitOp.and.comm C)))) (and_mask_or_mask (fun k h1 _ => h1))
  · exact Refines.trans (BitOp.and.comm C) (and_mask_or_mask (fun k _ h2 => h2))
  · exact Refines.trans (BitOp.and.comm C) (Refines.trans (BitOp.and.congr Refines.refl
      (BitOp.or.congr Refines.refl (BitOp.and.comm C))) (and_mask_or_mask (fun k _ h2 => h2)))
  · exact Refines.trans (BitOp.and.comm C) (Refines.trans
      (BitOp.and.congr Refines.refl (BitOp.or.comm Co)) (and_mask_or_mask (fun k _ h2 => h2)))
  · exact Refines.trans (BitOp.and.comm C) (Refines.trans (BitOp.and.congr Refines.refl
      (Refines.trans (BitOp.or.comm Co) (BitOp.or.congr Refines.refl (BitOp.and.comm C))))
      (and_mask_or_mask (fun k _ h2 => h2)))

theorem bv_and.r_mask_or.proof : bv_and.r_mask_or.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_and.r_mask_or] at h
  have C := fun {n} (x y : BitVec n) => BitVec.and_comm x y
  have Co := fun {n} (x y : BitVec n) => BitVec.or_comm x y
  rcases orElse_eq_some4 h with h | h | h | h <;> split at h <;> (try simp at h) <;>
    (try simp only [Option.some.injEq] at h) <;> subst h
  all_goals
    split
    · rename_i hmo; (try simp only [decide_eq_true_eq] at hmo)
      first
        | exact and_lit_or_lit_abs (fun n ht => by simpa using ht) hmo
        | exact Refines.trans (BitOp.and.congr Refines.refl (BitOp.or.comm Co))
            (and_lit_or_lit_abs (fun n ht => by simpa using ht) hmo)
        | exact Refines.trans (BitOp.and.comm C)
            (and_lit_or_lit_abs (fun n ht => by simpa using ht) hmo)
        | exact Refines.trans (BitOp.and.comm C) (Refines.trans
            (BitOp.and.congr Refines.refl (BitOp.or.comm Co))
            (and_lit_or_lit_abs (fun n ht => by simpa using ht) hmo))
    split
    · rename_i hmo; (try simp only [decide_eq_true_eq] at hmo)
      refine Refines.trans ?_ (hO.bv_and _ _)
      first
        | exact and_lit_or_lit_zero (fun n ht => by simpa using ht) hmo
        | exact Refines.trans (BitOp.and.congr Refines.refl (BitOp.or.comm Co))
            (and_lit_or_lit_zero (fun n ht => by simpa using ht) hmo)
        | exact Refines.trans (BitOp.and.comm C)
            (and_lit_or_lit_zero (fun n ht => by simpa using ht) hmo)
        | exact Refines.trans (BitOp.and.comm C) (Refines.trans
            (BitOp.and.congr Refines.refl (BitOp.or.comm Co))
            (and_lit_or_lit_zero (fun n ht => by simpa using ht) hmo))
    · exact BitOp.and.commut C

theorem bv_and.r_right_mask.proof : bv_and.r_right_mask.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_and.r_right_mask] at h
  have chain : ∀ M l r : Term, Refines FS (bv_and.spec (bv_and.spec M l) (bv_and.spec M r))
      (O.bv_and (O.bv_and M l) (O.bv_and M r)) := fun M l r =>
    Refines.trans (Refines.binop_ty (fun a => .bitVector (size a)) (fun a b h => by simp [h])
      (hO.bv_and _ _) (hO.bv_and _ _)) (hO.bv_and _ _)
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> obtain ⟨-, rfl⟩ := h
  · exact Refines.trans (and_mask_and (Or.inl ⟨rfl, rfl⟩) (fun n h _ => by simp [h])) (chain _ _ _)
  · exact Refines.trans (and_mask_and (Or.inr ⟨rfl, rfl⟩) (fun n _ h => by simp [h])) (chain _ _ _)

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
  intro FS O hO v1 v2 res h
  simp only [bv_and.r_ites] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i b1 l1 z1 T3 T1 b2 l2 z2 T4 T2 hz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hz
  obtain ⟨rfl, rfl⟩ := hz
  have chain : Refines FS (b_ite.spec (b_and.spec b1 b2) (bv_and.spec l1 l2)
      (bv_zero (size (Term.mk (.triop .ite b1 l1 (.mk (.bitVec 0) T3)) T1))))
      (O.b_ite (O.b_and b1 b2) (O.bv_and l1 l2)
        (bv_zero (size (Term.mk (.triop .ite b1 l1 (.mk (.bitVec 0) T3)) T1)))) :=
    Refines.trans (Refines.ite (hO.b_and _ _) (hO.bv_and _ _) Refines.refl
      (t' := ty (O.bv_and l1 l2)) (fun w => by
        have := ty_of_refines (hO.bv_and l1 l2) (WT_triop.1 w).2.2.1; simp [this]))
      (hO.b_ite _ _ _)
  refine Refines.trans ?_ chain
  have key : (bv_and.spec (.mk (.triop .ite b1 l1 (.mk (.bitVec 0) T3)) T1)
      (.mk (.triop .ite b2 l2 (.mk (.bitVec 0) T4)) T2)).WT → ∃ n : Int, 0 < n ∧
      T1 = .bitVector n ∧ T2 = .bitVector n ∧ T3 = .bitVector n ∧ T4 = .bitVector n ∧
      l1.ty = .bitVector n ∧ l2.ty = .bitVector n ∧ b1.ty = .bool ∧ b2.ty = .bool ∧
      b1.WT ∧ b2.WT ∧ l1.WT ∧ l2.WT := by
    intro w
    obtain ⟨n, hn, h1, h2, -, w1, w2⟩ := (BitOp.and (FS := FS)).WT.1 w
    obtain ⟨g1, r1, t1, wg1, wl1, -⟩ := WT_ite.1 w1
    obtain ⟨g2, r2, t2, wg2, wl2, -⟩ := WT_ite.1 w2
    simp only [Term.ty_mk] at h1 h2 r1 r2; subst h1 h2
    exact ⟨n, hn, rfl, rfl, r1.trans t1.symm, r2.trans t2.symm, t1.symm, t2.symm, g1, g2, wg1, wg2,
      wl1, wl2⟩
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨n, hn, rfl, rfl, rfl, rfl, hl1, hl2, g1, g2, wg1, wg2, wl1, wl2⟩ := key w
    refine ⟨WT_ite.2 ⟨by simp [b_and.spec], by simp [bv_and.spec, hl1], by simp [b_ite.spec],
      WT_and.2 ⟨g1, g2, rfl, wg1, wg2⟩,
      (BitOp.and (FS := FS)).WT.2 ⟨n, hn, hl1, hl2, by simp [hl1], wl1, wl2⟩,
      bv_zero_WT (by simp; omega)⟩, by simp [b_ite.spec, bv_and.spec, hl1]⟩
  · obtain ⟨n, hn, rfl, rfl, rfl, rfl, hl1, hl2, g1, g2, wg1, wg2, wl1, wl2⟩ := key w
    obtain ⟨k, x, y, ex, ey, rfl⟩ := BitOp.and.eval_eq_some e
    obtain ⟨c1, ec1, ex'⟩ := eval_ite_eq_some ex
    obtain ⟨c2, ec2, ey'⟩ := eval_ite_eq_some ey
    obtain ⟨-, wc, wa, wz⟩ := WT_triop.1 w'
    simp only [b_ite.spec] at w' ⊢
    rw [eval_ite w', b_and.spec, eval_binop wc, ec1, ec2]
    have hz : ∀ {T : Ty} {k : Nat} {x : BitVec k}, T = .bitVector n →
        eval FS ρ (.mk (.bitVec 0) T) = some (.bv k x) → x = 0 := by
      intro T k x hT e0; obtain ⟨rfl, rfl⟩ := lit_val e0 hT; simp
    obtain ⟨z0, hz0⟩ := eval_bv ex rfl
    obtain ⟨rfl, rfl⟩ := Val.bv_inj hz0
    cases c1 <;> cases c2 <;> simp only [evBinop, pand, ↓reduceIte, Bool.false_eq_true] at ex' ey' ⊢
    · rw [hz rfl ex', eval_bv_zero (by simp; omega)]; simp
    · rw [hz rfl ex', eval_bv_zero (by simp; omega)]; simp
    · rw [hz rfl ey', eval_bv_zero (by simp; omega)]; simp
    · simp only [bv_and.spec] at wa ⊢
      rw [BitOp.and.eval_of wa ex' ey']

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
  intro FS O hO v1 v2 res h
  simp only [bv_or.r_extend_shl] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  rename_i nx base T1 k tail T4 s T5 T2 hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; obtain ⟨hs, hnx⟩ := hc
  simp only [Option.some.injEq] at h; subst h
  simp only [bv_or.spec, ty, Term.ty_mk]
  split
  · rename_i h1; simp only [decide_eq_true_eq] at h1
    refine Refines.trans ?_ (hO.bv_concat _ _)
    refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
    · obtain ⟨nb, nt, hnb, hnt, hb, ht, -, hk, hsum, hT1, -, wb, wt⟩ := extend_shl_WT w
      simp only [size, ty, ht, size_of_ty] at h1
      refine ⟨WT_concat.2 ⟨nt, nb, hnt, hnb, ht, hb, by simp [size, ty, ht, hb, size_of_ty], wt, wb⟩, ?_⟩
      simp [bv_concat.spec, size, ty, ht, hb, size_of_ty, hT1]; omega
    · obtain ⟨nb, nt, xb, xt, N, Y, hN, hnb, hnt, hb, ht, -, hk, hsum, hT1, eb, et, rfl, hY⟩ :=
        extend_shl_eval hs e
      simp only [size, ty, ht, size_of_ty] at h1
      rw [bv_concat.spec, eval_concat_of w' et eb]
      congr 1
      apply Val.bv_ext (by omega)
      intro i hi
      rw [hY, BitVec.getLsbD_append]
      have : i < N := by omega
      simp [this]
  · rename_i h1; simp only [decide_eq_true_eq] at h1
    split
    · rename_i h2; simp only [decide_eq_true_eq] at h2
      refine Refines.trans ?_ (Refines.trans (Refines.unop_ty
        (fun a => .bitVector (size a + (nx - size tail))) (fun x y h => by simp [size, ty, h])
        (hO.bv_concat tail base)) (hO.bv_extend _ _ _))
      refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
      · obtain ⟨nb, nt, hnb, hnt, hb, ht, -, hk, hsum, hT1, -, wb, wt⟩ := extend_shl_WT w
        simp only [size, ty, ht, size_of_ty] at h1 h2 ⊢
        refine ⟨WT_extend.2 ⟨nt + nb, by omega, by simp [bv_concat.spec, size, ty, ht, hb,
          size_of_ty], by omega, by simp [bv_concat.spec, size, ty, ht, hb, size_of_ty], WT_concat.2 ⟨nt, nb, hnt, hnb, ht, hb,
          by simp [size, ty, ht, hb, size_of_ty], wt, wb⟩⟩, ?_⟩
        simp [bv_concat.spec, size, ty, ht, hb, size_of_ty, hT1]; omega
      · obtain ⟨nb, nt, xb, xt, N, Y, hN, hnb, hnt, hb, ht, -, hk, hsum, hT1, eb, et, rfl, hY⟩ :=
          extend_shl_eval hs e
        simp only [size, ty, ht, size_of_ty] at h1 h2 w' ⊢
        rw [eval_extend_of w' (eval_concat_of (WT_unop.1 w').2 et eb)]
        congr 1
        apply Val.bv_ext (by omega)
        intro i hi
        rw [hY]
        simp only [Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_setWidth,
          BitVec.getLsbD_append]
        have h3 : i < N := by omega
        simp [h3, hi]
    · rename_i h2; simp only [decide_eq_true_eq] at h2
      refine Refines.trans ?_ (Refines.trans (Refines.binop_ty2
        (fun a b => .bitVector (size a + size b)) (fun x x' y y' h h' => by simp [size, ty, h, h'])
        (hO.bv_extract 0 (nx - 1) tail) Refines.refl) (hO.bv_concat _ _))
      refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
      · obtain ⟨nb, nt, hnb, hnt, hb, ht, -, hk, hsum, hT1, -, wb, wt⟩ := extend_shl_WT w
        simp only [size, ty, ht, size_of_ty] at h1 h2 ⊢
        refine ⟨WT_concat.2 ⟨nx, nb, hnx, hnb, by simp [bv_extract.spec], hb,
          by simp [bv_extract.spec, size, ty, hb, size_of_ty],
          WT_extract.2 ⟨nt, ht, by omega, by omega, by omega, by simp, wt⟩, wb⟩, ?_⟩
        simp [bv_extract.spec, size, ty, hb, size_of_ty, hT1]; omega
      · obtain ⟨nb, nt, xb, xt, N, Y, hN, hnb, hnt, hb, ht, -, hk, hsum, hT1, eb, et, rfl, hY⟩ :=
          extend_shl_eval hs e
        simp only [size, ty, ht, size_of_ty] at h1 h2 w' ⊢
        rw [eval_concat_of w' (eval_extract_of (WT_binop.1 w').2.1 et) eb]
        congr 1
        apply Val.bv_ext (by omega)
        intro i hi
        rw [hY]
        simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
        have h3 : i < N := by omega
        have h4 : nx - 1 - 0 + 1 = nx := by omega
        simp only [h3, h4, decide_true, Bool.true_and, Int.toNat_zero, Nat.zero_add]
        split
        · rfl
        · have : i - nb.toNat < nx.toNat := by omega
          simp [this]

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

theorem bv_shl.r_lits.proof : bv_shl.r_lits.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_shl.r_lits] at h
  split at h <;> simp at h; subst h
  exact BitOp.shl.lits' (fun n h => by simp [h]) (fun n _ _ l0 _ r0 r1 => ofInt_zshiftl l0 r0 r1)

theorem bv_shl.r_zero.proof : bv_shl.r_zero.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_shl.r_zero] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  rename_i z T2 hz
  simp only [decide_eq_true_eq] at hz; subst hz
  simp only [Option.some.injEq] at h; subst h
  exact BitOp.shl.lit_r (fun n y _ _ _ => by simp)

theorem bv_shl.r_big.proof : bv_shl.r_big.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_shl.r_big] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i s T2 hs
  simp only [decide_eq_true_eq, ge_iff_le] at hs
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := (BitOp.shl (FS := FS)).WT.1 w
    exact ⟨bv_zero_WT (by simp [h1]; omega), by simp [bv_shl.spec, h1]⟩
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := (BitOp.shl (FS := FS)).WT.1 w
    obtain ⟨k, x, ex, rfl, s0, s1⟩ := BitOp.shl.eval_lit_r e
    obtain ⟨y, hy⟩ := eval_bv ex h1
    simp only [size_eq, h1, size_of_ty_bitVector] at hs ⊢
    obtain ⟨rfl, rfl⟩ := Val.bv_inj hy
    rw [eval_bv_zero hn]
    congr 1
    apply Val.bv_ext rfl
    intro t ht
    rw [BitVec.shiftLeft_eq', toNat_ofInt_lit s0 s1]
    bitw_simp

theorem bv_shl.r_shl.proof : bv_shl.r_shl.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_shl.r_shl] at h
  split at h <;> simp at h; subst h
  rename_i v s1 T1 T2 s2 T3
  exact Refines.trans (BitOp.shl.shift_shift (g := fun N => zmin (s1 + s2) N)
    (fun k _ x s10 s11 s20 s21 => shl_shl_lits x s10 s11 s20 s21)) (hO.bv_shl _ _)

theorem bv_shl.r_lshr.proof : bv_shl.r_lshr.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_shl.r_lshr] at h
  split at h
  case h_2 => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i x sr T1 T sl T2
  have key : (bv_shl.spec (.mk (.binop .lShr x (.mk (.bitVec sr) T1)) T) (.mk (.bitVec sl) T2)).WT →
      ∃ n : Int, 0 < n ∧ x.ty = .bitVector n ∧ T1 = .bitVector n ∧ T = .bitVector n ∧
        T2 = .bitVector n ∧ x.WT ∧ 0 ≤ sr ∧ sr < 2 ^ n.toNat ∧ 0 ≤ sl ∧ sl < 2 ^ n.toNat := by
    intro w
    obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := (BitOp.shl (FS := FS)).WT.1 w
    obtain ⟨n', hn', h1', h2', ht', w1', w2'⟩ := (BitOp.lshr (FS := FS)).WT.1 w1
    simp only [Term.ty_mk] at h1 h2 h2' ht'; subst h1
    simp only [Ty.bitVector.injEq] at ht'; subst ht'
    exact ⟨n, hn, h1', h2', rfl, h2, w1', (lit_inv w2' n h2').2.1, (lit_inv w2' n h2').2.2, (lit_inv w2 n h2).2.1,
      (lit_inv w2 n h2).2.2⟩
  have sem : ∀ ρ u, eval FS ρ (bv_shl.spec (.mk (.binop .lShr x (.mk (.bitVec sr) T1)) T)
      (.mk (.bitVec sl) T2)) = some u → ∃ n : Int, ∃ X : BitVec n.toNat,
        eval FS ρ x = some (.bv n.toNat X) ∧ 0 < n ∧ x.ty = .bitVector n ∧ T = .bitVector n ∧
        0 ≤ sr ∧ sr < 2 ^ n.toNat ∧ 0 ≤ sl ∧ sl < 2 ^ n.toNat ∧
        u = .bv n.toNat ((X >>> sr.toNat) <<< sl.toNat) := by
    intro ρ u e
    obtain ⟨n, hn, h1, _, h2, _, _, s0, s1, l0, l1⟩ := key (eval_WT e)
    obtain ⟨k, y, ey, rfl, _, _⟩ := BitOp.shl.eval_lit_r e
    obtain ⟨k', X, ex, hy, _, _⟩ := BitOp.lshr.eval_lit_r ey
    obtain ⟨rfl, rfl⟩ := Val.bv_inj hy
    obtain ⟨X', hX⟩ := eval_bv ex h1
    obtain ⟨rfl, rfl⟩ := Val.bv_inj hX
    refine ⟨n, X, ex, hn, h1, h2, s0, s1, l0, l1, ?_⟩
    simp only [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', toNat_ofInt_lit s0 s1,
      toNat_ofInt_lit l0 l1]
  by_cases hs : sl ≤ sr
  · simp only [decide_eq_true hs, ↓reduceIte]
    refine Refines.trans ?_ (Refines.trans (Refines.binop_ty (fun a => .bitVector (size a))
      (fun a b h => by simp [h]) (hO.bv_lshr _ _) Refines.refl) (hO.bv_and _ _))
    refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
    · obtain ⟨n, hn, h1, -, rfl, -, wx, s0, s1, l0, l1⟩ := key w
      refine ⟨(BitOp.and (FS := FS)).WT.2 ⟨n, hn, by simp [bv_lshr.spec, h1], by simp [mk_bv], by simp [bv_lshr.spec, h1],
        (BitOp.lshr (FS := FS)).WT.2 ⟨n, hn, h1, by simp [mk_bv], h1, wx, mk_masked_WT (by simp; omega)⟩,
        mk_masked_WT (by simp; omega)⟩, by simp [bv_shl.spec, mk_bv, bv_lshr.spec, h1]⟩
    · obtain ⟨n, X, ex, hn, h1, rfl, s0, s1, l0, l1, rfl⟩ := sem ρ u e
      obtain ⟨_, w1, w2⟩ := WT_binop.1 w'
      simp only [size_eq, Term.ty_mk, size_of_ty_bitVector, bv_lshr.spec, ty_eq, h1] at w1 w2 w' ⊢
      have d0 : 0 ≤ sr - sl := by omega
      have d1 : sr - sl < 2 ^ n.toNat := by omega
      rw [BitOp.and.eval_of w' (BitOp.lshr.eval_of w1 ex (eval_mk_masked hn)) (eval_mk_masked hn)]
      congr 1
      apply Val.bv_ext rfl
      intro t ht
      simp only [BitVec.ushiftRight_eq', toNat_ofInt_lit d0 d1]
      by_cases hts : t < sl.toNat
      · bitw_simp
      · bitw_simp; congr 1; omega
  · simp only [decide_eq_false hs, Bool.false_eq_true, ↓reduceIte]
    refine Refines.trans ?_ (Refines.trans (Refines.binop_ty (fun a => ty a)
      (fun a b h => by simp [h]) (hO.bv_and _ _) Refines.refl) (hO.bv_shl _ _))
    refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
    · obtain ⟨n, hn, h1, -, rfl, -, wx, s0, s1, l0, l1⟩ := key w
      refine ⟨(BitOp.shl (FS := FS)).WT.2 ⟨n, hn, by simp [bv_and.spec, h1], by simp [mk_bv], by simp [bv_and.spec, h1],
        (BitOp.and (FS := FS)).WT.2 ⟨n, hn, h1, by simp [mk_bv], by simp [h1], wx, mk_masked_WT (by simp; omega)⟩,
        mk_masked_WT (by simp; omega)⟩, by simp [bv_shl.spec, mk_bv, bv_and.spec, h1]⟩
    · obtain ⟨n, X, ex, hn, h1, rfl, s0, s1, l0, l1, rfl⟩ := sem ρ u e
      obtain ⟨_, w1, w2⟩ := WT_binop.1 w'
      simp only [size_eq, Term.ty_mk, size_of_ty_bitVector, bv_and.spec, ty_eq, h1] at w1 w2 w' ⊢
      have d0 : 0 ≤ sl - sr := by omega
      have d1 : sl - sr < 2 ^ n.toNat := by omega
      rw [BitOp.shl.eval_of w' (BitOp.and.eval_of w1 ex (eval_mk_masked hn)) (eval_mk_masked hn)]
      congr 1
      apply Val.bv_ext rfl
      intro t ht
      simp only [BitVec.shiftLeft_eq', toNat_ofInt_lit d0 d1]
      by_cases hts : t < sl.toNat
      · by_cases hts2 : t < (sl - sr).toNat <;> bitw_simp
      · bitw_simp; congr 1; omega

theorem bv_shl.r_and_mask.proof : bv_shl.r_and_mask.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_shl.r_and_mask] at h
  have hd : ∀ {k} (X M Z : BitVec k), (X &&& M) <<< Z = (X <<< Z) &&& (M <<< Z) := by
    intro k X M Z; simp only [BitVec.shiftLeft_eq']; exact BitVec.shiftLeft_and_distrib _ _ _
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> subst h
  · rename_i x m T1 T s T2
    refine Refines.trans ?_ (Refines.trans (Refines.binop_ty (fun a => .bitVector (size a))
      (fun a b h => by simp [h]) (hO.bv_shl _ _) Refines.refl) (hO.bv_and _ _))
    refine shift_distrib BitOp.and BitOp.shl hd
      (fun w => ?_) (fun ρ k u e => ?_) (fun k m0 m1 s0 s1 => ofInt_zshiftl m0 s0 s1)
      (fun n h => by simp only [Term.ty_mk] at h; simp [h]) (fun n h => h)
      (fun n h => by simp [bv_shl.spec, h])
    · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := (BitOp.and (FS := FS)).WT.1 w
      exact ⟨ht.trans h1.symm, w1⟩
    · obtain ⟨n, X, ex, hv, m0, m1⟩ := BitOp.and.eval_lit_r e
      obtain ⟨rfl, rfl⟩ := Val.bv_inj hv
      exact ⟨X, ex, rfl, m0, m1⟩
  · rename_i m T1 x T s T2
    refine Refines.trans ?_ (Refines.trans (Refines.binop_ty (fun a => .bitVector (size a))
      (fun a b h => by simp [h]) (hO.bv_shl _ _) Refines.refl) (hO.bv_and _ _))
    refine shift_distrib BitOp.and BitOp.shl hd
      (fun w => ?_) (fun ρ k u e => ?_) (fun k m0 m1 s0 s1 => ofInt_zshiftl m0 s0 s1)
      (fun n h => by simp only [Term.ty_mk] at h; simp [h]) (fun n h => h)
      (fun n h => by simp [bv_shl.spec, h])
    · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := (BitOp.and (FS := FS)).WT.1 w
      exact ⟨ht.trans h2.symm, w2⟩
    · obtain ⟨n, X, ex, hv, m0, m1⟩ := BitOp.and.eval_lit_l e
      obtain ⟨rfl, rfl⟩ := Val.bv_inj hv
      exact ⟨X, ex, BitVec.and_comm _ _, m0, m1⟩

theorem bv_shl.r_or_mask.proof : bv_shl.r_or_mask.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_shl.r_or_mask] at h
  have hd : ∀ {k} (X M Z : BitVec k), (X ||| M) <<< Z = (X <<< Z) ||| (M <<< Z) := by
    intro k X M Z; simp only [BitVec.shiftLeft_eq']; exact BitVec.shiftLeft_or_distrib _ _ _
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> subst h
  · rename_i x m T1 T s T2
    refine Refines.trans ?_ (Refines.trans (Refines.binop_ty (fun a => ty a)
      (fun a b h => by simp [h]) (hO.bv_shl _ _) Refines.refl) (hO.bv_or _ _))
    refine shift_distrib BitOp.or BitOp.shl hd
      (fun w => ?_) (fun ρ k u e => ?_) (fun k m0 m1 s0 s1 => ofInt_zshiftl m0 s0 s1)
      (fun n h => by simp only [Term.ty_mk] at h; simp [h]) (fun n h => h)
      (fun n h => by simp [bv_shl.spec, h])
    · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := (BitOp.or (FS := FS)).WT.1 w
      exact ⟨ht.trans h1.symm, w1⟩
    · obtain ⟨n, X, ex, hv, m0, m1⟩ := BitOp.or.eval_lit_r e
      obtain ⟨rfl, rfl⟩ := Val.bv_inj hv
      exact ⟨X, ex, rfl, m0, m1⟩
  · rename_i m T1 x T s T2
    refine Refines.trans ?_ (Refines.trans (Refines.binop_ty (fun a => ty a)
      (fun a b h => by simp [h]) (hO.bv_shl _ _) Refines.refl) (hO.bv_or _ _))
    refine shift_distrib BitOp.or BitOp.shl hd
      (fun w => ?_) (fun ρ k u e => ?_) (fun k m0 m1 s0 s1 => ofInt_zshiftl m0 s0 s1)
      (fun n h => by simp only [Term.ty_mk] at h; simp [h]) (fun n h => h)
      (fun n h => by simp [bv_shl.spec, h])
    · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := (BitOp.or (FS := FS)).WT.1 w
      exact ⟨ht.trans h2.symm, w2⟩
    · obtain ⟨n, X, ex, hv, m0, m1⟩ := BitOp.or.eval_lit_l e
      obtain ⟨rfl, rfl⟩ := Val.bv_inj hv
      exact ⟨X, ex, BitVec.or_comm _ _, m0, m1⟩

theorem bv_shl.r_default.proof : bv_shl.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp [bv_shl.r_default] at h; subst h; exact Refines.refl

theorem bv_lshr.r_lits.proof : bv_lshr.r_lits.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_lshr.r_lits] at h
  split at h <;> simp at h; subst h
  exact BitOp.lshr.lits' (fun n h => by simp [h]) (fun n _ _ l0 l1 r0 r1 => ofInt_zasr l0 l1 r0 r1)

theorem bv_lshr.r_zero.proof : bv_lshr.r_zero.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_lshr.r_zero] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  rename_i z T2 hz
  simp only [decide_eq_true_eq] at hz; subst hz
  simp only [Option.some.injEq] at h; subst h
  exact BitOp.lshr.lit_r (fun n y _ _ _ => by simp)

theorem bv_lshr.r_big.proof : bv_lshr.r_big.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_lshr.r_big] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i s T2 hs
  simp only [decide_eq_true_eq, ge_iff_le] at hs
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := (BitOp.lshr (FS := FS)).WT.1 w
    exact ⟨bv_zero_WT (by simp [h1]; omega), by simp [bv_lshr.spec, h1]⟩
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := (BitOp.lshr (FS := FS)).WT.1 w
    obtain ⟨k, x, ex, rfl, s0, s1⟩ := BitOp.lshr.eval_lit_r e
    obtain ⟨y, hy⟩ := eval_bv ex h1
    simp only [size_eq, h1, size_of_ty_bitVector] at hs ⊢
    obtain ⟨rfl, rfl⟩ := Val.bv_inj hy
    rw [eval_bv_zero hn]
    congr 1
    apply Val.bv_ext rfl
    intro t ht
    rw [BitVec.ushiftRight_eq', toNat_ofInt_lit s0 s1]
    bitw_simp

theorem bv_lshr.r_lshr.proof : bv_lshr.r_lshr.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_lshr.r_lshr] at h
  split at h <;> simp at h; subst h
  rename_i v s1 T1 T2 s2 T3
  exact Refines.trans (BitOp.lshr.shift_shift (g := fun N => zmin (s1 + s2) N)
    (fun k _ x s10 s11 s20 s21 => lshr_lshr_lits x s10 s11 s20 s21)) (hO.bv_lshr _ _)

theorem bv_lshr.r_and_mask.proof : bv_lshr.r_and_mask.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_lshr.r_and_mask] at h
  have hd : ∀ {k} (X M Z : BitVec k), (X &&& M) >>> Z = (X >>> Z) &&& (M >>> Z) := by
    intro k X M Z; simp only [BitVec.ushiftRight_eq']; exact BitVec.ushiftRight_and_distrib _ _ _
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> subst h
  · rename_i x m T1 T s T2
    refine Refines.trans ?_ (Refines.trans (Refines.binop_ty (fun a => .bitVector (size a))
      (fun a b h => by simp [h]) (hO.bv_lshr _ _) Refines.refl) (hO.bv_and _ _))
    refine shift_distrib BitOp.and BitOp.lshr hd
      (fun w => ?_) (fun ρ k u e => ?_) (fun k m0 m1 s0 s1 => ofInt_zasr m0 m1 s0 s1)
      (fun n h => by simp only [Term.ty_mk] at h; simp [h]) (fun n h => h)
      (fun n h => by simp [bv_lshr.spec, h])
    · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := (BitOp.and (FS := FS)).WT.1 w
      exact ⟨ht.trans h1.symm, w1⟩
    · obtain ⟨n, X, ex, hv, m0, m1⟩ := BitOp.and.eval_lit_r e
      obtain ⟨rfl, rfl⟩ := Val.bv_inj hv
      exact ⟨X, ex, rfl, m0, m1⟩
  · rename_i m T1 x T s T2
    refine Refines.trans ?_ (Refines.trans (Refines.binop_ty (fun a => .bitVector (size a))
      (fun a b h => by simp [h]) (hO.bv_lshr _ _) Refines.refl) (hO.bv_and _ _))
    refine shift_distrib BitOp.and BitOp.lshr hd
      (fun w => ?_) (fun ρ k u e => ?_) (fun k m0 m1 s0 s1 => ofInt_zasr m0 m1 s0 s1)
      (fun n h => by simp only [Term.ty_mk] at h; simp [h]) (fun n h => h)
      (fun n h => by simp [bv_lshr.spec, h])
    · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := (BitOp.and (FS := FS)).WT.1 w
      exact ⟨ht.trans h2.symm, w2⟩
    · obtain ⟨n, X, ex, hv, m0, m1⟩ := BitOp.and.eval_lit_l e
      obtain ⟨rfl, rfl⟩ := Val.bv_inj hv
      exact ⟨X, ex, BitVec.and_comm _ _, m0, m1⟩

theorem bv_lshr.r_or_mask.proof : bv_lshr.r_or_mask.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_lshr.r_or_mask] at h
  have hd : ∀ {k} (X M Z : BitVec k), (X ||| M) >>> Z = (X >>> Z) ||| (M >>> Z) := by
    intro k X M Z; simp only [BitVec.ushiftRight_eq']; exact BitVec.ushiftRight_or_distrib _ _ _
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> subst h
  · rename_i x m T1 T s T2
    refine Refines.trans ?_ (Refines.trans (Refines.binop_ty (fun a => ty a)
      (fun a b h => by simp [h]) (hO.bv_lshr _ _) Refines.refl) (hO.bv_or _ _))
    refine shift_distrib BitOp.or BitOp.lshr hd
      (fun w => ?_) (fun ρ k u e => ?_) (fun k m0 m1 s0 s1 => ofInt_zasr m0 m1 s0 s1)
      (fun n h => by simp only [Term.ty_mk] at h; simp [h]) (fun n h => h)
      (fun n h => by simp [bv_lshr.spec, h])
    · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := (BitOp.or (FS := FS)).WT.1 w
      exact ⟨ht.trans h1.symm, w1⟩
    · obtain ⟨n, X, ex, hv, m0, m1⟩ := BitOp.or.eval_lit_r e
      obtain ⟨rfl, rfl⟩ := Val.bv_inj hv
      exact ⟨X, ex, rfl, m0, m1⟩
  · rename_i m T1 x T s T2
    refine Refines.trans ?_ (Refines.trans (Refines.binop_ty (fun a => ty a)
      (fun a b h => by simp [h]) (hO.bv_lshr _ _) Refines.refl) (hO.bv_or _ _))
    refine shift_distrib BitOp.or BitOp.lshr hd
      (fun w => ?_) (fun ρ k u e => ?_) (fun k m0 m1 s0 s1 => ofInt_zasr m0 m1 s0 s1)
      (fun n h => by simp only [Term.ty_mk] at h; simp [h]) (fun n h => h)
      (fun n h => by simp [bv_lshr.spec, h])
    · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := (BitOp.or (FS := FS)).WT.1 w
      exact ⟨ht.trans h2.symm, w2⟩
    · obtain ⟨n, X, ex, hv, m0, m1⟩ := BitOp.or.eval_lit_l e
      obtain ⟨rfl, rfl⟩ := Val.bv_inj hv
      exact ⟨X, ex, BitVec.or_comm _ _, m0, m1⟩

theorem bv_lshr.r_default.proof : bv_lshr.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp [bv_lshr.r_default] at h; subst h; exact Refines.refl

theorem bv_ashr.r_lits.proof : bv_ashr.r_lits.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_ashr.r_lits] at h
  split at h <;> simp at h; subst h
  exact BitOp.ashr.lits' (fun n h => by simp [h]) (fun n h hn l0 l1 r0 r1 => by
    simp only [h, size_of_ty_bitVector]
    rw [show n = (n.toNat : Int) by omega] at *
    simp only [Int.toNat_natCast] at *
    exact ofInt_zasr_signed (by omega) l0 l1 r0 r1)

theorem bv_ashr.r_zero.proof : bv_ashr.r_zero.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_ashr.r_zero] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  rename_i z T2 hz
  simp only [decide_eq_true_eq] at hz; subst hz
  simp only [Option.some.injEq] at h; subst h
  exact BitOp.ashr.lit_r (fun n y _ _ _ => by simp [BitVec.sshiftRight_eq'])

theorem bv_ashr.r_big.proof : bv_ashr.r_big.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_ashr.r_big] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i s T2 hs
  simp only [decide_eq_true_eq, ge_iff_le] at hs
  refine Refines.trans ?_ (hO.bv_ashr _ _)
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := (BitOp.ashr (FS := FS)).WT.1 w
    refine ⟨(BitOp.ashr (FS := FS)).WT.2 ⟨n, hn, h1, by simp [h1], ht, w1, mk_masked_WT (by simp [h1]; omega)⟩,
      rfl⟩
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := (BitOp.ashr (FS := FS)).WT.1 w
    obtain ⟨k, x, ex, rfl, s0, s1⟩ := BitOp.ashr.eval_lit_r e
    obtain ⟨y, hy⟩ := eval_bv ex h1
    simp only [size_eq, h1, size_of_ty_bitVector] at hs w' ⊢
    obtain ⟨rfl, rfl⟩ := Val.bv_inj hy
    simp only [bv_ashr.spec] at w' ⊢
    rw [BitOp.ashr.eval_of w' ex (eval_mk_masked hn)]
    congr 1
    apply Val.bv_ext rfl
    intro t ht
    have m0 : 0 ≤ n - 1 := by omega
    have m1 : n - 1 < 2 ^ n.toNat := by
      have := Nat.lt_two_pow_self (n := n.toNat); have := int_two_pow_cast n.toNat; omega
    simp only [BitVec.sshiftRight_eq', toNat_ofInt_lit s0 s1, toNat_ofInt_lit m0 m1]
    by_cases ht0 : t = 0
    · subst ht0; bitw_simp; congr 1; omega
    · bitw_simp

theorem bv_ashr.r_ashr.proof : bv_ashr.r_ashr.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_ashr.r_ashr] at h
  split at h <;> simp at h; subst h
  rename_i v s1 T1 T2 s2 T3
  exact Refines.trans (BitOp.ashr.shift_shift (g := fun N => zmin (s1 + s2) (N - 1))
    (fun k hk x s10 s11 s20 s21 => ashr_ashr_lits hk x s10 s11 s20 s21)) (hO.bv_ashr _ _)

theorem bv_ashr.r_default.proof : bv_ashr.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp [bv_ashr.r_default] at h; subst h; exact Refines.refl

end Bvr
