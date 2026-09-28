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

theorem bv_extract.r_lit.proof : bv_extract.r_lit.Stmt := by
  intro FS O hO i j v res h
  simp only [bv_extract.r_lit] at h
  split at h
  case h_2 => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i z T
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨n, hb, h0, h1, h2, -, wb⟩ := WT_extract.1 w
    exact ⟨mk_masked_WT (by omega), rfl⟩
  · obtain ⟨n, x, hb, h0, h1, h2, -, eb, rfl⟩ := eval_extract e
    obtain ⟨rfl, z0, z1⟩ := lit_val₀ eb
    rw [eval_mk_masked (by omega)]; congr 2
    simp only [zasr]
    rw [ofInt_div_two_pow _ z0, BitVec.extractLsb', toNat_ofInt_lit z0 z1]

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
  intro FS O hO i j v res h
  simp only [bv_extract.r_zext_high] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i k a T hs
  simp only [decide_eq_true_eq, ge_iff_le] at hs
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨m, hm, ha, hk, rfl, h0, h1, h2, wa⟩ := extract_extend_WT w
    exact ⟨bv_zero_WT (by omega), rfl⟩
  · obtain ⟨m, x, ea, hm, ha, hk, rfl, h0, h1, h2, rfl⟩ := extract_extend_eval e
    simp only [size_eq, Term.ty_mk, size_of_ty_bitVector] at hs
    rw [eval_bv_zero (by omega)]; congr 1
    apply Val.bv_ext rfl
    intro t ht
    bitw_simp

theorem bv_extract.r_sext_bit.proof : bv_extract.r_sext_bit.Stmt := by
  intro FS O hO i j v res h
  simp only [bv_extract.r_sext_bit] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i k a T hs
  simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le] at hs
  obtain ⟨hs, rfl⟩ := hs
  refine Refines.trans ?_ (hO.bv_extract _ _ _)
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨m, hm, ha, hk, rfl, h0, h1, h2, wa⟩ := extract_extend_WT w
    simp only [size_eq, Term.ty_mk, size_of_ty_bitVector, ha] at hs ⊢
    refine ⟨WT_extract.2 ⟨m, ha, by omega, by omega, by omega, rfl, wa⟩, ?_⟩
    simp [bv_extract.spec]
  · obtain ⟨m, x, ea, hm, ha, hk, rfl, h0, h1, h2, rfl⟩ := extract_extend_eval e
    simp only [size_eq, Term.ty_mk, size_of_ty_bitVector, ha] at hs w' ⊢
    simp only [bv_extract.spec] at w' ⊢
    rw [eval_extract_of w' ea]; congr 1
    apply Val.bv_ext (by omega)
    intro t ht
    bitw_simp
    congr 1; omega

theorem bv_extract.r_ext_low.proof : bv_extract.r_ext_low.Stmt := by
  intro FS O hO i j v res h
  simp only [bv_extract.r_ext_low] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i s k a T hs
  simp only [decide_eq_true_eq] at hs
  subst hs
  by_cases hj : j = size a - 1
  · simp only [decide_eq_true hj, ↓reduceIte]
    refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
    · obtain ⟨m, hm, ha, hk, rfl, h0, h1, h2, wa⟩ := extract_extend_WT w
      simp only [size_eq, ha, size_of_ty_bitVector] at hj
      refine ⟨wa, ?_⟩
      simp [bv_extract.spec, ha]; omega
    · obtain ⟨m, x, ea, hm, ha, hk, rfl, h0, h1, h2, rfl⟩ := extract_extend_eval e
      simp only [size_eq, ha, size_of_ty_bitVector] at hj
      rw [ea]; congr 1
      apply Val.bv_ext (by omega)
      intro t ht
      cases s <;> bitw_simp
  simp only [decide_eq_false hj, Bool.false_eq_true, ↓reduceIte]
  by_cases hj2 : j < size a
  · simp only [decide_eq_true hj2, ↓reduceIte]
    refine Refines.trans ?_ (hO.bv_extract _ _ _)
    refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
    · obtain ⟨m, hm, ha, hk, rfl, h0, h1, h2, wa⟩ := extract_extend_WT w
      simp only [size_eq, ha, size_of_ty_bitVector] at hj hj2
      exact ⟨WT_extract.2 ⟨m, ha, by omega, by omega, by omega, rfl, wa⟩, rfl⟩
    · obtain ⟨m, x, ea, hm, ha, hk, rfl, h0, h1, h2, rfl⟩ := extract_extend_eval e
      simp only [size_eq, ha, size_of_ty_bitVector] at hj hj2
      simp only [bv_extract.spec] at w' ⊢
      rw [eval_extract_of w' ea]; congr 1
      apply Val.bv_ext (by omega)
      intro t ht
      cases s <;> bitw_simp
  simp only [decide_eq_false hj2, Bool.false_eq_true, ↓reduceIte]
  refine Refines.trans ?_ (hO.bv_extend _ _ _)
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨m, hm, ha, hk, rfl, h0, h1, h2, wa⟩ := extract_extend_WT w
    simp only [size_eq, ha, size_of_ty_bitVector] at hj hj2 ⊢
    refine ⟨WT_extend.2 ⟨m, hm, ha, by omega, by simp [ha], wa⟩, ?_⟩
    simp [bv_extend.spec, bv_extract.spec, ha]; omega
  · obtain ⟨m, x, ea, hm, ha, hk, rfl, h0, h1, h2, rfl⟩ := extract_extend_eval e
    simp only [size_eq, ha, size_of_ty_bitVector] at hj hj2 w' ⊢
    simp only [bv_extend.spec] at w' ⊢
    rw [eval_extend_of w' ea]; congr 1
    apply Val.bv_ext (by omega)
    intro t ht
    cases s <;> bitw_simp

theorem bv_extract.r_ext_orig.proof : bv_extract.r_ext_orig.Stmt := by
  intro FS O hO i j v res h
  simp only [bv_extract.r_ext_orig] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i s k a T hs
  simp only [decide_eq_true_eq] at hs
  refine Refines.trans ?_ (hO.bv_extract _ _ _)
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨m, hm, ha, hk, rfl, h0, h1, h2, wa⟩ := extract_extend_WT w
    simp only [size_eq, Term.ty_mk, size_of_ty_bitVector, ha] at hs ⊢
    exact ⟨WT_extract.2 ⟨m, ha, by omega, by omega, by omega, rfl, wa⟩, rfl⟩
  · obtain ⟨m, x, ea, hm, ha, hk, rfl, h0, h1, h2, rfl⟩ := extract_extend_eval e
    simp only [size_eq, Term.ty_mk, size_of_ty_bitVector, ha] at hs w' ⊢
    simp only [bv_extract.spec] at w' ⊢
    rw [eval_extract_of w' ea]; congr 1
    apply Val.bv_ext (by omega)
    intro t ht
    cases s <;> bitw_simp

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
  intro FS O hO i j v res h
  simp only [bv_extract.r_concat] at h
  split at h
  case h_2 => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i l r T
  have key : (bv_extract.spec i j (.mk (.binop .bvConcat l r) T)).WT →
      ∃ n m : Int, 0 < n ∧ 0 < m ∧ l.ty = .bitVector n ∧ r.ty = .bitVector m ∧
        T = .bitVector (n + m) ∧ 0 ≤ i ∧ i ≤ j ∧ j < n + m ∧ l.WT ∧ r.WT := by
    intro w
    obtain ⟨k, hb, h0, h1, h2, -, wb⟩ := WT_extract.1 w
    obtain ⟨n, m, hn, hm, hl, hr, hT, wl, wr⟩ := WT_concat.1 wb
    simp only [Term.ty_mk] at hb; subst hT; simp only [Ty.bitVector.injEq] at hb; subst hb
    exact ⟨n, m, hn, hm, hl, hr, rfl, h0, h1, h2, wl, wr⟩
  have sem : ∀ ρ u, eval FS ρ (bv_extract.spec i j (.mk (.binop .bvConcat l r) T)) = some u →
      ∃ n m : Int, ∃ x : BitVec n.toNat, ∃ y : BitVec m.toNat,
        eval FS ρ l = some (.bv n.toNat x) ∧ eval FS ρ r = some (.bv m.toNat y) ∧
        0 < n ∧ 0 < m ∧ l.ty = .bitVector n ∧ r.ty = .bitVector m ∧
        T = .bitVector (n + m) ∧ 0 ≤ i ∧ i ≤ j ∧ j < n + m ∧
        u = .bv (j - i + 1).toNat ((x ++ y).extractLsb' i.toNat _) := by
    intro ρ u e
    obtain ⟨k, z, hb, h0, h1, h2, -, eb, rfl⟩ := eval_extract e
    obtain ⟨n, m, x, y, hn, hm, hl, hr, hT, el, er, hz⟩ := eval_concat eb
    simp only [Term.ty_mk] at hb; subst hT; simp only [Ty.bitVector.injEq] at hb; subst hb
    refine ⟨n, m, x, y, el, er, hn, hm, hl, hr, rfl, h0, h1, h2, ?_⟩
    apply Val.bv_ext rfl
    intro t ht
    simp only [BitVec.getLsbD_extractLsb']
    rw [Val.bv_getLsbD hz]
  by_cases hs1 : i ≥ size r
  · simp only [decide_eq_true hs1, ↓reduceIte]
    refine Refines.trans ?_ (hO.bv_extract _ _ _)
    refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
    · obtain ⟨n, m, hn, hm, hl, hr, rfl, h0, h1, h2, wl, wr⟩ := key w
      simp only [size_eq, hr, size_of_ty_bitVector] at hs1 ⊢
      refine ⟨WT_extract.2 ⟨n, hl, by omega, by omega, by omega, rfl, wl⟩, ?_⟩
      simp [bv_extract.spec]; omega
    · obtain ⟨n, m, x, y, el, er, hn, hm, hl, hr, rfl, h0, h1, h2, rfl⟩ := sem ρ u e
      simp only [size_eq, hr, size_of_ty_bitVector] at hs1 w' ⊢
      simp only [bv_extract.spec] at w' ⊢
      rw [eval_extract_of w' el]; congr 1
      apply Val.bv_ext (by omega)
      intro t ht
      bitw_simp; congr 1; omega
  simp only [decide_eq_false hs1, Bool.false_eq_true, ↓reduceIte]
  by_cases hs2 : j < size r
  · simp only [decide_eq_true hs2, ↓reduceIte]
    refine Refines.trans ?_ (hO.bv_extract _ _ _)
    refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
    · obtain ⟨n, m, hn, hm, hl, hr, rfl, h0, h1, h2, wl, wr⟩ := key w
      simp only [size_eq, hr, size_of_ty_bitVector] at hs1 hs2 ⊢
      exact ⟨WT_extract.2 ⟨m, hr, by omega, by omega, by omega, rfl, wr⟩, rfl⟩
    · obtain ⟨n, m, x, y, el, er, hn, hm, hl, hr, rfl, h0, h1, h2, rfl⟩ := sem ρ u e
      simp only [size_eq, hr, size_of_ty_bitVector] at hs1 hs2 w' ⊢
      simp only [bv_extract.spec] at w' ⊢
      rw [eval_extract_of w' er]; congr 1
      apply Val.bv_ext (by omega)
      intro t ht
      bitw_simp
  simp only [decide_eq_false hs2, Bool.false_eq_true, ↓reduceIte]
  refine Refines.trans ?_ (Refines.trans (Refines.binop_ty2 (op := .bvConcat)
    (fun x y => .bitVector (size x + size y)) (fun x x' y y' h1 h2 => by simp [h1, h2])
    (hO.bv_extract _ _ _) (hO.bv_extract _ _ _)) (hO.bv_concat _ _))
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨n, m, hn, hm, hl, hr, rfl, h0, h1, h2, wl, wr⟩ := key w
    simp only [size_eq, hr, size_of_ty_bitVector] at hs1 hs2 ⊢
    refine ⟨WT_concat.2 ⟨j - m + 1, m - 1 - i + 1, by omega, by omega,
      by simp [bv_extract.spec], by simp [bv_extract.spec],
      by simp [bv_extract.spec] <;> omega,
      WT_extract.2 ⟨n, hl, by omega, by omega, by omega, by simp, wl⟩,
      WT_extract.2 ⟨m, hr, by omega, by omega, by omega, by simp, wr⟩⟩, ?_⟩
    simp only [bv_extract.spec, Term.ty_mk, Ty.sort_eq, size_eq, size_of_ty_bitVector]
    congr 1; omega
  · obtain ⟨n, m, x, y, el, er, hn, hm, hl, hr, rfl, h0, h1, h2, rfl⟩ := sem ρ u e
    simp only [size_eq, hr, size_of_ty_bitVector] at hs1 hs2 w' ⊢
    obtain ⟨_, w1, w2⟩ := WT_binop.1 w'
    simp only [bv_extract.spec] at w1 w2 w' ⊢
    rw [eval_concat_of w' (eval_extract_of w1 el) (eval_extract_of w2 er)]; congr 1
    apply Val.bv_ext (by omega)
    intro t ht
    by_cases hts : t < (m - 1 - i + 1).toNat
    · bitw_simp
    · bitw_simp; congr 1; omega

theorem bv_extract.r_add_low.proof : bv_extract.r_add_low.Stmt := by
  intro FS O hO i j v res h
  simp only [bv_extract.r_add_low] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i c l r T hi
  simp only [decide_eq_true_eq] at hi; subst hi
  refine Refines.trans ?_ (Refines.trans (Refines.binop_ty (fun x => ty x)
    (fun x y h => by simp [h]) (hO.bv_extract _ _ _) (hO.bv_extract _ _ _)) (hO.bv_add _ _ _))
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨k, hb, h0, h1, h2, -, wb⟩ := WT_extract.1 w
    obtain ⟨n, hn, hl, hr, hT, wl, wr⟩ := (WT_checked (fun _ _ _ => Iff.rfl)).1 wb
    simp only [Term.ty_mk] at hb; subst hT; simp only [Ty.bitVector.injEq] at hb; subst hb
    refine ⟨(@BitOp.add FS).WT.2 ⟨j - 0 + 1, by omega, rfl, rfl, rfl,
      WT_extract.2 ⟨n, hl, h0, h1, h2, rfl, wl⟩, WT_extract.2 ⟨n, hr, h0, h1, h2, rfl, wr⟩⟩, rfl⟩
  · obtain ⟨k, z, hb, h0, h1, h2, -, eb, rfl⟩ := eval_extract e
    obtain ⟨n, x, y, el, er, hz⟩ := eval_add_eq_some eb
    obtain ⟨rfl, rfl⟩ := Val.bv_inj hz
    obtain ⟨_, w1, w2⟩ := WT_binop.1 w'
    rw [BitOp.add.eval_of w' (eval_extract_of w1 el) (eval_extract_of w2 er)]
    congr 2
    simp only [Int.toNat_zero]
    rw [BitVec.extractLsb'_add (by omega)]

theorem bv_extract.r_add_const.proof : bv_extract.r_add_const.Stmt := by
  intro FS O hO i j v res h
  simp only [bv_extract.r_add_const] at h
  have main : ∀ {c l r T} (x : Term) {n : Int}, j < lsb n →
      (∀ ρ u, eval FS ρ (.mk (.binop (.add c) l r) T) = some u →
        ∃ k a b, eval FS ρ x = some (.bv k b) ∧ u = .bv k (a + b) ∧ 0 ≤ n ∧
          a = BitVec.ofInt k n ∧ n < 2 ^ k) →
      ((Term.mk (.binop (.add c) l r) T).WT → x.ty = T ∧ x.WT) →
      Refines FS (bv_extract.spec i j (.mk (.binop (.add c) l r) T)) (O.bv_extract i j x) := by
    intro c l r T x n hj hsem hwt
    refine Refines.trans ?_ (hO.bv_extract _ _ _)
    refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
    · obtain ⟨m, hb, h0, h1, h2, -, wb⟩ := WT_extract.1 w
      obtain ⟨hx, wx⟩ := hwt wb
      exact ⟨WT_extract.2 ⟨m, hx.trans hb, h0, h1, h2, rfl, wx⟩, rfl⟩
    · obtain ⟨m, z, hb, h0, h1, h2, -, eb, rfl⟩ := eval_extract e
      obtain ⟨k, a, b, ex, hz, n0, rfl, n1⟩ := hsem ρ _ eb
      have hd := lsb_dvd n0 hj (by omega)
      obtain ⟨rfl, rfl⟩ := Val.bv_inj hz
      simp only [bv_extract.spec] at w' ⊢
      rw [eval_extract_of w' ex]; congr 1
      apply Val.bv_ext rfl
      intro t ht
      simp only [BitVec.getLsbD_extractLsb']
      rw [getLsbD_add_of_dvd _ _ (q := j.toNat + 1) (by rw [toNat_ofInt_lit n0 n1]; exact hd)
        (by omega)]
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> obtain ⟨hj, rfl⟩ := h
  · rename_i c n T1 x T
    refine main x hj (fun ρ u e => ?_) (fun w => ?_)
    · obtain ⟨k, a, b, ea, eb, rfl⟩ := eval_add_eq_some e
      obtain ⟨rfl, n0, n1⟩ := lit_val₀ ea
      exact ⟨k, _, b, eb, rfl, n0, rfl, n1⟩
    · obtain ⟨m, hm, h1, h2, hT, w1, w2⟩ := (WT_checked (fun _ _ _ => Iff.rfl)).1 w
      exact ⟨h2.trans hT.symm, w2⟩
  · rename_i c x n T1 T
    refine main x hj (fun ρ u e => ?_) (fun w => ?_)
    · obtain ⟨k, b, a, eb, ea, rfl⟩ := eval_add_eq_some e
      obtain ⟨rfl, n0, n1⟩ := lit_val₀ ea
      exact ⟨k, _, b, eb, by rw [BitVec.add_comm], n0, rfl, n1⟩
    · obtain ⟨m, hm, h1, h2, hT, w1, w2⟩ := (WT_checked (fun _ _ _ => Iff.rfl)).1 w
      exact ⟨h1.trans hT.symm, w1⟩

theorem bv_extract.r_mul_pow2.proof : bv_extract.r_mul_pow2.Stmt := by
  intro FS O hO i j v res h
  simp only [bv_extract.r_mul_pow2] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i c z T1 y T hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hp, hj⟩ := hc
  obtain ⟨hz, hl⟩ := is_pow2_eq hp
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨n, hb, h0, h1, h2, -, wb⟩ := WT_extract.1 w
    exact ⟨bv_zero_WT (by omega), rfl⟩
  · obtain ⟨n, x, hb, h0, h1, h2, -, eb, rfl⟩ := eval_extract e
    obtain ⟨k, a, b, ea, eb', hx⟩ := eval_mul_eq_some eb
    obtain ⟨rfl, rfl⟩ := Val.bv_inj hx
    obtain ⟨rfl, -, -⟩ := lit_val₀ ea
    rw [eval_bv_zero (by omega)]; congr 1
    apply Val.bv_ext rfl
    intro t ht
    rw [hz, ofInt_two_pow, BitVec.twoPow_mul_eq_shiftLeft]
    bitw_simp

theorem bv_extract.r_mul_low.proof : bv_extract.r_mul_low.Stmt := by
  intro FS O hO i j v res h
  simp only [bv_extract.r_mul_low] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i c l r T hi
  simp only [decide_eq_true_eq] at hi; subst hi
  refine Refines.trans ?_ (Refines.trans (Refines.binop_ty (fun x => ty x)
    (fun x y h => by simp [h]) (hO.bv_extract _ _ _) (hO.bv_extract _ _ _)) (hO.bv_mul _ _ _))
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨k, hb, h0, h1, h2, -, wb⟩ := WT_extract.1 w
    obtain ⟨n, hn, hl, hr, hT, wl, wr⟩ := (WT_checked (fun _ _ _ => Iff.rfl)).1 wb
    simp only [Term.ty_mk] at hb; subst hT; simp only [Ty.bitVector.injEq] at hb; subst hb
    refine ⟨(@BitOp.mul FS).WT.2 ⟨j - 0 + 1, by omega, rfl, rfl, rfl,
      WT_extract.2 ⟨n, hl, h0, h1, h2, rfl, wl⟩, WT_extract.2 ⟨n, hr, h0, h1, h2, rfl, wr⟩⟩, rfl⟩
  · obtain ⟨k, z, hb, h0, h1, h2, -, eb, rfl⟩ := eval_extract e
    obtain ⟨n, x, y, el, er, hz⟩ := eval_mul_eq_some eb
    obtain ⟨rfl, rfl⟩ := Val.bv_inj hz
    obtain ⟨_, w1, w2⟩ := WT_binop.1 w'
    rw [BitOp.mul.eval_of w' (eval_extract_of w1 el) (eval_extract_of w2 er)]
    congr 2
    simp only [Int.toNat_zero]
    rw [BitVec.extractLsb'_mul (by omega)]

theorem bv_extract.r_urem.proof : bv_extract.r_urem.Stmt := by
  intro FS O hO i j v res h
  simp only [bv_extract.r_urem] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i l z T2 T hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨rfl, hp, hj⟩ := hc
  obtain ⟨hz, hl⟩ := is_pow2_eq hp
  refine Refines.trans ?_ (Refines.trans (Refines.binop_ty (fun x => ty x)
    (fun x y h => by simp [h]) (hO.bv_extract _ _ _) Refines.refl) (hO.bv_rem _ _ _))
  have key : (bv_extract.spec 0 j (.mk (.binop (.rem false) l (.mk (.bitVec z) T2)) T)).WT →
      ∃ n : Int, 0 < n ∧ l.ty = .bitVector n ∧ T2 = .bitVector n ∧ T = .bitVector n ∧
        0 ≤ j ∧ j < n ∧ l.WT ∧ 0 ≤ z ∧ z < 2 ^ n.toNat := by
    intro w
    obtain ⟨n, hb, h0, h1, h2, -, wb⟩ := WT_extract.1 w
    obtain ⟨n', hn', ha, h2', ht, wa, w2⟩ := (BitOp.urem (FS := FS)).WT.1 wb
    simp only [Term.ty_mk] at hb h2'; subst hb
    simp only [Ty.bitVector.injEq] at ht; subst ht
    exact ⟨n, hn', ha, h2', rfl, h1, h2, wa, (lit_inv w2 n h2').2⟩
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨n, hn, hl, -, rfl, h1, h2, wl, z0, z1⟩ := key w
    refine ⟨(BitOp.urem (FS := FS)).WT.2 ⟨j - 0 + 1, by omega, rfl, by simp [mk_bv], rfl,
      WT_extract.2 ⟨n, hl, by omega, h1, h2, rfl, wl⟩, mk_masked_WT (by omega)⟩, rfl⟩
  · obtain ⟨n, hn, hl, rfl, rfl, h1, h2, wl, z0, z1⟩ := key w
    obtain ⟨k, x, hb, h0, -, -, -, eb, rfl⟩ := eval_extract e
    simp only [Term.ty_mk, Ty.bitVector.injEq] at hb; subst hb
    obtain ⟨k', y, ea, hx, -, -⟩ := BitOp.urem.eval_lit_r eb
    obtain ⟨rfl, rfl⟩ := Val.bv_inj hx
    obtain ⟨_, w1, w2⟩ := WT_binop.1 w'
    have em : eval FS ρ (mk_bv (j + 1) z) = some (.bv (j - 0 + 1).toNat (BitVec.ofInt _ z)) := by
      rw [mk_bv, eval_mk_masked (by omega), show j - 0 + 1 = j + 1 by omega]
    rw [BitOp.urem.eval_of w' (eval_extract_of w1 ea) em]
    congr 2
    apply BitVec.eq_of_toNat_eq
    obtain ⟨K, hK, rfl⟩ : ∃ K : Nat, K < (j - 0 + 1).toNat ∧ z = ((2 ^ K : Nat) : Int) :=
      ⟨(log2 z).toNat, by omega, by rw [int_two_pow_cast]; exact hz⟩
    simp only [BitVec.umod_eq, BitVec.toNat_umod, BitVec.extractLsb'_toNat, Int.toNat_zero,
      Nat.shiftRight_zero, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
    have hKL : 2 ^ K < 2 ^ (j - 0 + 1).toNat := Nat.pow_lt_pow_right (by omega) hK
    have hKN : 2 ^ K < 2 ^ n.toNat := by
      exact_mod_cast (by rw [int_two_pow_cast]; exact z1 : ((2 ^ K : Nat) : Int) < ((2 ^ n.toNat : Nat) : Int))
    rw [Nat.mod_eq_of_lt hKL, Nat.mod_eq_of_lt hKN,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (Nat.le_of_lt hK)),
      Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (Nat.two_pow_pos _)) hKL)]

theorem bv_extract.r_default.proof : bv_extract.r_default.Stmt := by
  intro FS O hO i j v res h
  simp [bv_extract.r_default] at h; subst h; exact Refines.refl

theorem bv_extend.r_lit.proof : bv_extend.r_lit.Stmt := by
  intro FS O hO s k v res h
  simp only [bv_extend.r_lit] at h
  split at h
  case h_2 => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i z T
  have key : (bv_extend.spec s k (.mk (.bitVec z) T)).WT → ∃ n : Int, 0 < n ∧
      T = .bitVector n ∧ 0 ≤ k ∧ 0 ≤ z ∧ z < 2 ^ n.toNat := by
    intro w
    obtain ⟨n, hn, h1, hk, -, w1⟩ := WT_extend.1 w
    simp only [Term.ty_mk] at h1
    exact ⟨n, hn, h1, hk, (lit_inv w1 n h1).2⟩
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨n, hn, rfl, hk, z0, z1⟩ := key w
    cases s <;> exact ⟨mk_masked_WT (by simp; omega), rfl⟩
  · obtain ⟨n, hn, rfl, hk, z0, z1⟩ := key w
    obtain ⟨m, x, hm, h1, -, -, ex, rfl⟩ := eval_extend e
    simp only [Term.ty_mk, Ty.bitVector.injEq] at h1; subst h1
    obtain ⟨rfl, -, -⟩ := lit_val₀ ex
    simp only [size_eq, Term.ty_mk, size_of_ty_bitVector]
    cases s
    · simp only [mk_bv, Bool.false_eq_true, ↓reduceIte]
      rw [eval_mk_masked (by omega)]; congr 1
      apply Val.bv_ext_toNat (by omega)
      have z2 := two_pow_mono z1 (show n.toNat ≤ (n + k).toNat by omega)
      have z3 := two_pow_mono z1 (show n.toNat ≤ n.toNat + k.toNat by omega)
      have := int_two_pow_cast (n.toNat + k.toNat)
      rw [BitVec.toNat_setWidth, toNat_ofInt_lit z0 z1, toNat_ofInt_lit z0 z2,
        Nat.mod_eq_of_lt (by omega)]
    · simp only [↓reduceIte]
      rw [eval_mk_masked (by omega)]; congr 1
      rw [signed_extract_eq_toInt' hn z0 z1]
      apply Val.bv_ext_toNat (by omega)
      simp only [BitVec.signExtend, BitVec.toNat_ofInt]
      rw [show (n + k).toNat = n.toNat + k.toNat by omega]

theorem bv_extend.r_extend.proof : bv_extend.r_extend.Stmt := by
  intro FS O hO s k v res h
  simp only [bv_extend.r_extend] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i s' p a T hs
  simp only [decide_eq_true_eq] at hs; subst hs
  refine Refines.trans ?_ (hO.bv_extend _ _ _)
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨n, hn, h1, hk, -, w1⟩ := WT_extend.1 w
    obtain ⟨m, hm, ha, hp, hT, wa⟩ := WT_extend.1 w1
    simp only [Term.ty_mk] at h1; subst hT; simp only [Ty.bitVector.injEq] at h1; subst h1
    refine ⟨WT_extend.2 ⟨m, hm, ha, by omega, by simp [ha], wa⟩, ?_⟩
    simp [bv_extend.spec, ha]; omega
  · obtain ⟨n, x, hn, h1, hk, -, ex, rfl⟩ := eval_extend e
    obtain ⟨m, y, hm, ha, hp, hT, ey, hx⟩ := eval_extend ex
    simp only [Term.ty_mk] at h1; subst hT; simp only [Ty.bitVector.injEq] at h1; subst h1
    simp only [bv_extend.spec] at w' ⊢
    rw [eval_extend_of w' ey]; congr 1
    apply Val.bv_ext (by omega)
    intro t ht
    have hb := Val.bv_getLsbD hx
    cases s'
    · simp only [Bool.false_eq_true, ↓reduceIte] at hb ⊢
      (try bitw_simp); (try simp only [hb])
      by_cases h1 : t < m.toNat <;> by_cases h2 : t < (m + p).toNat <;> bitw_simp
    · simp only [↓reduceIte] at hb ⊢
      (try bitw_simp); (try simp only [hb])
      by_cases h1 : t < m.toNat <;> by_cases h2 : t < (m + p).toNat <;>
        by_cases h3 : p = 0 <;> bitw_simp <;> congr 1 <;> omega

theorem bv_extend.r_ite.proof : bv_extend.r_ite.Stmt := by
  intro FS O hO s k v res h
  simp only [bv_extend.r_ite] at h
  split at h <;> simp at h; subst h
  have rt : ∀ {a : Term} {t}, Refines FS (.mk (.unop (.bvExtend s k) a) t) (O.bv_extend s k a) :=
    fun {a t} => Refines.trans (Refines.retype (fun w => by
      obtain ⟨n, _, h1, _, ht, _⟩ := WT_extend.1 w; simp [h1, ht])) (hO.bv_extend s k a)
  exact Refines.trans Refines.unop_ite (Refines.ite_O hO rt rt)

theorem bv_extend.r_of_bool.proof : bv_extend.r_of_bool.Stmt := by
  intro FS O hO s k v res h
  simp only [bv_extend.r_of_bool] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i m b T hs
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at hs
  refine Refines.trans ?_ (hO.bv_of_bool _ _)
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨n, hn, h1, hk, -, w1⟩ := WT_extend.1 w
    obtain ⟨hm, hb, hT, wb⟩ := WT_bvOfBool.1 w1
    simp only [Term.ty_mk] at h1; subst hT; simp only [Ty.bitVector.injEq] at h1; subst h1
    exact ⟨WT_bvOfBool.2 ⟨by simp; omega, hb, rfl, wb⟩, rfl⟩
  · obtain ⟨n, x, hn, h1, hk, -, ex, rfl⟩ := eval_extend e
    obtain ⟨hm, hb, hT, wb⟩ := WT_bvOfBool.1 (eval_WT ex)
    simp only [Term.ty_mk] at h1; subst hT; simp only [Ty.bitVector.injEq] at h1; subst h1
    obtain ⟨c, ec, hx⟩ := eval_bvOfBool ex
    simp only [bv_of_bool.spec] at w' ⊢
    rw [eval_bvOfBool' w' ec]; congr 1
    apply Val.bv_ext (by simp; omega)
    intro t ht
    have hb := Val.bv_getLsbD hx
    have hsz : size (Term.mk (.unop (.bvOfBool m) b) (.bitVector m)) = m := by simp
    cases s <;> cases c <;> (try simp at hs) <;> simp only [↓reduceIte, Bool.false_eq_true] at hb ⊢ <;>
      bitw_simp <;> simp only [hb, getLsbD_zero', getLsbD_one'] <;>
      by_cases h1 : t < m.toNat <;> by_cases h2 : t = 0 <;> bitw_simp

theorem bv_extend.r_default.proof : bv_extend.r_default.Stmt := by
  intro FS O hO s k v res h
  simp [bv_extend.r_default] at h; subst h; exact Refines.refl

theorem bv_concat.r_lits.proof : bv_concat.r_lits.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_concat.r_lits] at h
  split at h
  case h_2 => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i l T1 r T2
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨n, m, hn, hm, h1, h2, -, -, -⟩ := WT_concat.1 w
    simp only [Term.ty_mk] at h1 h2; subst h1 h2
    exact ⟨mk_masked_WT (by simp; omega), rfl⟩
  · obtain ⟨n, m, x, y, hn, hm, h1, h2, -, ex, ey, rfl⟩ := eval_concat e
    simp only [Term.ty_mk] at h1 h2; subst h1 h2
    obtain ⟨rfl, l0, l1⟩ := lit_val₀ ex
    obtain ⟨rfl, r0, r1⟩ := lit_val₀ ey
    simp only [size_eq, Term.ty_mk, size_of_ty_bitVector]
    rw [eval_mk_masked (by omega)]; congr 1
    have hm' : zshiftl l m = zshiftl l (m.toNat : Int) := by rw [zshiftl, zshiftl, Int.toNat_natCast]
    rw [hm', ← ofInt_concat_lits l0 l1 r0 r1]
    apply Val.bv_ext_toNat (by omega)
    simp only [BitVec.toNat_ofInt]
    rw [show (n + m).toNat = n.toNat + m.toNat by omega]

theorem bv_concat.r_extracts.proof : bv_concat.r_extracts.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_concat.r_extracts] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i f1 t1 a T1 f2 t2 a' T2 hc
  simp only [Bool.and_eq_true, equal, decide_eq_true_eq] at hc
  obtain ⟨rfl, hc⟩ := hc
  refine Refines.trans ?_ (hO.bv_extract _ _ _)
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨n, m, hn, hm, h1, h2, hT, w1, w2⟩ := WT_concat.1 w
    obtain ⟨k, ha, a0, a1, a2, hT1, wa⟩ := WT_extract.1 w1
    obtain ⟨k', ha', b0, b1, b2, hT2, -⟩ := WT_extract.1 w2
    simp only [Term.ty_mk] at h1 h2; subst h1 h2
    rw [ha] at ha'; simp only [Ty.bitVector.injEq] at ha' hT1 hT2; subst ha'
    refine ⟨WT_extract.2 ⟨k, ha, by omega, by omega, by omega, rfl, wa⟩, ?_⟩
    simp [bv_extract.spec, bv_concat.spec]; omega
  · obtain ⟨n, m, x, y, hn, hm, h1, h2, -, ex, ey, rfl⟩ := eval_concat e
    obtain ⟨k, X, ha, a0, a1, a2, hT1, ea, hx⟩ := eval_extract ex
    obtain ⟨k', Y, ha', b0, b1, b2, hT2, ea', hy⟩ := eval_extract ey
    simp only [Term.ty_mk] at h1 h2; subst h1 h2
    rw [ha] at ha'; simp only [Ty.bitVector.injEq] at ha' hT1 hT2; subst ha'
    have e3 := Val.bv_getLsbD (Option.some.inj (ea.symm.trans ea'))
    simp only [bv_extract.spec] at w' ⊢
    rw [eval_extract_of w' ea]; congr 1
    apply Val.bv_ext (by omega)
    intro t ht
    have e1 := Val.bv_getLsbD hx
    have e2 := Val.bv_getLsbD hy
    by_cases hts : t < m.toNat
    · bitw_simp; rw [e2]; bitw_simp; rw [← e3]
    · bitw_simp; rw [e1]; bitw_simp; congr 1; omega

theorem bv_concat.r_extract_extracts.proof : bv_concat.r_extract_extracts.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_concat.r_extract_extracts] at h
  split at h <;> simp at h; subst h; exact Refines.refl

theorem bv_concat.r_assoc_l.proof : bv_concat.r_assoc_l.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_concat.r_assoc_l] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  simp only [Option.some.injEq] at h; subst h
  refine Refines.trans concat_assoc_l (Refines.trans (Refines.binop_ty2
    (fun x y => .bitVector (size x + size y)) (fun x x' y y' h1 h2 => by simp [h1, h2])
    (hO.bv_concat _ _) Refines.refl) (hO.bv_concat _ _))

theorem bv_concat.r_assoc_r.proof : bv_concat.r_assoc_r.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_concat.r_assoc_r] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  simp only [Option.some.injEq] at h; subst h
  refine Refines.trans concat_assoc_r (Refines.trans (Refines.binop_ty2
    (fun x y => .bitVector (size x + size y)) (fun x x' y y' h1 h2 => by simp [h1, h2])
    Refines.refl (hO.bv_concat _ _)) (hO.bv_concat _ _))

theorem bv_concat.r_ites.proof : bv_concat.r_ites.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [bv_concat.r_ites] at h
  split at h
  case h_2 => simp at h
  split at h
  case isFalse => simp at h
  simp only [Option.some.injEq] at h; subst h
  rename_i g l1 r1 T1 g' l2 r2 T2 hc
  simp only [equal, decide_eq_true_eq] at hc; subst hc
  refine Refines.trans ?_ (Refines.ite_O hO (t := .bitVector
    (size (Term.mk (.triop .ite g l1 r1) T1) + size (Term.mk (.triop .ite g l2 r2) T2)))
    (hO.bv_concat _ _) (hO.bv_concat _ _))
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨n, m, hn, hm, h1, h2, hT, w1, w2⟩ := WT_concat.1 w
    obtain ⟨hg, hr1, hl1, wg, wl1, wr1⟩ := WT_ite.1 w1
    obtain ⟨-, hr2, hl2, -, wl2, wr2⟩ := WT_ite.1 w2
    simp only [Term.ty_mk] at h1 h2; subst h1 h2
    refine ⟨WT_ite.2 ⟨hg, ?_, ?_, wg, WT_concat.2 ⟨n, m, hn, hm, hl1.symm, hl2.symm, ?_, wl1, wl2⟩,
      WT_concat.2 ⟨n, m, hn, hm, hr1.trans hl1.symm, hr2.trans hl2.symm, ?_, wr1, wr2⟩⟩, rfl⟩ <;>
      simp [bv_concat.spec, ← hl1, ← hl2, hr1, hr2]
  · obtain ⟨n, m, x, y, hn, hm, h1, h2, -, ex, ey, rfl⟩ := eval_concat e
    obtain ⟨-, -, -, -, wc1, wc2⟩ := WT_ite.1 w'
    obtain ⟨hg, hr1, hl1, wg, wl1, wr1⟩ := WT_ite.1 (eval_WT ex)
    rw [eval_ite w']
    rw [eval_ite (eval_WT ex)] at ex
    rw [eval_ite (eval_WT ey)] at ey
    simp only [bv_concat.spec] at wc1 wc2 ⊢
    rcases eg : eval FS ρ g with _ | ⟨c | _ | _ | _ | _ | _⟩ <;> simp only [eg] at ex ey ⊢ <;>
      (try simp at ex)
    cases c
    · simp only at ex ey ⊢; rw [eval_concat_of wc2 ex ey]
    · simp only at ex ey ⊢; rw [eval_concat_of wc1 ex ey]

theorem bv_concat.r_default.proof : bv_concat.r_default.Stmt := by
  intro FS O hO v1 v2 res h
  simp [bv_concat.r_default] at h; subst h; exact Refines.refl

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
