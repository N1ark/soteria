import Bvr.Proofs.ArithLemmas

/-! Bit-vector arithmetic and overflow checks. -/

namespace Bvr

open Classical ArithL

set_option linter.unusedSimpArgs false

theorem bv_add.r_lits.proof : bv_add.r_lits.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_add.r_lits] at h; split at h <;> simp at h; subst h
  simp only [bv_add.spec, ty_eq, Term.ty_mk]
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  all_goals obtain ⟨n, wa, wb, hT⟩ := (WT_arith (.add c)).1 w
  all_goals obtain ⟨rfl, _⟩ := BV_lit wa
  · exact ⟨mk_masked_WT wa.2.2, rfl⟩
  · rw [eval_arith (.add c) wa wb hT, eval_lit wa, eval_lit wb] at e
    simp [evBinop, checkedOp, bvBin] at e
    rw [size_of_ty_bitVector, eval_mk_masked wa.2.2, ← e.2, BitVec.ofInt_add]

theorem bv_add.r_neg_l.proof : bv_add.r_neg_l.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_add.r_neg_l] at h; split at h <;> simp at h; subst h
  rename_i ck x T
  simp only [bv_add.spec, ty_eq, Term.ty_mk]
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  all_goals obtain ⟨n, wa, wb, hT⟩ := (WT_arith (.add c)).1 w
  all_goals obtain ⟨wx, rfl⟩ := BV_neg_inv wa
  all_goals have wr := BV_arith (.sub _) (hO.bv_sub unchecked v2 x) wb wx
  · exact ⟨wr.1, by simp [wr.2.1]⟩
  · rw [eval_arith (.add c) wa wb rfl] at e
    obtain ⟨a, y, ha, hy, e⟩ := evBinop_inv (.inl (.add c)) wa wb e
    rw [eval_neg wx rfl] at ha
    obtain ⟨x', hx, ha⟩ := evUnop_inv wx ha
    refine (hO.bv_sub _ _ _).sem ρ v ?_
    rw [bv_sub.spec, ty_eq, eval_arith (.sub _) wb wx wb.2.1, hx, hy]
    simp [evBinop, evUnop, checkedOp, bvBin, unchecked] at e ha ⊢
    rw [← e.2, ← ha.2, BitVec.sub_eq_add_neg, BitVec.add_comm]

theorem bv_add.r_neg_r.proof : bv_add.r_neg_r.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_add.r_neg_r] at h; split at h <;> simp at h; subst h
  rename_i ck x T
  simp only [bv_add.spec, ty_eq]
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  all_goals obtain ⟨n, wa, wb, hT⟩ := (WT_arith (.add c)).1 w
  all_goals obtain ⟨wx, rfl⟩ := BV_neg_inv wb
  all_goals have wr := BV_arith (.sub _) (hO.bv_sub unchecked v1 x) wa wx
  · exact ⟨wr.1, by simp [wr.2.1, wa.2.1]⟩
  · rw [eval_arith (.add c) wa wb wa.2.1] at e
    obtain ⟨y, a, hy, ha, e⟩ := evBinop_inv (.inl (.add c)) wa wb e
    rw [eval_neg wx rfl] at ha
    obtain ⟨x', hx, ha⟩ := evUnop_inv wx ha
    refine (hO.bv_sub _ _ _).sem ρ v ?_
    rw [bv_sub.spec, ty_eq, eval_arith (.sub _) wa wx wa.2.1, hx, hy]
    simp [evBinop, evUnop, checkedOp, bvBin, unchecked] at e ha ⊢
    rw [← e.2, ← ha.2, BitVec.sub_eq_add_neg]

theorem bv_add.r_zero_r.proof : bv_add.r_zero_r.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_add.r_zero_r] at h; split at h <;> simp at h; obtain ⟨rfl, rfl⟩ := h
  simp only [bv_add.spec, ty_eq]
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  all_goals obtain ⟨n, wa, wb, hT⟩ := (WT_arith (.add c)).1 w
  · exact ⟨wa.1, by simp⟩
  · rw [eval_arith (.add c) wa wb hT] at e
    obtain ⟨x, y, hx, hy, e⟩ := evBinop_inv (.inl (.add c)) wa wb e
    rw [eval_lit wb] at hy; simp at hy; subst hy
    simp [evBinop, checkedOp, bvBin] at e
    rw [hx, ← e.2]

theorem bv_add.r_zero_l.proof : bv_add.r_zero_l.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_add.r_zero_l] at h; split at h <;> simp at h; obtain ⟨rfl, rfl⟩ := h
  simp only [bv_add.spec, ty_eq]
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  all_goals obtain ⟨n, wa, wb, hT⟩ := (WT_arith (.add c)).1 w
  · exact ⟨wb.1, by simp [wa.2.1, wb.2.1]⟩
  · rw [eval_arith (.add c) wa wb hT] at e
    obtain ⟨x, y, hx, hy, e⟩ := evBinop_inv (.inl (.add c)) wa wb e
    rw [eval_lit wa] at hx; simp at hx; subst hx
    simp [evBinop, checkedOp, bvBin] at e
    rw [hy, ← e.2]

theorem bv_add.r_not_one.proof : bv_add.r_not_one.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_add.r_not_one] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> obtain ⟨rfl, rfl⟩ := h
  · rename_i T1 x T2
    simp only [bv_add.spec, ty_eq, Term.ty_mk]
    refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
    all_goals obtain ⟨n, wa, wb, rfl⟩ := (WT_arith (.add c)).1 w
    all_goals obtain ⟨wx, rfl⟩ := BV_not_inv wb
    all_goals have wr := BV_neg (hO.bv_neg false x) wx
    · exact ⟨wr.1, by simp [wr.2.1]⟩
    · rw [eval_arith (.add c) wa wb rfl, eval_lit wa, eval_not wx rfl] at e
      obtain ⟨x', hx⟩ := (eval_BV wx FS ρ).resolve_left (by intro h; simp [h, evBinop, checkedOp] at e)
      refine (hO.bv_neg _ _).sem ρ v ?_
      rw [bv_neg.spec, ty_eq, eval_neg wx wx.2.1, hx]
      rw [hx] at e
      simp [evBinop, evUnop, checkedOp, bvBin] at e ⊢
      rw [← e.2, BitVec.neg_eq_not_add, BitVec.add_comm]
  · rename_i x T1 T2
    simp only [bv_add.spec, ty_eq, Term.ty_mk]
    refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
    all_goals obtain ⟨n, wa, wb, rfl⟩ := (WT_arith (.add c)).1 w
    all_goals obtain ⟨wx, -⟩ := BV_not_inv wa
    all_goals have wr := BV_neg (hO.bv_neg false x) wx
    · exact ⟨wr.1, by simp [wr.2.1]⟩
    · rw [eval_arith (.add c) wa wb rfl, eval_lit wb, eval_not wx rfl] at e
      obtain ⟨x', hx⟩ := (eval_BV wx FS ρ).resolve_left (by intro h; simp [h, evBinop, checkedOp] at e)
      refine (hO.bv_neg _ _).sem ρ v ?_
      rw [bv_neg.spec, ty_eq, eval_neg wx wx.2.1, hx]
      rw [hx] at e
      simp [evBinop, evUnop, checkedOp, bvBin] at e ⊢
      rw [← e.2, BitVec.neg_eq_not_add]

theorem bv_add.add_const_aux {FS : FloatSem} {O : Ops} (hO : O.Sound FS) {c ck z1 Tc r T1 z2 T2} :
    Refines FS (bv_add.spec c (.mk (.binop (.add ck) (.mk (.bitVec z1) Tc) r) T1) (.mk (.bitVec z2) T2))
      (O.bv_add (mask_checked_after_fold (checked_meet c ck) (.mk (.bitVec z1) Tc)
          (.mk (.bitVec z2) T2) true)
        (O.bv_add unchecked (.mk (.bitVec z1) Tc) (.mk (.bitVec z2) T2)) r) := by
  simp only [bv_add.spec, ty_eq, Term.ty_mk]
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  all_goals obtain ⟨n, wa, wb, rfl⟩ := (WT_arith (.add c)).1 w
  all_goals obtain ⟨wc, wr, -⟩ := BV_arith_inv (.add ck) wa
  all_goals obtain ⟨rfl, hz1⟩ := BV_lit wc
  all_goals obtain ⟨rfl, hz2⟩ := BV_lit wb
  all_goals have wi := BV_arith (.add _) (hO.bv_add unchecked _ _) wc wb
  all_goals have wres := BV_arith (.add _) (hO.bv_add (mask_checked_after_fold (checked_meet c ck)
    (.mk (.bitVec z1) (.bitVector n)) (.mk (.bitVec z2) (.bitVector n)) true) _ r) wi wr
  · exact ⟨wres.1, by simp [wres.2.1]⟩
  · rw [eval_arith (.add c) wa wb rfl, eval_lit wb] at e
    obtain ⟨s, Y, hs, hY, e⟩ := evBinop_inv (.inl (.add c)) wa wb (by rwa [eval_lit wb])
    rw [eval_lit wb] at hY; simp at hY; subst hY
    rw [eval_arith (.add ck) wc wr rfl] at hs
    obtain ⟨X, R, hX, hR, hs⟩ := evBinop_inv (.inl (.add ck)) wc wr hs
    rw [eval_lit wc] at hX; simp at hX; subst hX
    have hi := (hO.bv_add unchecked _ _).sem ρ (.bv n.toNat (BitVec.ofInt _ z1 + BitVec.ofInt _ z2))
      (by rw [bv_add.spec, ty_eq, eval_arith (.add _) wc wb wc.2.1, eval_lit wc, eval_lit wb]
          simp [evBinop, checkedOp, bvBin, unchecked])
    refine (hO.bv_add _ _ _).sem ρ v ?_
    rw [bv_add.spec, ty_eq, eval_arith (.add _) wi wr wi.2.1, hi, hR, mask_lits,
      size_of_ty_bitVector, overflows_add_lit wc.2.2 hz1.1 hz1.2 hz2.1 hz2.2,
      overflows_add_lit wc.2.2 hz1.1 hz1.2 hz2.1 hz2.2]
    simp [evBinop, checkedOp, bvBin, checked_meet] at e hs ⊢
    obtain ⟨⟨e1, e2⟩, rfl⟩ := e; obtain ⟨⟨h1, h2⟩, rfl⟩ := hs
    refine ⟨⟨fun hc hck h3 => sadd_reassoc (h1 hck) (e1 hc) h3,
      fun hc hck h3 => uadd_reassoc (h2 hck) (e2 hc) h3⟩, ?_⟩
    congr 1; ac_rfl

theorem bv_add.r_add_const.proof : bv_add.r_add_const.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_add.r_add_const] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> subst h
  · exact bv_add.add_const_aux hO
  · rename_i T1 _ _
    refine Refines.trans ?_ (bv_add.add_const_aux hO (T1 := T1))
    exact Refines.binop (Refines.comm (.add _)) Refines.refl (fun _ => rfl)

theorem bv_add.r_sub_const_r.proof : bv_add.r_sub_const_r.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_add.r_sub_const_r] at h; split at h <;> simp at h; subst h
  rename_i ck l z1 Tc T1 z2 T2
  simp only [bv_add.spec, ty_eq, Term.ty_mk]
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  all_goals obtain ⟨n, wa, wb, rfl⟩ := (WT_arith (.add c)).1 w
  all_goals obtain ⟨wl, wc, -⟩ := BV_arith_inv (.sub ck) wa
  all_goals obtain ⟨rfl, hz1⟩ := BV_lit wc
  all_goals obtain ⟨rfl, hz2⟩ := BV_lit wb
  all_goals have wi := BV_arith (.sub _) (hO.bv_sub unchecked _ _) wb wc
  all_goals have wres := BV_arith (.add _) (hO.bv_add (mask_checked_after_fold (checked_meet c ck)
    (.mk (.bitVec z2) (.bitVector n)) (.mk (.bitVec z1) (.bitVector n)) false) l _) wl wi
  · exact ⟨wres.1, by simp [wres.2.1]⟩
  · rw [eval_arith (.add c) wa wb rfl] at e
    obtain ⟨s, Y, hs, hY, e⟩ := evBinop_inv (.inl (.add c)) wa wb e
    rw [eval_lit wb] at hY; simp at hY; subst hY
    rw [eval_arith (.sub ck) wl wc rfl] at hs
    obtain ⟨L, X, hL, hX, hs⟩ := evBinop_inv (.inl (.sub ck)) wl wc hs
    rw [eval_lit wc] at hX; simp at hX; subst hX
    have hi := (hO.bv_sub unchecked _ _).sem ρ (.bv n.toNat (BitVec.ofInt _ z2 - BitVec.ofInt _ z1))
      (by rw [bv_sub.spec, ty_eq, eval_arith (.sub _) wb wc wb.2.1, eval_lit wc, eval_lit wb]
          simp [evBinop, checkedOp, bvBin, unchecked])
    refine (hO.bv_add _ _ _).sem ρ v ?_
    rw [bv_add.spec, ty_eq, eval_arith (.add _) wl wi wl.2.1, hi, hL, mask_lits,
      size_of_ty_bitVector, overflows_sub_lit wc.2.2 hz2.1 hz2.2 hz1.1 hz1.2,
      overflows_sub_lit wc.2.2 hz2.1 hz2.2 hz1.1 hz1.2]
    simp [evBinop, checkedOp, bvBin, checked_meet] at e hs ⊢
    obtain ⟨⟨e1, e2⟩, rfl⟩ := e; obtain ⟨⟨h1, h2⟩, rfl⟩ := hs
    refine ⟨⟨fun hc hck h3 => ssub_add_reassoc (h1 hck) (e1 hc) h3,
      fun hc hck h3 => usub_add_reassoc (h2 hck) (e2 hc) h3⟩, ?_⟩
    congr 1; rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg]; ac_rfl

theorem bv_add.r_sub_const_l.proof : bv_add.r_sub_const_l.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_add.r_sub_const_l] at h; split at h <;> simp at h; subst h
  rename_i ck z1 Tc r T1 z2 T2
  simp only [bv_add.spec, ty_eq, Term.ty_mk]
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  all_goals obtain ⟨n, wa, wb, rfl⟩ := (WT_arith (.add c)).1 w
  all_goals obtain ⟨wc, wr, -⟩ := BV_arith_inv (.sub ck) wa
  all_goals obtain ⟨rfl, hz1⟩ := BV_lit wc
  all_goals obtain ⟨rfl, hz2⟩ := BV_lit wb
  all_goals have wi := BV_arith (.add _) (hO.bv_add unchecked _ _) wc wb
  all_goals have wres := BV_arith (.sub _) (hO.bv_sub (mask_checked_after_fold (checked_meet c ck)
    (.mk (.bitVec z1) (.bitVector n)) (.mk (.bitVec z2) (.bitVector n)) true) _ r) wi wr
  · exact ⟨wres.1, by simp [wres.2.1]⟩
  · rw [eval_arith (.add c) wa wb rfl] at e
    obtain ⟨s, Y, hs, hY, e⟩ := evBinop_inv (.inl (.add c)) wa wb e
    rw [eval_lit wb] at hY; simp at hY; subst hY
    rw [eval_arith (.sub ck) wc wr rfl] at hs
    obtain ⟨X, R, hX, hR, hs⟩ := evBinop_inv (.inl (.sub ck)) wc wr hs
    rw [eval_lit wc] at hX; simp at hX; subst hX
    have hi := (hO.bv_add unchecked _ _).sem ρ (.bv n.toNat (BitVec.ofInt _ z1 + BitVec.ofInt _ z2))
      (by rw [bv_add.spec, ty_eq, eval_arith (.add _) wc wb wc.2.1, eval_lit wc, eval_lit wb]
          simp [evBinop, checkedOp, bvBin, unchecked])
    refine (hO.bv_sub _ _ _).sem ρ v ?_
    rw [bv_sub.spec, ty_eq, eval_arith (.sub _) wi wr wi.2.1, hi, hR, mask_lits,
      size_of_ty_bitVector, overflows_add_lit wc.2.2 hz1.1 hz1.2 hz2.1 hz2.2,
      overflows_add_lit wc.2.2 hz1.1 hz1.2 hz2.1 hz2.2]
    simp [evBinop, checkedOp, bvBin, checked_meet] at e hs ⊢
    obtain ⟨⟨e1, e2⟩, rfl⟩ := e; obtain ⟨⟨h1, h2⟩, rfl⟩ := hs
    refine ⟨⟨fun hc hck h3 => ssub_add_reassoc' (h1 hck) (e1 hc) h3,
      fun hc hck h3 => usub_add_reassoc' (h2 hck) (e2 hc) h3⟩, ?_⟩
    congr 1; rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg]; ac_rfl

theorem bv_add.r_sub_cancel_r.proof : bv_add.r_sub_cancel_r.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_add.r_sub_cancel_r] at h; split at h <;> simp [equal] at h; obtain ⟨rfl, rfl⟩ := h
  rename_i ck l T
  simp only [bv_add.spec, ty_eq]
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  all_goals obtain ⟨n, wa, wb, hT⟩ := (WT_arith (.add c)).1 w
  all_goals obtain ⟨wl, -, rfl⟩ := BV_arith_inv (.sub ck) wb
  · exact ⟨wl.1, by simp [wl.2.1, wa.2.1]⟩
  · rw [eval_arith (.add c) wa wb hT] at e
    obtain ⟨R, s, hR, hs, e⟩ := evBinop_inv (.inl (.add c)) wa wb e
    rw [eval_arith (.sub ck) wl wa rfl] at hs
    obtain ⟨L, R', hL, hR', hs⟩ := evBinop_inv (.inl (.sub ck)) wl wa hs
    rw [hR] at hR'; simp at hR'; subst hR'
    simp [evBinop, checkedOp, bvBin] at e hs
    obtain ⟨-, rfl⟩ := hs; obtain ⟨-, rfl⟩ := e
    rw [hL, show R + (L - R) = L by grind]

theorem bv_add.r_sub_cancel_l.proof : bv_add.r_sub_cancel_l.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_add.r_sub_cancel_l] at h; split at h <;> simp [equal] at h; obtain ⟨rfl, rfl⟩ := h
  rename_i ck l r T
  simp only [bv_add.spec, ty_eq, Term.ty_mk]
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  all_goals obtain ⟨n, wa, wb, rfl⟩ := (WT_arith (.add c)).1 w
  all_goals obtain ⟨wl, -, -⟩ := BV_arith_inv (.sub ck) wa
  · exact ⟨wl.1, by simp [wl.2.1]⟩
  · rw [eval_arith (.add c) wa wb rfl] at e
    obtain ⟨s, R, hs, hR, e⟩ := evBinop_inv (.inl (.add c)) wa wb e
    rw [eval_arith (.sub ck) wl wb rfl] at hs
    obtain ⟨L, R', hL, hR', hs⟩ := evBinop_inv (.inl (.sub ck)) wl wb hs
    rw [hR] at hR'; simp at hR'; subst hR'
    simp [evBinop, checkedOp, bvBin] at e hs
    obtain ⟨-, rfl⟩ := hs; obtain ⟨-, rfl⟩ := e
    rw [hL, show L - R + R = L by grind]

theorem bv_add.add_sub_aux {FS : FloatSem} {O : Ops} (hO : O.Sound FS) {c ck1 ck2 a b cc T1 T2} :
    Refines FS (bv_add.spec c (.mk (.binop (.add ck1) a b) T1) (.mk (.binop (.sub ck2) cc a) T2))
      (O.bv_add unchecked b cc) := by
  simp only [bv_add.spec, ty_eq, Term.ty_mk]
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  all_goals obtain ⟨n, w1, w2, rfl⟩ := (WT_arith (.add c)).1 w
  all_goals obtain ⟨wa, wb, -⟩ := BV_arith_inv (.add ck1) w1
  all_goals obtain ⟨wc, -, rfl⟩ := BV_arith_inv (.sub ck2) w2
  all_goals have wres := BV_arith (.add _) (hO.bv_add unchecked b cc) wb wc
  · exact ⟨wres.1, by simp [wres.2.1]⟩
  · rw [eval_arith (.add c) w1 w2 rfl] at e
    obtain ⟨s1, s2, hs1, hs2, e⟩ := evBinop_inv (.inl (.add c)) w1 w2 e
    rw [eval_arith (.add ck1) wa wb rfl] at hs1
    obtain ⟨A, B, hA, hB, hs1⟩ := evBinop_inv (.inl (.add ck1)) wa wb hs1
    rw [eval_arith (.sub ck2) wc wa rfl] at hs2
    obtain ⟨C, A', hC, hA', hs2⟩ := evBinop_inv (.inl (.sub ck2)) wc wa hs2
    rw [hA] at hA'; simp at hA'; subst hA'
    refine (hO.bv_add _ _ _).sem ρ v ?_
    rw [bv_add.spec, ty_eq, eval_arith (.add _) wb wc wb.2.1, hB, hC]
    simp [evBinop, checkedOp, bvBin, unchecked] at e hs1 hs2 ⊢
    obtain ⟨-, rfl⟩ := hs1; obtain ⟨-, rfl⟩ := hs2; obtain ⟨-, rfl⟩ := e
    congr 1; grind

theorem bv_add.r_add_sub.proof : bv_add.r_add_sub.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_add.r_add_sub] at h
  rcases orElse_eq_some h with h | h
  · split at h <;> simp [equal] at h; obtain ⟨rfl, rfl⟩ := h
    exact bv_add.add_sub_aux hO
  rcases orElse_eq_some h with h | h
  · split at h <;> simp [equal] at h; obtain ⟨rfl, rfl⟩ := h
    exact Refines.trans (Refines.binop (Refines.comm (.add _)) Refines.refl (fun _ => rfl))
      (bv_add.add_sub_aux hO)
  rcases orElse_eq_some h with h | h
  · split at h <;> simp [equal] at h; obtain ⟨rfl, rfl⟩ := h
    refine Refines.trans (Refines.comm' (.add _) (fun w => ?_)) (bv_add.add_sub_aux hO)
    obtain ⟨n, w1, w2, -⟩ := (WT_arith (.add c)).1 w
    simp [w1.2.1, w2.2.1]
  · split at h <;> simp [equal] at h; obtain ⟨rfl, rfl⟩ := h
    refine Refines.trans (Refines.comm' (.add _) (fun w => ?_))
      (Refines.trans (Refines.binop (Refines.comm (.add _)) Refines.refl (fun _ => rfl))
        (bv_add.add_sub_aux hO))
    obtain ⟨n, w1, w2, -⟩ := (WT_arith (.add c)).1 w
    have := w1.2.1; have := w2.2.1; simp_all

-- UNSOUND: the flags of the outer addition are given to the rebuilt multiplication, but the
-- original multiplications may wrap. Take 8 bits, `checked = {signed := true, unsigned := false}`,
-- v1 = Mul (unchecked, x, y), v2 = Mul (unchecked, x, z), with x = 2, y = 64, z = 0 (unsigned
-- representations; take `O` returning the raw spec terms). Then x*y wraps to 0x80 (-128), and
-- x*y + x*z = 0x80 without a signed overflow, so the spec is `some 0x80`. The result is
-- x *s (y +s z) = 2 *s 64, whose signed overflow makes it poison.
theorem bv_add.r_factor.proof : bv_add.r_factor.Stmt := by
  sorry

-- UNSOUND: `divisible` and `tdiv` are applied to the unsigned representations of the constants,
-- which is wrong for signed flags. Take 8 bits, `checked = ck1 = ck2 = {signed := true,
-- unsigned := false}`, v1 = Mul (ck1, 3, x), v2 = Mul (ck2, 255, y), with x = 0, y = 1 (take `O`
-- returning the raw spec terms). `divisible 255 3` holds and common = 85. The spec is
-- 3 *s 0 +s (-1) *s 1 = -1 = `some 0xff`, with no signed overflow. The result is
-- 3 *s (x +s 85 *s y) = 3 *s 85 = 255, which overflows as a signed product, so it is poison.
theorem bv_add.r_factor_const.proof : bv_add.r_factor_const.Stmt := by
  sorry

theorem bv_add.r_ite.proof : bv_add.r_ite.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_add.r_ite] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> subst h
  · simp only [bv_add.spec, ty_eq, Term.ty_mk]
    refine Refines.ite_push_l hO (.add c) (fun n wl wV hT => ?_) (fun n wr wV hT => ?_)
    all_goals subst hT; rw [size_of_ty_bitVector]
    · exact O_arith_lit (.add c) (hO.bv_add _ _ _) wl wV
    · exact O_arith_lit (.add c) (hO.bv_add _ _ _) wr wV
  · simp only [bv_add.spec, ty_eq, Term.ty_mk]
    refine Refines.ite_push_r hO (.add c) (fun n wl wV hT => ?_) (fun n wr wV hT => ?_)
    all_goals obtain ⟨rfl, -⟩ := BV_lit wV; rw [size_of_ty_bitVector]
    · exact O_arith_lit' (.add c) (.add c) (hO.bv_add _ _ _) wl wV
    · exact O_arith_lit' (.add c) (.add c) (hO.bv_add _ _ _) wr wV

theorem bv_add.r_default.proof : bv_add.r_default.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_add.r_default] at h; simp at h; subst h
  exact Refines.commut_binop (.add c)

theorem bv_sub.r_lits.proof : bv_sub.r_lits.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_sub.r_lits] at h; split at h <;> simp at h; subst h
  refine Refines.arith_intro (.sub c) (fun n wa wb hT => ?_) (fun n wa wb hT ρ x y v hx hy e => ?_)
  · rw [size_ty_lit wa]; exact BV_mk_masked wa.2.2
  · rw [size_ty_lit wa, eval_mk_masked wa.2.2]
    rw [lit_eval_eq wa hx, lit_eval_eq wb hy] at e
    simp [evBinop, checkedOp, bvBin] at e
    rw [← e.2, BitVec.ofInt_sub]

theorem bv_sub.r_zero_r.proof : bv_sub.r_zero_r.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_sub.r_zero_r] at h; split at h <;> simp at h; obtain ⟨rfl, rfl⟩ := h
  refine Refines.arith_intro (.sub c) (fun n wa wb hT => wa) (fun n wa wb hT ρ x y v hx hy e => ?_)
  rw [lit_eval_eq wb hy] at e
  simp [evBinop, checkedOp, bvBin] at e
  rw [hx, ← e.2]

theorem bv_sub.r_zero_l.proof : bv_sub.r_zero_l.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_sub.r_zero_l] at h; split at h <;> simp at h; obtain ⟨rfl, rfl⟩ := h
  refine Refines.arith_intro (.sub c) (fun n wa wb hT => (O_neg (hO.bv_neg _ _) wb).1)
    (fun n wa wb hT ρ x y v hx hy e => ?_)
  refine (O_neg (hO.bv_neg _ _) wb).2 ρ y v hy ?_
  rw [lit_eval_eq wa hx] at e
  simp [evBinop, evUnop, checkedOp, bvBin] at e ⊢
  obtain ⟨⟨h1, -⟩, rfl⟩ := e
  refine ⟨fun hs hy => ?_, by simp⟩
  have := h1 hs; subst hy
  rw [ssubOverflow_zero_intMin (by have := wa.2.2; omega)] at this; cases this

theorem bv_sub.r_same.proof : bv_sub.r_same.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_sub.r_same] at h; split at h <;> simp at h; subst h
  rename_i he; simp [equal] at he; subst he
  refine Refines.arith_intro (.sub c) (fun n wa wb hT => ?_) (fun n wa wb hT ρ x y v hx hy e => ?_)
  · simp only [size_eq, wa.2.1, size_of_ty_bitVector]; exact BV_bv_zero wa.2.2
  · rw [hx] at hy; simp at hy; subst hy
    simp [evBinop, checkedOp, bvBin] at e
    simp only [size_eq, wa.2.1, size_of_ty_bitVector]
    rw [eval_bv_zero wa.2.2, ← e.2]; simp

theorem bv_sub.r_neg_r.proof : bv_sub.r_neg_r.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_sub.r_neg_r] at h; split at h <;> simp at h; subst h
  rename_i ck x T
  refine Refines.arith_intro (.sub c) (fun n wa wb hT => ?_) (fun n wa wb hT ρ X y v hx hy e => ?_)
  · obtain ⟨wx, rfl⟩ := BV_neg_inv wb
    exact BV_arith (.add _) (hO.bv_add unchecked _ x) wa wx
  · obtain ⟨wx, rfl⟩ := BV_neg_inv wb
    rw [eval_neg wx rfl] at hy
    obtain ⟨x', hx', hy⟩ := evUnop_inv wx hy
    refine O_eval (.add _) (hO.bv_add _ _ _) wa wx hx hx' ?_
    simp [evBinop, evUnop, checkedOp, bvBin, unchecked] at e hy ⊢
    rw [← e.2, ← hy.2, BitVec.sub_neg]

theorem bv_sub.r_sub_const_l.proof : bv_sub.r_sub_const_l.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_sub.r_sub_const_l] at h; split at h <;> simp at h; subst h
  rename_i ck z1 Tc s T1 z2 T2
  simp only [bv_sub.spec, ty_eq, Term.ty_mk]
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  all_goals obtain ⟨n, wa, wb, rfl⟩ := (WT_arith (.sub c)).1 w
  all_goals obtain ⟨wc, ws, -⟩ := BV_arith_inv (.sub ck) wa
  all_goals obtain ⟨rfl, hz1⟩ := BV_lit wc
  all_goals obtain ⟨rfl, hz2⟩ := BV_lit wb
  all_goals have wi := BV_arith (.sub _) (hO.bv_sub unchecked _ _) wc wb
  all_goals have wres := BV_arith (.sub _) (hO.bv_sub (mask_checked_after_fold (checked_meet ck c)
    (.mk (.bitVec z1) (.bitVector n)) (.mk (.bitVec z2) (.bitVector n)) false) _ s) wi ws
  · exact ⟨wres.1, by simp [wres.2.1]⟩
  · rw [eval_arith (.sub c) wa wb rfl] at e
    obtain ⟨S, Y, hS, hY, e⟩ := evBinop_inv (.inl (.sub c)) wa wb e
    rw [eval_lit wb] at hY; simp at hY; subst hY
    rw [eval_arith (.sub ck) wc ws rfl] at hS
    obtain ⟨X, R, hX, hR, hS⟩ := evBinop_inv (.inl (.sub ck)) wc ws hS
    rw [eval_lit wc] at hX; simp at hX; subst hX
    have hi := (hO.bv_sub unchecked _ _).sem ρ (.bv n.toNat (BitVec.ofInt _ z1 - BitVec.ofInt _ z2))
      (by rw [bv_sub.spec, ty_eq, eval_arith (.sub _) wc wb wc.2.1, eval_lit wc, eval_lit wb]
          simp [evBinop, checkedOp, bvBin, unchecked])
    refine (hO.bv_sub _ _ _).sem ρ v ?_
    rw [bv_sub.spec, ty_eq, eval_arith (.sub _) wi ws wi.2.1, hi, hR, mask_lits,
      size_of_ty_bitVector, overflows_sub_lit wc.2.2 hz1.1 hz1.2 hz2.1 hz2.2,
      overflows_sub_lit wc.2.2 hz1.1 hz1.2 hz2.1 hz2.2]
    simp [evBinop, checkedOp, bvBin, checked_meet] at e hS ⊢
    obtain ⟨⟨e1, e2⟩, rfl⟩ := e; obtain ⟨⟨h1, h2⟩, rfl⟩ := hS
    refine ⟨⟨fun hck hc h3 => ssub_sub_reassoc (h1 hck) (e1 hc) h3,
      fun hck hc h3 => usub_sub_reassoc (h2 hck) (e2 hc) h3⟩, ?_⟩
    congr 1; rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg,
      BitVec.sub_eq_add_neg]; ac_rfl

theorem bv_sub.r_sub_const_r.proof : bv_sub.r_sub_const_r.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_sub.r_sub_const_r] at h; split at h <;> simp at h; subst h
  rename_i ck s z1 Tc T1 z2 T2
  simp only [bv_sub.spec, ty_eq, Term.ty_mk]
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  all_goals obtain ⟨n, wa, wb, rfl⟩ := (WT_arith (.sub c)).1 w
  all_goals obtain ⟨ws, wc, -⟩ := BV_arith_inv (.sub ck) wa
  all_goals obtain ⟨rfl, hz1⟩ := BV_lit wc
  all_goals obtain ⟨rfl, hz2⟩ := BV_lit wb
  all_goals have wi := BV_arith (.add _) (hO.bv_add unchecked _ _) wc wb
  all_goals have wres := BV_arith (.sub _) (hO.bv_sub (mask_checked_after_fold (checked_meet ck c)
    (.mk (.bitVec z1) (.bitVector n)) (.mk (.bitVec z2) (.bitVector n)) true) s _) ws wi
  · exact ⟨wres.1, by simp [wres.2.1]⟩
  · rw [eval_arith (.sub c) wa wb rfl] at e
    obtain ⟨S, Y, hS, hY, e⟩ := evBinop_inv (.inl (.sub c)) wa wb e
    rw [eval_lit wb] at hY; simp at hY; subst hY
    rw [eval_arith (.sub ck) ws wc rfl] at hS
    obtain ⟨R, X, hR, hX, hS⟩ := evBinop_inv (.inl (.sub ck)) ws wc hS
    rw [eval_lit wc] at hX; simp at hX; subst hX
    have hi := (hO.bv_add unchecked _ _).sem ρ (.bv n.toNat (BitVec.ofInt _ z1 + BitVec.ofInt _ z2))
      (by rw [bv_add.spec, ty_eq, eval_arith (.add _) wc wb wc.2.1, eval_lit wc, eval_lit wb]
          simp [evBinop, checkedOp, bvBin, unchecked])
    refine (hO.bv_sub _ _ _).sem ρ v ?_
    rw [bv_sub.spec, ty_eq, eval_arith (.sub _) ws wi ws.2.1, hi, hR, mask_lits,
      size_of_ty_bitVector, overflows_add_lit wc.2.2 hz1.1 hz1.2 hz2.1 hz2.2,
      overflows_add_lit wc.2.2 hz1.1 hz1.2 hz2.1 hz2.2]
    simp [evBinop, checkedOp, bvBin, checked_meet] at e hS ⊢
    obtain ⟨⟨e1, e2⟩, rfl⟩ := e; obtain ⟨⟨h1, h2⟩, rfl⟩ := hS
    refine ⟨⟨fun hck hc h3 => ssub_sub_reassoc' (h1 hck) (e1 hc) h3,
      fun hck hc h3 => usub_sub_reassoc' (h2 hck) (e2 hc) h3⟩, ?_⟩
    congr 1; grind

theorem bv_sub.const_add_aux {FS : FloatSem} {O : Ops} (hO : O.Sound FS) {c ck z1 T1 z2 T2 l T} :
    Refines FS (bv_sub.spec c (.mk (.bitVec z1) T1) (.mk (.binop (.add ck) (.mk (.bitVec z2) T2) l) T))
      (O.bv_sub (mask_checked_after_fold (checked_meet ck c) (.mk (.bitVec z1) T1)
          (.mk (.bitVec z2) T2) false)
        (O.bv_sub unchecked (.mk (.bitVec z1) T1) (.mk (.bitVec z2) T2)) l) := by
  simp only [bv_sub.spec, ty_eq, Term.ty_mk]
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  all_goals obtain ⟨n, wa, wb, hT⟩ := (WT_arith (.sub c)).1 w
  all_goals obtain ⟨wc, wl, rfl⟩ := BV_arith_inv (.add ck) wb
  all_goals obtain ⟨rfl, hz1⟩ := BV_lit wa
  all_goals obtain ⟨rfl, hz2⟩ := BV_lit wc
  all_goals have wi := BV_arith (.sub _) (hO.bv_sub unchecked _ _) wa wc
  all_goals have wres := BV_arith (.sub _) (hO.bv_sub (mask_checked_after_fold (checked_meet ck c)
    (.mk (.bitVec z1) (.bitVector n)) (.mk (.bitVec z2) (.bitVector n)) false) _ l) wi wl
  · exact ⟨wres.1, by simp [wres.2.1]⟩
  · rw [eval_arith (.sub c) wa wb rfl] at e
    obtain ⟨X, S, hX, hS, e⟩ := evBinop_inv (.inl (.sub c)) wa wb e
    rw [eval_lit wa] at hX; simp at hX; subst hX
    rw [eval_arith (.add ck) wc wl rfl] at hS
    obtain ⟨Z, L, hZ, hL, hS⟩ := evBinop_inv (.inl (.add ck)) wc wl hS
    rw [eval_lit wc] at hZ; simp at hZ; subst hZ
    have hi := (hO.bv_sub unchecked _ _).sem ρ (.bv n.toNat (BitVec.ofInt _ z1 - BitVec.ofInt _ z2))
      (by rw [bv_sub.spec, ty_eq, eval_arith (.sub _) wa wc wa.2.1, eval_lit wc, eval_lit wa]
          simp [evBinop, checkedOp, bvBin, unchecked])
    refine (hO.bv_sub _ _ _).sem ρ v ?_
    rw [bv_sub.spec, ty_eq, eval_arith (.sub _) wi wl wi.2.1, hi, hL, mask_lits,
      size_of_ty_bitVector, overflows_sub_lit wa.2.2 hz1.1 hz1.2 hz2.1 hz2.2,
      overflows_sub_lit wa.2.2 hz1.1 hz1.2 hz2.1 hz2.2]
    simp [evBinop, checkedOp, bvBin, checked_meet] at e hS ⊢
    obtain ⟨⟨e1, e2⟩, rfl⟩ := e; obtain ⟨⟨h1, h2⟩, rfl⟩ := hS
    refine ⟨⟨fun hck hc h3 => sadd_sub_reassoc (h1 hck) (e1 hc) h3,
      fun hck hc h3 => uadd_sub_reassoc (h2 hck) (e2 hc) h3⟩, ?_⟩
    congr 1; grind

theorem bv_sub.r_const_add.proof : bv_sub.r_const_add.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_sub.r_const_add] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> subst h
  · exact bv_sub.const_add_aux hO
  · rename_i T
    refine Refines.trans ?_ (bv_sub.const_add_aux hO (T := T))
    exact Refines.binop Refines.refl (Refines.comm (.add _)) (fun _ => rfl)

theorem bv_sub.add_const_aux {FS : FloatSem} {O : Ops} (hO : O.Sound FS) {c ck z1 T1 l T z2 T2} :
    Refines FS (bv_sub.spec c (.mk (.binop (.add ck) (.mk (.bitVec z1) T1) l) T) (.mk (.bitVec z2) T2))
      (if decide (z1 < z2) = true then
        O.bv_sub (mask_checked_after_fold (checked_meet ck c) (.mk (.bitVec z2) T2)
          (.mk (.bitVec z1) T1) false) l
          (O.bv_neg false (O.bv_sub unchecked (.mk (.bitVec z1) T1) (.mk (.bitVec z2) T2)))
      else
        O.bv_add (mask_checked_after_fold (checked_meet ck c) (.mk (.bitVec z1) T1)
          (.mk (.bitVec z2) T2) false) l
          (O.bv_sub unchecked (.mk (.bitVec z1) T1) (.mk (.bitVec z2) T2))) := by
  simp only [bv_sub.spec, ty_eq, Term.ty_mk]
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  all_goals obtain ⟨n, wa, wb, rfl⟩ := (WT_arith (.sub c)).1 w
  all_goals obtain ⟨wc, wl, -⟩ := BV_arith_inv (.add ck) wa
  all_goals obtain ⟨rfl, hz1⟩ := BV_lit wc
  all_goals obtain ⟨rfl, hz2⟩ := BV_lit wb
  all_goals have wi := BV_arith (.sub _) (hO.bv_sub unchecked _ _) wc wb
  all_goals have wn := O_neg (hO.bv_neg false _) wi
  · split
    · have := BV_arith (.sub _) (hO.bv_sub (mask_checked_after_fold (checked_meet ck c)
        (.mk (.bitVec z2) (.bitVector n)) (.mk (.bitVec z1) (.bitVector n)) false) l _) wl wn.1
      exact ⟨this.1, by simp [this.2.1]⟩
    · have := BV_arith (.add _) (hO.bv_add (mask_checked_after_fold (checked_meet ck c)
        (.mk (.bitVec z1) (.bitVector n)) (.mk (.bitVec z2) (.bitVector n)) false) l _) wl wi
      exact ⟨this.1, by simp [this.2.1]⟩
  · rw [eval_arith (.sub c) wa wb rfl] at e
    obtain ⟨S, Y, hS, hY, e⟩ := evBinop_inv (.inl (.sub c)) wa wb e
    rw [eval_lit wb] at hY; simp at hY; subst hY
    rw [eval_arith (.add ck) wc wl rfl] at hS
    obtain ⟨Z, L, hZ, hL, hS⟩ := evBinop_inv (.inl (.add ck)) wc wl hS
    rw [eval_lit wc] at hZ; simp at hZ; subst hZ
    have hi := (hO.bv_sub unchecked _ _).sem ρ (.bv n.toNat (BitVec.ofInt _ z1 - BitVec.ofInt _ z2))
      (by rw [bv_sub.spec, ty_eq, eval_arith (.sub _) wc wb wc.2.1, eval_lit wc, eval_lit wb]
          simp [evBinop, checkedOp, bvBin, unchecked])
    simp [evBinop, checkedOp, bvBin] at e hS
    obtain ⟨⟨e1, e2⟩, rfl⟩ := e; obtain ⟨⟨h1, h2⟩, rfl⟩ := hS
    split
    · have hn := wn.2 ρ (BitVec.ofInt _ z1 - BitVec.ofInt _ z2)
        (.bv n.toNat (-(BitVec.ofInt _ z1 - BitVec.ofInt _ z2))) hi (by simp [evUnop])
      refine (hO.bv_sub _ _ _).sem ρ _ ?_
      rw [bv_sub.spec, ty_eq, eval_arith (.sub _) wl wn.1 wl.2.1, hn, hL, mask_lits,
        size_of_ty_bitVector, overflows_sub_lit wc.2.2 hz2.1 hz2.2 hz1.1 hz1.2,
        overflows_sub_lit wc.2.2 hz2.1 hz2.2 hz1.1 hz1.2]
      simp only [BitVec.neg_sub]
      simp [evBinop, checkedOp, bvBin, checked_meet]
      rw [show -BitVec.ofInt n.toNat z1 + BitVec.ofInt n.toNat z2 =
        BitVec.ofInt n.toNat z2 - BitVec.ofInt n.toNat z1 by grind]
      refine ⟨⟨fun hck hc h3 => sadd_sub_reassoc' (h1 hck) (e1 hc) h3,
        fun hck hc h3 => uadd_sub_reassoc' (h2 hck) (e2 hc) h3⟩, ?_⟩
      grind
    · refine (hO.bv_add _ _ _).sem ρ _ ?_
      rw [bv_add.spec, ty_eq, eval_arith (.add _) wl wi wl.2.1, hi, hL, mask_lits,
        size_of_ty_bitVector, overflows_sub_lit wc.2.2 hz1.1 hz1.2 hz2.1 hz2.2,
        overflows_sub_lit wc.2.2 hz1.1 hz1.2 hz2.1 hz2.2]
      simp [evBinop, checkedOp, bvBin, checked_meet]
      refine ⟨⟨fun hck hc h3 => sadd_sub_reassoc'' (h1 hck) (e1 hc) h3,
        fun hck hc h3 => uadd_sub_reassoc'' (h2 hck) (e2 hc) h3⟩, ?_⟩
      congr 1; grind

theorem bv_sub.r_add_const.proof : bv_sub.r_add_const.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_sub.r_add_const] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
  · exact bv_sub.add_const_aux hO
  · rename_i T _ _
    refine Refines.trans ?_ (bv_sub.add_const_aux hO (T := T))
    exact Refines.binop (Refines.comm (.add _)) Refines.refl (fun _ => rfl)

theorem bv_sub.r_add_cancel_l.proof : bv_sub.r_add_cancel_l.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_sub.r_add_cancel_l] at h; split at h <;> simp [equal] at h; obtain ⟨rfl, rfl⟩ := h
  rename_i ck _ _ T
  refine Refines.arith_intro (.sub c) (fun n wa wb hT => (BV_arith_inv (.add ck) wa).2.1)
    (fun n wa wb hT ρ x y v hx hy e => ?_)
  obtain ⟨wl, wr, rfl⟩ := BV_arith_inv (.add ck) wa
  rw [eval_arith (.add ck) wl wr rfl] at hx
  obtain ⟨L, R, hL, hR, hx⟩ := evBinop_inv (.inl (.add ck)) wl wr hx
  rw [hL] at hy; simp at hy; subst hy
  simp [evBinop, checkedOp, bvBin] at hx e
  obtain ⟨-, rfl⟩ := hx; obtain ⟨-, rfl⟩ := e
  rw [hR]; congr 2; grind

theorem bv_sub.r_add_cancel_r.proof : bv_sub.r_add_cancel_r.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_sub.r_add_cancel_r] at h; split at h <;> simp [equal] at h; obtain ⟨rfl, rfl⟩ := h
  rename_i ck _ _ T
  refine Refines.arith_intro (.sub c) (fun n wa wb hT => (BV_arith_inv (.add ck) wa).1)
    (fun n wa wb hT ρ x y v hx hy e => ?_)
  obtain ⟨wl, wr, rfl⟩ := BV_arith_inv (.add ck) wa
  rw [eval_arith (.add ck) wl wr rfl] at hx
  obtain ⟨L, R, hL, hR, hx⟩ := evBinop_inv (.inl (.add ck)) wl wr hx
  rw [hR] at hy; simp at hy; subst hy
  simp [evBinop, checkedOp, bvBin] at hx e
  obtain ⟨-, rfl⟩ := hx; obtain ⟨-, rfl⟩ := e
  rw [hL]; congr 2; grind

-- UNSOUND: the flags of the outer subtraction are kept, but the inner additions may wrap. Take
-- 8 bits, `checked = {signed := true, unsigned := false}`, v1 = Add (unchecked, l, r1),
-- v2 = Add (unchecked, l, r2), with l = 1, r1 = 127, r2 = 0xff (take `O` returning the raw spec
-- terms). Then l + r1 = 0x80 (-128) and l + r2 = 0, and -128 -s 0 = -128 has no signed overflow,
-- so the spec is `some 0x80`. The result is r1 -s r2 = 127 -s (-1), whose signed overflow makes it
-- poison.
theorem bv_sub.r_add_add.proof : bv_sub.r_add_add.Stmt := by
  sorry

theorem bv_sub.r_sub_sub.proof : bv_sub.r_sub_sub.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_sub.r_sub_sub] at h; split at h <;> simp [equal] at h; obtain ⟨rfl, rfl⟩ := h
  rename_i ck _ T
  refine Refines.arith_intro (.sub c) (fun n wa wb hT => (BV_arith_inv (.sub ck) wb).2.1)
    (fun n wa wb hT ρ x y v hx hy e => ?_)
  obtain ⟨wl, wr, rfl⟩ := BV_arith_inv (.sub ck) wb
  rw [eval_arith (.sub ck) wl wr rfl] at hy
  obtain ⟨L, R, hL, hR, hy⟩ := evBinop_inv (.inl (.sub ck)) wl wr hy
  rw [hL] at hx; simp at hx; subst hx
  simp [evBinop, checkedOp, bvBin] at hy e
  obtain ⟨-, rfl⟩ := hy; obtain ⟨-, rfl⟩ := e
  rw [hR]; congr 2; grind

theorem bv_sub.r_ite_ite.proof : bv_sub.r_ite_ite.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_sub.r_ite_ite] at h; split at h <;> simp [equal] at h; obtain ⟨rfl, rfl⟩ := h
  rename_i g l r T l' r' T'
  refine Refines.arith_intro (.sub c) (fun n wa wb hT => ?_) (fun n wa wb hT ρ x y v hx hy e => ?_)
  all_goals obtain ⟨wg, hg, wl, wr, rfl⟩ := BV_ite_inv wa
  all_goals obtain ⟨-, -, wl', wr', rfl⟩ := BV_ite_inv wb
  all_goals have hA := O_arith (.sub _) (hO.bv_sub unchecked l l') wl wl'
  all_goals have hB := O_arith (.sub _) (hO.bv_sub unchecked r r') wr wr'
  all_goals have hres := O_ite hO wg hg hA.1 hB.1
  · exact hres.1
  · refine hres.2 ρ v ?_
    rcases eval_ite_inv hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases eval_ite_inv hy with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;> rw [h1] at h1' <;> simp at h1'
    · exact .inl ⟨h1, hA.2 ρ v (by rw [h2, h2']; exact evBinop_sub_unchecked e)⟩
    · exact .inr ⟨h1, hB.2 ρ v (by rw [h2, h2']; exact evBinop_sub_unchecked e)⟩

theorem bv_sub.r_ite_l.proof : bv_sub.r_ite_l.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_sub.r_ite_l] at h; split at h <;> simp at h; subst h
  simp only [bv_sub.spec, ty_eq, Term.ty_mk]
  refine Refines.ite_push_l hO (.sub c) (fun n wl wV hT => ?_) (fun n wr wV hT => ?_)
  · have := O_arith (.sub _) (hO.bv_sub unchecked _ _) wl wV
    exact ⟨this.1, fun ρ v e => this.2 ρ v (evBinop_sub_unchecked e)⟩
  · have := O_arith (.sub _) (hO.bv_sub unchecked _ _) wr wV
    exact ⟨this.1, fun ρ v e => this.2 ρ v (evBinop_sub_unchecked e)⟩

theorem bv_sub.r_ite_r.proof : bv_sub.r_ite_r.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_sub.r_ite_r] at h; split at h <;> simp at h; subst h
  simp only [bv_sub.spec, ty_eq, Term.ty_mk]
  refine Refines.ite_push_r hO (.sub c) (fun n wl wV hT => ?_) (fun n wr wV hT => ?_)
  · have := O_arith (.sub _) (hO.bv_sub unchecked _ _) wV wl
    exact ⟨this.1, fun ρ v e => this.2 ρ v (evBinop_sub_unchecked e)⟩
  · have := O_arith (.sub _) (hO.bv_sub unchecked _ _) wV wr
    exact ⟨this.1, fun ρ v e => this.2 ρ v (evBinop_sub_unchecked e)⟩

theorem bv_sub.r_of_bool_l.proof : bv_sub.r_of_bool_l.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_sub.r_of_bool_l] at h; split at h <;> simp at h; subst h
  rename_i m g T z T2
  refine Refines.arith_intro (.sub c) (fun n wa wb hT => ?_) (fun n wa wb hT ρ x y v hx hy e => ?_)
  all_goals obtain ⟨rfl, wg, hg, rfl⟩ := BV_ofBool_inv wa
  all_goals have hA := O_arith (.sub _) (hO.bv_sub unchecked (bv_one m) _) (BV_bv_one wb.2.2) wb
  all_goals have hB := O_neg (hO.bv_neg false _) wb
  all_goals have hres := O_ite hO wg hg hA.1 hB.1
  · exact hres.1
  · refine hres.2 ρ v ?_
    obtain ⟨b, hb, rfl⟩ := eval_ofBool_inv wa hx
    cases b
    · refine .inr ⟨hb, hB.2 ρ y v hy ?_⟩
      simp [evBinop, evUnop, checkedOp, bvBin] at e ⊢; rw [← e.2]
    · refine .inl ⟨hb, hA.2 ρ v ?_⟩
      rw [eval_bv_one wb.2.2, hy]
      simp [evBinop, checkedOp, bvBin, unchecked] at e ⊢; exact e.2

theorem bv_sub.r_of_bool_r.proof : bv_sub.r_of_bool_r.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_sub.r_of_bool_r] at h; split at h <;> simp at h; subst h
  rename_i z T1 m g T
  refine Refines.arith_intro (.sub c) (fun n wa wb hT => ?_) (fun n wa wb hT ρ x y v hx hy e => ?_)
  all_goals obtain ⟨rfl, wg, hg, rfl⟩ := BV_ofBool_inv wb
  all_goals have hA := O_arith (.sub _) (hO.bv_sub unchecked _ (bv_one m)) wa (BV_bv_one wa.2.2)
  all_goals have hres := O_ite hO wg hg hA.1 wa
  · exact hres.1
  · refine hres.2 ρ v ?_
    obtain ⟨b, hb, rfl⟩ := eval_ofBool_inv wb hy
    cases b
    · refine .inr ⟨hb, ?_⟩
      simp [evBinop, checkedOp, bvBin] at e; rw [hx, ← e.2]
    · refine .inl ⟨hb, hA.2 ρ v ?_⟩
      rw [eval_bv_one wa.2.2, hx]
      simp [evBinop, checkedOp, bvBin, unchecked] at e ⊢; exact e.2

theorem bv_sub.r_default.proof : bv_sub.r_default.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_sub.r_default] at h; simp at h; subst h
  exact Refines.refl

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
  sorry

theorem bv_mod.r_default.proof : bv_mod.r_default.Stmt := by
  sorry

theorem bv_rem.r_lits.proof : bv_rem.r_lits.Stmt := by
  sorry

theorem bv_rem.r_zero_l.proof : bv_rem.r_zero_l.Stmt := by
  sorry

theorem bv_rem.r_one_r.proof : bv_rem.r_one_r.Stmt := by
  sorry

theorem bv_rem.r_pow2.proof : bv_rem.r_pow2.Stmt := by
  sorry

theorem bv_rem.r_add.proof : bv_rem.r_add.Stmt := by
  sorry

theorem bv_rem.r_rem_rem.proof : bv_rem.r_rem_rem.Stmt := by
  sorry

theorem bv_rem.r_default.proof : bv_rem.r_default.Stmt := by
  sorry

theorem bv_mul.r_lits.proof : bv_mul.r_lits.Stmt := by
  sorry

theorem bv_mul.r_one_r.proof : bv_mul.r_one_r.Stmt := by
  sorry

theorem bv_mul.r_one_l.proof : bv_mul.r_one_l.Stmt := by
  sorry

theorem bv_mul.r_zero_r.proof : bv_mul.r_zero_r.Stmt := by
  sorry

theorem bv_mul.r_zero_l.proof : bv_mul.r_zero_l.Stmt := by
  sorry

theorem bv_mul.r_neg.proof : bv_mul.r_neg.Stmt := by
  sorry

theorem bv_mul.r_mul_const.proof : bv_mul.r_mul_const.Stmt := by
  sorry

theorem bv_mul.r_ite.proof : bv_mul.r_ite.Stmt := by
  sorry

theorem bv_mul.r_default.proof : bv_mul.r_default.Stmt := by
  sorry

theorem bv_div.r_lits.proof : bv_div.r_lits.Stmt := by
  sorry

theorem bv_div.r_one.proof : bv_div.r_one.Stmt := by
  sorry

theorem bv_div.r_mul_lits.proof : bv_div.r_mul_lits.Stmt := by
  sorry

theorem bv_div.r_mul_div.proof : bv_div.r_mul_div.Stmt := by
  sorry

theorem bv_div.r_div_mul.proof : bv_div.r_div_mul.Stmt := by
  sorry

theorem bv_div.r_div_div.proof : bv_div.r_div_div.Stmt := by
  sorry

theorem bv_div.r_zext.proof : bv_div.r_zext.Stmt := by
  sorry

theorem bv_div.r_default.proof : bv_div.r_default.Stmt := by
  sorry

theorem bv_add_overflows.r_lits.proof : bv_add_overflows.r_lits.Stmt := by
  sorry

theorem bv_add_overflows.r_zero.proof : bv_add_overflows.r_zero.Stmt := by
  sorry

theorem bv_add_overflows.r_size1.proof : bv_add_overflows.r_size1.Stmt := by
  sorry

theorem bv_add_overflows.r_unsigned.proof : bv_add_overflows.r_unsigned.Stmt := by
  sorry

theorem bv_add_overflows.r_signed.proof : bv_add_overflows.r_signed.Stmt := by
  sorry

theorem bv_add_overflows.r_of_bools.proof : bv_add_overflows.r_of_bools.Stmt := by
  sorry

theorem bv_add_overflows.r_of_bool.proof : bv_add_overflows.r_of_bool.Stmt := by
  sorry

theorem bv_add_overflows.r_default.proof : bv_add_overflows.r_default.Stmt := by
  sorry

theorem bv_mul_overflows.r_lits.proof : bv_mul_overflows.r_lits.Stmt := by
  sorry

theorem bv_mul_overflows.r_size1.proof : bv_mul_overflows.r_size1.Stmt := by
  sorry

theorem bv_mul_overflows.r_msb.proof : bv_mul_overflows.r_msb.Stmt := by
  sorry

theorem bv_mul_overflows.r_const.proof : bv_mul_overflows.r_const.Stmt := by
  sorry

theorem bv_mul_overflows.r_div.proof : bv_mul_overflows.r_div.Stmt := by
  sorry

theorem bv_mul_overflows.r_default.proof : bv_mul_overflows.r_default.Stmt := by
  sorry

theorem bv_neg_overflows.r_main.proof : bv_neg_overflows.r_main.Stmt := by
  sorry

theorem bv_sub_overflows.r_lits.proof : bv_sub_overflows.r_lits.Stmt := by
  sorry

theorem bv_sub_overflows.r_same.proof : bv_sub_overflows.r_same.Stmt := by
  sorry

theorem bv_sub_overflows.r_unsigned.proof : bv_sub_overflows.r_unsigned.Stmt := by
  sorry

theorem bv_sub_overflows.r_default.proof : bv_sub_overflows.r_default.Stmt := by
  sorry

end Bvr
