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

theorem bv_add.factor_aux {FS : FloatSem} {O : Ops} (hO : O.Sound FS) {c ck1 ck2 a b cc T1 T2 T} :
    Refines FS (.mk (.binop (.add c) (.mk (.binop (.mul ck1) a b) T1) (.mk (.binop (.mul ck2) a cc) T2)) T)
      (O.bv_mul unchecked a (O.bv_add unchecked b cc)) := by
  refine Refines.arith_intro (.add c) (fun n w1 w2 hT => ?_) (fun n w1 w2 hT ρ P Q v hp hq e => ?_)
  all_goals obtain ⟨wa, wb, rfl⟩ := BV_arith_inv (.mul _) w1
  all_goals obtain ⟨-, wc, rfl⟩ := BV_arith_inv (.mul _) w2
  all_goals have hs := O_arith (.add _) (hO.bv_add unchecked b cc) wb wc
  all_goals have hm := O_arith (.mul _) (hO.bv_mul unchecked a _) wa hs.1
  · exact hm.1
  · rw [eval_arith (.mul _) wa wb rfl] at hp
    obtain ⟨A, B, hA, hB, hp⟩ := evBinop_inv (.inl (.mul _)) wa wb hp
    rw [eval_arith (.mul _) wa wc rfl] at hq
    obtain ⟨A', C, hA', hC, hq⟩ := evBinop_inv (.inl (.mul _)) wa wc hq
    rw [hA] at hA'; simp at hA'; subst hA'
    have hS := O_eval (.add _) (hO.bv_add unchecked b cc) wb wc hB hC (v := .bv _ (B + C))
      (by simp [evBinop, checkedOp, bvBin, unchecked])
    refine O_eval (.mul _) (hO.bv_mul _ _ _) wa hs.1 hA hS ?_
    simp [evBinop, checkedOp, bvBin, unchecked] at hp hq e ⊢
    obtain ⟨-, rfl⟩ := hp; obtain ⟨-, rfl⟩ := hq; obtain ⟨-, rfl⟩ := e
    rw [BitVec.mul_add]

theorem bv_add.r_factor.proof : bv_add.r_factor.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_add.r_factor] at h
  rcases orElse_eq_some h with h | h
  · split at h <;> simp [equal] at h; obtain ⟨rfl, rfl⟩ := h
    exact bv_add.factor_aux hO
  rcases orElse_eq_some h with h | h
  · split at h <;> simp [equal] at h; obtain ⟨rfl, rfl⟩ := h
    exact Refines.trans (Refines.binop Refines.refl (Refines.comm (.mul _)) (fun _ => rfl))
      (bv_add.factor_aux hO)
  rcases orElse_eq_some h with h | h
  · split at h <;> simp [equal] at h; obtain ⟨rfl, rfl⟩ := h
    exact Refines.trans (Refines.binop (Refines.comm (.mul _)) Refines.refl (fun _ => rfl))
      (bv_add.factor_aux hO)
  · split at h <;> simp [equal] at h; obtain ⟨rfl, rfl⟩ := h
    exact Refines.trans (Refines.binop (Refines.comm (.mul _)) (Refines.comm (.mul _))
      (fun _ => rfl)) (bv_add.factor_aux hO)

theorem bv_add.factor_const_aux {FS : FloatSem} {O : Ops} (hO : O.Sound FS)
    {c ck1 ck2 l1 T1 r1 S1 l2 T2 r2 S2 T N} (hc : c.unsigned = true) (h1 : ck1.unsigned = true)
    (h2 : ck2.unsigned = true) (hd : l1 ∣ l2) (hN : ∀ n, S1 = .bitVector n → S2 = .bitVector n → N = n) :
    Refines FS (.mk (.binop (.add c) (.mk (.binop (.mul ck1) (.mk (.bitVec l1) T1) r1) S1)
        (.mk (.binop (.mul ck2) (.mk (.bitVec l2) T2) r2) S2)) T)
      (O.bv_mul checked_unsigned (.mk (.bitVec l1) T1) (O.bv_add checked_unsigned r1
        (O.bv_mul checked_unsigned (mk_bv N (tdiv l2 l1)) r2))) := by
  refine Refines.arith_intro (.add c) (fun n w1 w2 hT => ?_) (fun n w1 w2 hT ρ P Q v hp hq e => ?_)
  all_goals obtain ⟨wl1, wr1, rfl⟩ := BV_arith_inv (.mul _) w1
  all_goals obtain ⟨wl2, wr2, rfl⟩ := BV_arith_inv (.mul _) w2
  all_goals obtain rfl := hN n rfl rfl
  all_goals obtain ⟨rfl, hz1⟩ := BV_lit wl1
  all_goals obtain ⟨rfl, hz2⟩ := BV_lit wl2
  all_goals have hk := BV_mk_bv (n := N) (z := tdiv l2 l1) w1.2.2
  all_goals have m2 := O_arith (.mul _) (hO.bv_mul checked_unsigned _ r2) hk wr2
  all_goals have s := O_arith (.add _) (hO.bv_add checked_unsigned r1 _) wr1 m2.1
  all_goals have m1 := O_arith (.mul _) (hO.bv_mul checked_unsigned _ _) wl1 s.1
  · exact m1.1
  · rw [eval_arith (.mul _) wl1 wr1 rfl] at hp
    obtain ⟨L1, R1, hL1, hR1, hp⟩ := evBinop_inv (.inl (.mul _)) wl1 wr1 hp
    obtain rfl := lit_eval_eq wl1 hL1
    rw [eval_arith (.mul _) wl2 wr2 rfl] at hq
    obtain ⟨L2, R2, hL2, hR2, hq⟩ := evBinop_inv (.inl (.mul _)) wl2 wr2 hq
    obtain rfl := lit_eval_eq wl2 hL2
    simp [evBinop, checkedOp, bvBin] at hp hq e
    obtain ⟨⟨-, hp1⟩, rfl⟩ := hp; obtain ⟨⟨-, hq1⟩, rfl⟩ := hq; obtain ⟨⟨-, he1⟩, rfl⟩ := e
    obtain ⟨t0, t1, t2, t3⟩ := tdiv_facts hz1.1 hz2.1 hd
    have hK : (BitVec.ofInt N.toNat (tdiv l2 l1)).toNat = (l2.tdiv l1).toNat :=
      lit_toNat (w := N.toNat) t0 (by simp only [tdiv]; omega)
    obtain ⟨k1, k2, k3, hv⟩ := factor_const_bv (K := BitVec.ofInt N.toNat (tdiv l2 l1))
      (by rw [lit_toNat hz1.1 hz1.2, lit_toNat hz2.1 hz2.2, hK]; exact t2)
      (by
        intro h; rw [lit_toNat hz1.1 hz1.2] at h
        obtain rfl : l1 = 0 := by omega
        rw [hK, t3 (Int.zero_dvd.1 hd)]; rfl)
      (hp1 h1) (hq1 h2) (he1 hc)
    have hM2 := m2.2 ρ (.bv _ (BitVec.ofInt N.toNat (tdiv l2 l1) * R2))
      (by rw [mk_bv, eval_mk_masked w1.2.2, hR2]; simp [evBinop, checkedOp, bvBin, checked_unsigned, k1])
    have hS := s.2 ρ (.bv _ (R1 + BitVec.ofInt N.toNat (tdiv l2 l1) * R2))
      (by rw [hR1, hM2]; simp [evBinop, checkedOp, bvBin, checked_unsigned, k2])
    refine m1.2 ρ _ ?_
    rw [eval_lit wl1, hS]; simp [evBinop, checkedOp, bvBin, checked_unsigned, k3, hv]

theorem bv_add.factor_const_v1 {FS : FloatSem} {O : Ops} (hO : O.Sound FS)
    {c ck1 ck2 l1 T1 r1 S1 l2 T2 r2 S2 T}
    (hm : (checked_meet (checked_meet c ck1) ck2).unsigned = true)
    (hdv : divisible l1 l2 = true ∨ divisible l2 l1 = true) :
    Refines FS (.mk (.binop (.add c) (.mk (.binop (.mul ck1) (.mk (.bitVec l1) T1) r1) S1)
        (.mk (.binop (.mul ck2) (.mk (.bitVec l2) T2) r2) S2)) T)
      (if divisible l2 l1 = true then
        O.bv_mul checked_unsigned (.mk (.bitVec l1) T1) (O.bv_add checked_unsigned r1
          (O.bv_mul checked_unsigned (mk_bv (size_of_ty S1) (tdiv l2 l1)) r2))
      else
        O.bv_mul checked_unsigned (.mk (.bitVec l2) T2) (O.bv_add checked_unsigned r2
          (O.bv_mul checked_unsigned (mk_bv (size_of_ty S1) (tdiv l1 l2)) r1))) := by
  simp only [checked_meet, Bool.and_eq_true] at hm
  obtain ⟨⟨hc, h1⟩, h2⟩ := hm
  split
  · rename_i hd; simp [divisible] at hd
    exact bv_add.factor_const_aux hO hc h1 h2 hd (fun n h _ => by simp [h])
  · rename_i hd
    have hd' : l2 ∣ l1 := by
      simp [divisible] at hd hdv; rcases hdv with h | h
      · exact h
      · exact absurd h hd
    exact Refines.trans (Refines.comm (.add c))
      (bv_add.factor_const_aux hO hc h2 h1 hd' (fun n _ h => by simp [h]))

theorem bv_add.r_factor_const.proof : bv_add.r_factor_const.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_add.r_factor_const] at h
  rcases orElse_eq_some h with h | h
  · split at h <;> simp at h; obtain ⟨⟨hm, hdv⟩, rfl⟩ := h
    exact bv_add.factor_const_v1 hO hm hdv
  rcases orElse_eq_some h with h | h
  · split at h <;> simp at h; obtain ⟨⟨hm, hdv⟩, rfl⟩ := h
    exact Refines.trans (Refines.binop Refines.refl (Refines.comm (.mul _)) (fun _ => rfl))
      (bv_add.factor_const_v1 hO hm hdv)
  rcases orElse_eq_some h with h | h
  · split at h <;> simp at h; obtain ⟨⟨hm, hdv⟩, rfl⟩ := h
    exact Refines.trans (Refines.binop (Refines.comm (.mul _)) Refines.refl (fun _ => rfl))
      (bv_add.factor_const_v1 hO hm hdv)
  · split at h <;> simp at h; obtain ⟨⟨hm, hdv⟩, rfl⟩ := h
    exact Refines.trans (Refines.binop (Refines.comm (.mul _)) (Refines.comm (.mul _))
      (fun _ => rfl)) (bv_add.factor_const_v1 hO hm hdv)

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

-- UNSOUND: `is_pow2 1` holds, and then the bit-width is `log2 1 = 0`, so the rule extracts the
-- empty range `0 .. -1`. Take 8 bits, `signed = false`, v1 a variable x = 5 and v2 the literal 1
-- (take `O` returning the raw spec terms). The spec `x %u 1` is well-typed and is `some 0`. The
-- result is `Extend (false, 8, Extract (0, -1, x))`, whose extraction is ill-typed, so the result
-- is not well-typed (and is poison). In `bv_rem.step`, `r_one_r` fires first on this input.
theorem bv_rem.r_pow2.proof : bv_rem.r_pow2.Stmt := by
  sorry

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

-- UNSOUND: a zero modulus divides everything as far as `trem` is concerned (`trem 0 r2 = 0`), but
-- `x %u 0 = x`. Take 8 bits, `signed = false`, v1 = Rem (false, x, 0), v2 = 2, with x = 5 (take
-- `O` returning the raw spec terms). Then `0 = trem 0 2` and `zmin 0 2 = 0`, so the result is
-- `x %u 0 = some 5`, while the spec is `(5 %u 0) %u 2 = 5 %u 2 = some 1`.
theorem bv_rem.r_rem_rem.proof : bv_rem.r_rem_rem.Stmt := by
  sorry

theorem bv_rem.r_default.proof : bv_rem.r_default.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_rem.r_default] at h; simp at h; subst h
  exact Refines.refl

theorem bv_mul.r_lits.proof : bv_mul.r_lits.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_mul.r_lits] at h; split at h <;> simp at h; subst h
  refine Refines.arith_intro (.mul c) (fun n wa wb hT => ?_) (fun n wa wb hT ρ x y v hx hy e => ?_)
  · rw [size_ty_lit wa]; exact BV_mk_masked wa.2.2
  · rw [size_ty_lit wa, eval_mk_masked wa.2.2]
    rw [lit_eval_eq wa hx, lit_eval_eq wb hy] at e
    simp [evBinop, checkedOp, bvBin] at e
    rw [← e.2, BitVec.ofInt_mul]

theorem bv_mul.r_one_r.proof : bv_mul.r_one_r.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_mul.r_one_r] at h; split at h <;> simp at h; obtain ⟨rfl, rfl⟩ := h
  refine Refines.arith_intro (.mul c) (fun n wa wb hT => wa) (fun n wa wb hT ρ x y v hx hy e => ?_)
  rw [lit_eval_eq wb hy] at e
  simp [evBinop, checkedOp, bvBin] at e
  rw [hx, ← e.2]

theorem bv_mul.r_one_l.proof : bv_mul.r_one_l.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_mul.r_one_l] at h; split at h <;> simp at h; obtain ⟨rfl, rfl⟩ := h
  refine Refines.arith_intro (.mul c) (fun n wa wb hT => wb) (fun n wa wb hT ρ x y v hx hy e => ?_)
  rw [lit_eval_eq wa hx] at e
  simp [evBinop, checkedOp, bvBin] at e
  rw [hy, ← e.2]

theorem bv_mul.r_zero_r.proof : bv_mul.r_zero_r.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_mul.r_zero_r] at h; split at h <;> simp at h; obtain ⟨rfl, rfl⟩ := h
  refine Refines.arith_intro (.mul c) (fun n wa wb hT => ?_) (fun n wa wb hT ρ x y v hx hy e => ?_)
  · simp only [wa.2.1, size_of_ty_bitVector]; exact BV_bv_zero wa.2.2
  · simp only [wa.2.1, size_of_ty_bitVector]; rw [eval_bv_zero wa.2.2]
    rw [lit_eval_eq wb hy] at e
    simp [evBinop, checkedOp, bvBin] at e
    rw [← e.2]; rfl

theorem bv_mul.r_zero_l.proof : bv_mul.r_zero_l.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_mul.r_zero_l] at h; split at h <;> simp at h; obtain ⟨rfl, rfl⟩ := h
  refine Refines.arith_intro (.mul c) (fun n wa wb hT => ?_) (fun n wa wb hT ρ x y v hx hy e => ?_)
  · rw [size_ty_lit wa]; exact BV_bv_zero wa.2.2
  · rw [size_ty_lit wa, eval_bv_zero wa.2.2]
    rw [lit_eval_eq wa hx] at e
    simp [evBinop, checkedOp, bvBin] at e
    rw [← e.2]; rfl

theorem bv_mul.neg_aux {FS : FloatSem} {O : Ops} (hO : O.Sound FS) {c z Tc x Tn T N}
    (hN : ∀ n, Tc = .bitVector n → Tn = .bitVector n → N = n)
    (hz : ¬bv_to_z true N z = min_for true N) :
    Refines FS (.mk (.binop (.mul c) (.mk (.bitVec z) Tc) (.mk (.unop (.neg true) x) Tn)) T)
      (O.bv_mul (checked_meet c checked_signed) (O.bv_neg false (mk_bv N z)) x) := by
  refine Refines.arith_intro (.mul c) (fun n wa wb hT => ?_) (fun n wa wb hT ρ C Y v hx hy e => ?_)
  all_goals obtain ⟨rfl, hz'⟩ := BV_lit wa
  all_goals obtain ⟨wx, rfl⟩ := BV_neg_inv wb
  all_goals obtain rfl := hN n rfl rfl
  all_goals have hneg := O_neg (hO.bv_neg false (mk_bv N z)) (BV_mk_bv wa.2.2)
  all_goals have hmul := O_arith (.mul _) (hO.bv_mul (checked_meet c checked_signed) _ x) hneg.1 wx
  · exact hmul.1
  · rw [lit_eval_eq wa hx] at e
    rw [eval_neg wx rfl] at hy
    obtain ⟨X, hX, hy⟩ := evUnop_inv wx hy
    simp [evUnop] at hy; obtain ⟨hXm, rfl⟩ := hy
    have hN' := hneg.2 ρ (BitVec.ofInt _ z) _ (by rw [eval_mk_bv_lit wa, eval_lit wa])
      (by simp [evUnop]; rfl)
    refine O_eval (.mul _) (hO.bv_mul _ _ _) hneg.1 wx hN' hX ?_
    rw [bv_to_z_lit wa.2.2 hz'.1 hz'.2, min_for_eq wa.2.2] at hz
    have hC := ne_intMin_of_toInt (w := N.toNat) (C := BitVec.ofInt _ z) (by have := wa.2.2; omega)
      (by simpa using hz)
    simp [evBinop, checkedOp, bvBin, checked_meet, checked_signed] at e ⊢
    obtain ⟨⟨e1, -⟩, rfl⟩ := e
    exact ⟨fun hs => smul_neg_swap hC hXm (e1 hs), by simp⟩

theorem bv_mul.r_neg.proof : bv_mul.r_neg.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_mul.r_neg] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> obtain ⟨hz, rfl⟩ := h
  · exact bv_mul.neg_aux hO (fun n h1 h2 => by simp [h1]) (of_decide_eq_false hz)
  · rename_i x Tn z Tc
    refine Refines.trans (Refines.comm' (.mul _) (fun w => ?_)) (bv_mul.neg_aux hO (T := Tn)
      (fun n h1 h2 => by simp [h2]) (of_decide_eq_false hz))
    obtain ⟨n, w1, w2, -⟩ := (WT_arith (.mul c)).1 w
    have := w1.2.1; simp at this; simp [this]

-- UNSOUND: the folded constant `n * m` may overflow as a signed product even when `(x * n) * m`
-- does not. Take 8 bits, `checked = ckm = {signed := true, unsigned := false}`,
-- v1 = Mul (ckm, x, 0x40), v2 = 2, with x = 0xff (-1) (take `O` returning the raw spec terms).
-- Then x *s 64 = -64 and -64 *s 2 = -128 have no signed overflow, so the spec is `some 0x80`. The
-- result is x *s 0x80 = (-1) *s (-128), whose signed overflow makes it poison.
theorem bv_mul.r_mul_const.proof : bv_mul.r_mul_const.Stmt := by
  sorry

theorem bv_mul.r_ite.proof : bv_mul.r_ite.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_mul.r_ite] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> subst h
  · simp only [bv_mul.spec, ty_eq, Term.ty_mk]
    refine Refines.ite_push_l hO (.mul c) (fun n wl wV hT => ?_) (fun n wr wV hT => ?_)
    all_goals subst hT; rw [size_of_ty_bitVector]
    · have := O_arith_lit (.mul _) (hO.bv_mul unchecked _ _) wl wV
      exact ⟨this.1, fun ρ v e => this.2 ρ v (evBinop_mul_unchecked e)⟩
    · have := O_arith_lit (.mul _) (hO.bv_mul unchecked _ _) wr wV
      exact ⟨this.1, fun ρ v e => this.2 ρ v (evBinop_mul_unchecked e)⟩
  · simp only [bv_mul.spec, ty_eq, Term.ty_mk]
    refine Refines.ite_push_r hO (.mul c) (fun n wl wV hT => ?_) (fun n wr wV hT => ?_)
    all_goals obtain ⟨rfl, -⟩ := BV_lit wV; rw [size_of_ty_bitVector]
    · have := O_arith_lit' (.mul _) (.mul _) (hO.bv_mul unchecked _ _) wl wV
      exact ⟨this.1, fun ρ v e => this.2 ρ v (evBinop_mul_unchecked e)⟩
    · have := O_arith_lit' (.mul _) (.mul _) (hO.bv_mul unchecked _ _) wr wV
      exact ⟨this.1, fun ρ v e => this.2 ρ v (evBinop_mul_unchecked e)⟩

theorem bv_mul.r_default.proof : bv_mul.r_default.Stmt := by
  intro FS O hO c v1 v2 res h
  simp only [bv_mul.r_default] at h; simp at h; subst h
  exact Refines.commut_binop (.mul c)

-- UNSOUND: the literals are divided with `tdiv`, for which `tdiv l 0 = 0`, but division by zero
-- follows SMT-LIB (`x /u 0` is all ones, `x /s 0` is -1 or 1). Take 8 bits, `signed = false`,
-- v1 = 5 and v2 = 0. The spec `5 /u 0` is `some 0xff`, and the result is the literal 0.
theorem bv_div.r_lits.proof : bv_div.r_lits.Stmt := by
  sorry

theorem bv_div.r_one.proof : bv_div.r_one.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_div.r_one] at h; split at h <;> simp at h; obtain ⟨rfl, rfl⟩ := h
  refine Refines.arith_intro (.div s) (fun n wa wb hT => wa) (fun n wa wb hT ρ x y v hx hy e => ?_)
  rw [lit_eval_eq wb hy] at e
  simp [evBinop, bvBin] at e
  rw [hx, ← e]
  have hn : 0 < n.toNat := by have := wa.2.2; omega
  cases s
  · simp [BitVec.smtUDiv_eq, one_ne_zero' hn, BitVec.udiv_one]
  · simp [smtSDiv_of_ne_zero (one_ne_zero' hn)]

theorem bv_div.r_mul_lits.proof : bv_div.r_mul_lits.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_div.r_mul_lits] at h; split at h <;> simp at h; subst h
  rename_i c l Tl r Tr T z T2
  have hm := hO.bv_mul c (.mk (.bitVec l) Tl) (.mk (.bitVec r) Tr)
  refine Refines.trans (Refines.binop (Refines.trans (Refines.retype (fun w => ?_)) hm)
    Refines.refl (fun w => ?_)) (hO.bv_div _ _ _)
  · obtain ⟨n, wa, wb, rfl⟩ := (WT_arith (.mul c)).1 w
    obtain ⟨rfl, -⟩ := BV_lit wa; rfl
  · obtain ⟨n, wa, wb, rfl⟩ := (WT_arith (.div s)).1 w
    have := BV_arith_inv (.mul c) wa
    have := (BV_arith (.mul c) hm this.1 this.2.1).2.1
    simp [this]

-- UNSOUND: `divisible 0 0` holds, and then the rule replaces a division by zero with a
-- multiplication by `tdiv 0 0 = 0`. Take 8 bits, `signed = false`, v1 = Mul (checked_unsigned,
-- 0, x), v2 = 0, with x = 1 (take `O` returning the raw spec terms). The spec is
-- `(0 *u 1) /u 0 = some 0xff`, and the result is `x *u 0 = some 0`.
theorem bv_div.r_mul_div.proof : bv_div.r_mul_div.Stmt := by
  sorry

theorem bv_div.div_mul_aux {FS : FloatSem} {O : Ops} (hO : O.Sound FS) {s' n Tn x T1 d T2 N}
    (hdiv : n ∣ d) (hN : ∀ m, T1 = .bitVector m → N = m) :
    Refines FS (.mk (.binop (.div false) (.mk (.binop (.mul ⟨s', true⟩) (.mk (.bitVec n) Tn) x) T1)
        (.mk (.bitVec d) T2)) T1)
      (O.bv_div false x (mk_bv N (tdiv d n))) := by
  refine Refines.arith_intro (.div false) (fun m wa wb hT => ?_)
    (fun m wa wb hT ρ P Dv v hx hy e => ?_)
  all_goals obtain ⟨wn, wx, rfl⟩ := BV_arith_inv (.mul _) wa
  all_goals obtain rfl := hN m rfl
  all_goals obtain ⟨rfl, hzn⟩ := BV_lit wn
  all_goals obtain ⟨rfl, hzd⟩ := BV_lit wb
  all_goals have hk := BV_mk_bv (n := N) (z := tdiv d n) wa.2.2
  all_goals have hres := O_arith (.div _) (hO.bv_div false x _) wx hk
  · exact hres.1
  · rw [eval_arith (.mul _) wn wx rfl] at hx
    obtain ⟨Nv, X, hNv, hX, hx⟩ := evBinop_inv (.inl (.mul _)) wn wx hx
    obtain rfl := lit_eval_eq wn hNv
    obtain rfl := lit_eval_eq wb hy
    simp [evBinop, checkedOp, bvBin] at hx e; obtain ⟨⟨-, hu⟩, rfl⟩ := hx; subst e
    refine O_eval (.div _) (hO.bv_div _ _ _) wx hk hX (by rw [mk_bv, eval_mk_masked wa.2.2]) ?_
    simp [evBinop, bvBin]
    obtain ⟨t0, t1, t2, t3⟩ := tdiv_facts hzn.1 hzd.1 hdiv
    rw [umul_ok, lit_toNat hzn.1 hzn.2] at hu
    exact (udiv_mul_cancel (lit_toNat hzn.1 hzn.2) (lit_toNat hzd.1 hzd.2)
      (lit_toNat t0 (by omega)) t2 (fun h => by rw [t3 (by omega)]; rfl) hu).symm

theorem bv_div.r_div_mul.proof : bv_div.r_div_mul.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_div.r_div_mul] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp [divisible] at h <;>
    obtain ⟨⟨rfl, hd⟩, rfl⟩ := h
  · exact bv_div.div_mul_aux hO hd (fun m h => by simp [h])
  · refine Refines.trans (Refines.binop (Refines.comm (.mul _)) Refines.refl (fun _ => rfl))
      (bv_div.div_mul_aux hO hd (fun m h => by simp [h]))

-- UNSOUND: when the inner divisor is zero, `x / 0` is all ones (SMT-LIB), and dividing it again
-- differs from dividing `x` by `0 * d = 0`. Take 8 bits, `signed = false`, v1 = Div (false, x, 0),
-- v2 = 2, with x = 5 (take `O` returning the raw spec terms); `overflows_mul false 8 0 2` is false.
-- The spec is `(5 /u 0) /u 2 = 0xff /u 2 = some 0x7f`, and the result is `x /u 0 = some 0xff`.
theorem bv_div.r_div_div.proof : bv_div.r_div_div.Stmt := by
  sorry

theorem bv_div.r_zext.proof : bv_div.r_zext.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_div.r_zext] at h; split at h <;> simp at h; obtain ⟨⟨rfl, hm⟩, rfl⟩ := h
  rename_i k x T z T2
  refine Refines.arith_intro (.div false) (fun n wa wb hT => ?_)
    (fun n wa wb hT ρ X' Z v hx hy e => ?_)
  all_goals obtain ⟨m, wx, hk, rfl, rfl⟩ := BV_extend_inv wa
  all_goals obtain ⟨rfl, hz⟩ := BV_lit wb
  all_goals rw [show size_of_ty x.ty = m by simp [wx.2.1]]
  all_goals have hd := O_arith (.div _) (hO.bv_div false x (mk_bv m z)) wx (BV_mk_bv wx.2.2)
  all_goals have he := hO.bv_extend false k (O.bv_div false x (mk_bv m z))
  · exact BV_extend he hd.1 hk
  · obtain ⟨X, hX, hv⟩ := eval_extend_inv wa wx hx
    obtain ⟨hw, hv⟩ := Val.bv_toNat_eq hv
    obtain rfl := lit_eval_eq wb hy
    simp only [msb_of_lit, wx.2.1, size_of_ty_bitVector, decide_eq_true_eq] at hm
    have hD := hd.2 ρ (.bv m.toNat (X.smtUDiv (BitVec.ofInt _ z)))
      (by rw [hX, mk_bv, eval_mk_masked wx.2.2]; simp [evBinop, bvBin])
    have hR := he.sem ρ _ (eval_extend hd.1 hk hD)
    rw [hR]
    simp [evBinop, bvBin] at e; subst e
    congr 1; apply Val.bv_congr (by omega)
    rw [BitVec.toNat_setWidth, BitVec.smtUDiv_eq, BitVec.smtUDiv_eq]
    have hX2 := X.isLt
    have hp : 2 ^ m.toNat ≤ 2 ^ (m.toNat + k.toNat) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)] at hv
    by_cases hz0 : 0 < z
    · simp only [hz0, ↓reduceIte] at hm
      have hl := Nat.lt_log2_self (n := z.toNat)
      have hm' : Nat.log2 z.toNat + 1 ≤ m.toNat := by simp only [log2] at hm; omega
      have h3 : z.toNat < 2 ^ m.toNat := Nat.lt_of_lt_of_le hl (Nat.pow_le_pow_right (by omega) hm')
      have hzm : z < 2 ^ m.toNat := by have := natCast_two_pow m.toNat; omega
      have h1 : BitVec.ofInt (m + k).toNat z ≠ 0#_ := by
        intro h; have := congrArg BitVec.toNat h
        rw [lit_toNat hz.1 hz.2] at this; simp at this; omega
      have h2 : BitVec.ofInt m.toNat z ≠ 0#_ := by
        intro h; have := congrArg BitVec.toNat h
        rw [lit_toNat hz.1 hzm] at this; simp at this; omega
      simp only [h1, h2, ↓reduceIte, BitVec.toNat_udiv, lit_toNat hz.1 hz.2, lit_toNat hz.1 hzm, hv]
      rw [Nat.mod_eq_of_lt]
      have := Nat.div_le_self X.toNat z.toNat
      omega
    · simp only [hz0, ↓reduceIte] at hm
      obtain rfl : z = 0 := by omega
      obtain rfl : k = 0 := by omega
      simp

theorem bv_div.r_default.proof : bv_div.r_default.Stmt := by
  intro FS O hO s v1 v2 res h
  simp only [bv_div.r_default] at h; simp at h; subst h
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

-- UNSOUND: for one-bit vectors, `1 + 1` overflows (in both signednesses). Take `signed = false`,
-- v1 = BvOfBool (1, b1), v2 = BvOfBool (1, b2), with b1 = b2 = true. The spec is
-- `uaddOverflow 1 1 = some true`, and the result is `v_false`. In `bv_add_overflows.step`,
-- `r_size1` fires first on one-bit vectors.
theorem bv_add_overflows.r_of_bools.proof : bv_add_overflows.r_of_bools.Stmt := by
  sorry

-- UNSOUND: for one-bit vectors, `BvOfBool (1, true)` is -1 as a signed number, not 1. Take
-- `signed = true`, v1 = BvOfBool (1, b), v2 = the literal 0 (of 1 bit), with b = true (take `O`
-- returning the raw spec terms). The spec is `saddOverflow 1 0 = some false` (-1 + 0 = -1), but
-- `max_for true 1 = 0`, so the result is `b && (0 = 0) = some true`. In `bv_add_overflows.step`,
-- `r_size1` fires first on one-bit vectors.
theorem bv_add_overflows.r_of_bool.proof : bv_add_overflows.r_of_bool.Stmt := by
  sorry

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
  sorry

-- UNSOUND: the literal 1 is only neutral as an unsigned number; as a signed one-bit vector it is -1.
-- Take `signed = true`, v1 = the literal 1 (of 1 bit), v2 = x with x = 1. The spec is
-- `smulOverflow 1 1 = some true` ((-1) * (-1) = 1 > 0), and the result is `v_false`. In
-- `bv_mul_overflows.step`, `r_size1` fires first on signed one-bit vectors.
theorem bv_mul_overflows.r_const.proof : bv_mul_overflows.r_const.Stmt := by
  sorry

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
