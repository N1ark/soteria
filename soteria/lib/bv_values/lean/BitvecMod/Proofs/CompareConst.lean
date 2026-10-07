import BitvecMod.Proofs.CompareMul

/-!
# The arms of the comparisons of a sum or a difference of a term and a constant with a constant

`lt`/`leq` `.r_add_const`, `.r_const_add`, `.r_sub_const1`, `.r_sub_const2`, `.r_const_sub1` and
`.r_const_sub2` (`x + k ⋚ c`, `c ⋚ k - x`, …), checked in the signedness of the comparison: the
comparison is one of `x` with the constant `c ∓ k` when that does not overflow, and a constant
when it does (unsigned).

The proofs read the value of the left side once (`cc_cmp`, `cc_add`/`cc_sub`, `cc_lit`: the value
of `x`, the non-overflow of the operation, the comparison of bit-vectors), compute that of the
right side, and close the comparison of integers by `omega`.
-/

noncomputable section

namespace BitvecMod

open Classical Kanon

section
variable {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [Lang S] [KanonBool.Typed S]
  [CoreMod.Typed S] [Typed S]

omit [KanonBool.Typed S] [CoreMod.Typed S] in
/-- The value of a comparison: those of its sides, bit-vectors of the width of their sort. -/
theorem cc_cmp {s le : Bool} {A B : S.Term} {ρ : S.Env} {v : S.Val}
    (w : S.WT (mk (if le then .Leq s A B else .Lt s A B) (KanonBool.sort .TBool)))
    (e : S.ev ρ (mk (if le then .Leq s A B else .Lt s A B) (KanonBool.sort .TBool)) = some v) :
    ∃ n : Nat, 0 < n ∧ S.ty A = sort (.TBitVector n) ∧ S.ty B = S.ty A ∧ S.WT A ∧ S.WT B ∧
      ∃ a b : BitVec n, S.ev ρ A = some (bv n a) ∧ S.ev ρ B = some (bv n b) ∧
        v = KanonBool.Values.vbool.inj (if le then (if s then a.sle b else a.ule b)
          else (if s then a.slt b else a.ult b)) := by
  cases le <;>
  · simp only [Bool.false_eq_true, ↓reduceIte, WT_mk, Node.wt, Node.All] at w e ⊢
    obtain ⟨⟨⟨N, hN, hA⟩, hB, -⟩, wA, wB⟩ := w
    obtain ⟨n, rfl⟩ : ∃ n : Nat, N = n := ⟨N.toNat, by omega⟩
    have hw : Values.width (D := S.toDom) (S.ty A) = n := by
      rw [hA]; simpa using width_sort (S := S) ρ (.inl rfl) hN
    rcases ev_cases (ρ := ρ) wA hA with hv | ⟨_, hv, -, a, rfl⟩
    · simp [ev_mk, Node.eval, Node.map, hv] at e
    rcases ev_cases (ρ := ρ) wB (hB.trans hA) with hv' | ⟨_, hv', -, b, rfl⟩
    · simp [ev_mk, Node.eval, Node.map, hv'] at e
    replace hv : S.ev ρ A = some (bv n a) := hv
    replace hv' : S.ev ρ B = some (bv n b) := hv'
    simp only [ev_mk, Node.eval, Node.map, hv, hv', withW_bv, asBV_bv, binB_some, ofB_some,
      Option.some.injEq] at e
    exact ⟨n, by omega, hA, hB, wA, wB, a, b, hv, hv', e.symm⟩

set_option hygiene false in
/-- The proof of `cc_add` and `cc_sub`. -/
macro "cc_op_tac" : tactic => `(tactic| (
  subst ht
  simp only [WT_mk, Node.wt, Node.All] at w
  obtain ⟨⟨-, hB, hT⟩, wA, wB⟩ := w
  have hA' : S.ty A = sort (.TBitVector n) := hT.symm
  have hw : Values.width (D := S.toDom) (sort (.TBitVector n)) = n := by
    simpa using width_sort (S := S) ρ (.inl rfl) (show (0 : Int) < n by omega)
  rcases ev_cases (ρ := ρ) wA hA' with hv | ⟨_, hv, -, a, rfl⟩
  · simp [ev_mk, Node.eval, Node.map, hv] at e
  rcases ev_cases (ρ := ρ) wB (hB.trans hA') with hv' | ⟨_, hv', -, b, rfl⟩
  · simp [ev_mk, Node.eval, Node.map, hv'] at e
  replace hv : S.ev ρ A = some (bv n a) := hv
  replace hv' : S.ev ρ B = some (bv n b) := hv'
  simp only [ev_mk, Node.eval, Node.map, hv, hv'] at e
  rw [hw] at e
  simp only [asBV_bv, ckOp_some] at e
  refine ⟨hA', hB, wA, wB, a, b, hv, hv', ?_⟩
  split at e
  · simp at e
  · rename_i h
    simp only [Bool.or_eq_true, Bool.and_eq_true, not_or, not_and, Bool.not_eq_true] at h
    simp only [ofBV_some, Option.some.injEq, Kanon.Embed.inj_eq_iff, Sigma.mk.injEq, heq_eq_eq,
      true_and] at e
    exact ⟨h.1, h.2, e.symm⟩))

omit [KanonBool.Typed S] [CoreMod.Typed S] in
/-- The value of a checked sum of a sort of bit-vectors: those of its terms, without overflow. -/
theorem cc_add {ck : CoreMod.Checked} {A B : S.Term} {t : S.Ty} {ρ : S.Env} {n : Nat}
    {r : BitVec n} (w : S.WT (mk (.Add ck A B) t)) (ht : t = sort (.TBitVector n)) (hn : 0 < n)
    (e : S.ev ρ (mk (.Add ck A B) t) = some (bv n r)) :
    S.ty A = sort (.TBitVector n) ∧ S.ty B = S.ty A ∧ S.WT A ∧ S.WT B ∧
      ∃ a b : BitVec n, S.ev ρ A = some (bv n a) ∧ S.ev ρ B = some (bv n b) ∧
        (ck.signed = true → a.saddOverflow b = false) ∧
        (ck.unsigned = true → a.uaddOverflow b = false) ∧ r = a + b := by
  cc_op_tac

omit [KanonBool.Typed S] [CoreMod.Typed S] in
/-- `cc_add`, for a difference. -/
theorem cc_sub {ck : CoreMod.Checked} {A B : S.Term} {t : S.Ty} {ρ : S.Env} {n : Nat}
    {r : BitVec n} (w : S.WT (mk (.Sub ck A B) t)) (ht : t = sort (.TBitVector n)) (hn : 0 < n)
    (e : S.ev ρ (mk (.Sub ck A B) t) = some (bv n r)) :
    S.ty A = sort (.TBitVector n) ∧ S.ty B = S.ty A ∧ S.WT A ∧ S.WT B ∧
      ∃ a b : BitVec n, S.ev ρ A = some (bv n a) ∧ S.ev ρ B = some (bv n b) ∧
        (ck.signed = true → a.ssubOverflow b = false) ∧
        (ck.unsigned = true → a.usubOverflow b = false) ∧ r = a - b := by
  cc_op_tac

omit [KanonBool.Typed S] [CoreMod.Typed S] in
/-- A literal of a sort of bit-vectors: in range, and its value. -/
theorem cc_lit {c : Int} {t : S.Ty} {ρ : S.Env} {n : Nat} (w : S.WT (mk (.BitVec c) t))
    (ht : t = sort (.TBitVector n)) (hn : 0 < n) :
    0 ≤ c ∧ c < 2 ^ n ∧ S.ev ρ (mk (.BitVec c) t) = some (bv n (BitVec.ofInt n c)) := by
  subst ht
  simp only [WT_mk, Node.wt, bv_wf] at w
  obtain ⟨⟨-, r⟩, -⟩ := w
  obtain ⟨c0, c1⟩ := r n (.inl rfl)
  simp only [Int.toNat_natCast] at c1
  refine ⟨c0, c1, ?_⟩
  have hw : Values.width (D := S.toDom) (sort (.TBitVector n)) = n := by
    simpa using width_sort (S := S) ρ (.inl rfl) (show (0 : Int) < n by omega)
  simp only [ev_mk, Node.eval, Node.map]
  rw [hw]
  rfl

omit [KanonBool.Typed S] [CoreMod.Typed S] [Typed S] in
/-- The values of bit-vectors are those bit-vectors. -/
theorem cc_bv_eq {n : Nat} {a b : BitVec n} (h : some (bv (D := S.toDom) n a) = some (bv n b)) :
    a = b := by
  simpa only [Option.some.injEq, Kanon.Embed.inj_eq_iff, Sigma.mk.injEq, heq_eq_eq, true_and]
    using h

omit [KanonBool.Typed S] [CoreMod.Typed S] [Typed S] in
/-- The typing of a comparison. -/
theorem cc_cmp_wt {s le : Bool} {A B : S.Term}
    (w : S.WT (mk (if le then .Leq s A B else .Lt s A B) (KanonBool.sort .TBool))) :
    ∃ N : Int, 0 < N ∧ S.ty A = sort (.TBitVector N) ∧ S.ty B = S.ty A ∧ S.WT A ∧ S.WT B := by
  cases le <;>
  · simp only [Bool.false_eq_true, ↓reduceIte, WT_mk, Node.wt, Node.All] at w
    obtain ⟨⟨⟨N, hN, hA⟩, hB, -⟩, wA, wB⟩ := w
    exact ⟨N, hN, hA, hB, wA, wB⟩

omit [KanonBool.Typed S] [CoreMod.Typed S] [Typed S] in
/-- The typing of a sum or a difference. -/
theorem cc_op_wt {sub : Bool} {ck : CoreMod.Checked} {A B : S.Term} {t : S.Ty}
    (w : S.WT (mk (if sub then .Sub ck A B else .Add ck A B) t)) :
    t = S.ty A ∧ S.ty B = S.ty A ∧ S.WT A ∧ S.WT B := by
  cases sub <;>
  · simp only [Bool.false_eq_true, ↓reduceIte, WT_mk, Node.wt, Node.All] at w
    obtain ⟨⟨-, hB, ht⟩, wA, wB⟩ := w
    exact ⟨ht, hB, wA, wB⟩

end

section
variable {n : Nat} {a b : BitVec n}

/-! Sums and differences without overflow, as conditional rewritings (`simp (disch := omega)`). -/

theorem cc_toNat_add (h : a.toNat + b.toNat < 2 ^ n) : (a + b).toNat = a.toNat + b.toNat :=
  toNat_add_ok (uadd_ok.2 h)
theorem cc_toNat_sub (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat :=
  toNat_sub_ok (usub_ok.2 h)
theorem cc_toInt_add (h0 : -2 ^ (n - 1) ≤ a.toInt + b.toInt)
    (h1 : a.toInt + b.toInt < 2 ^ (n - 1)) :
    (a + b).toInt = a.toInt + b.toInt :=
  toInt_add_ok (sadd_ok.2 ⟨h0, h1⟩)
theorem cc_toInt_sub (h0 : -2 ^ (n - 1) ≤ a.toInt - b.toInt)
    (h1 : a.toInt - b.toInt < 2 ^ (n - 1)) :
    (a - b).toInt = a.toInt - b.toInt :=
  toInt_sub_ok (ssub_ok.2 ⟨h0, h1⟩)
end

set_option hygiene false in
/-- A side of a comparison, or a term of an operation, that is a literal: its value and range. -/
macro "cc_lit_side " W:ident H:ident l0:ident l1:ident T:term : tactic => `(tactic| (
  obtain ⟨$l0, $l1, hl⟩ := cc_lit $W $T hn
  rw [hl] at $H:ident
  obtain rfl := cc_bv_eq $H))

set_option hygiene false in
/-- Reads the value of the left side of an arm: the value `xv` of its term `x`, the non-overflow
of its operation, and the comparison. -/
macro "cc_lhs" : tactic => `(tactic| (
  obtain ⟨n, hn, hA, hB, wA, wB, a, b, ha, hb, rfl⟩ :=
    by first | exact cc_cmp (le := false) w e | exact cc_cmp (le := true) w e
  simp only [ty_mk] at hA hB
  first
    | cc_lit_side wB hb c0 c1 (hB.trans hA)
    | cc_lit_side wA ha c0 c1 hA
  first
    | obtain ⟨hx1, hx2, wX, wY, xa, xb, hxa, hxb, hs, hu, rfl⟩ := cc_sub wA hA hn ha
    | obtain ⟨hx1, hx2, wX, wY, xa, xb, hxa, hxb, hs, hu, rfl⟩ := cc_add wA hA hn ha
    | obtain ⟨hx1, hx2, wX, wY, xa, xb, hxa, hxb, hs, hu, rfl⟩ := cc_sub wB (hB.trans hA) hn hb
    | obtain ⟨hx1, hx2, wX, wY, xa, xb, hxa, hxb, hs, hu, rfl⟩ := cc_add wB (hB.trans hA) hn hb
  first
    | (simp only [ty_mk] at hx2; cc_lit_side wY hxb k0 k1 (hx2.trans hx1))
    | (simp only [ty_mk] at hx1; cc_lit_side wX hxa k0 k1 hx1)
  have hw : Values.width (D := S.toDom) (sort (.TBitVector n)) = n := by
    simpa using width_sort (S := S) ρ (.inl rfl) (show (0 : Int) < n by omega)
  clear e
  simp only [KanonBool.ev_v_true, KanonBool.ev_v_false, ev_mk, Node.eval, Node.map, mk_bv,
    mk_masked, ty_mk, hA, hx1, size_of_ty_TBitVector, lit_add, lit_sub, hxa, hxb,
    Int.toNat_natCast, Bool.false_eq_true, ↓reduceIte]
  (try rw [hw])
  simp only [withW_bv, asBV_bv, ofBV_some, binB_some, ofB_some, Option.some.injEq,
    Kanon.Embed.inj_eq_iff]
  (try rw [hw])
  (try simp only [ofInt_emod_two_pow, LitOps.ofInt_lit_add, LitOps.ofInt_lit_sub])))

set_option hygiene false in
/-- The typing of the right side of an arm: a constant, or the comparison of the term of the
operation of the left side with a literal. -/
macro "cc_wt" : tactic => `(tactic| (
  intro w
  first
    | exact ⟨KanonBool.WT_v_true, by rw [KanonBool.ty_v_true, ty_mk]⟩
    | exact ⟨KanonBool.WT_v_false, by rw [KanonBool.ty_v_false, ty_mk]⟩
    | (obtain ⟨N, hN, hA, hB, wA, wB⟩ :=
         by first | exact cc_cmp_wt (le := false) w | exact cc_cmp_wt (le := true) w
       simp only [ty_mk] at hA hB
       first
         | obtain ⟨ht, hY, wX, wY⟩ := cc_op_wt (sub := true) wA
         | obtain ⟨ht, hY, wX, wY⟩ := cc_op_wt (sub := false) wA
         | obtain ⟨ht, hY, wX, wY⟩ := cc_op_wt (sub := true) wB
         | obtain ⟨ht, hY, wX, wY⟩ := cc_op_wt (sub := false) wB
       simp only [ty_mk] at hY ht
       have hx : S.ty x = sort (.TBitVector N) := by
         first
           | exact ht.symm.trans hA
           | exact hY.trans (ht.symm.trans hA)
           | exact ht.symm.trans (hB.trans hA)
           | exact hY.trans (ht.symm.trans (hB.trans hA))
       simp only [ty_mk, mk_bv, mk_masked, hA, hx, size_of_ty_TBitVector, WT_mk, Node.wt,
         Node.All, bv_wf, wX, sort_inj_iff, Srt.TBitVector.injEq, reduceCtorEq, or_false,
         forall_eq', and_true, true_and]
       have hp : (0 : Int) < 2 ^ N.toNat := Int.pow_pos (by decide)
       and_intros
       all_goals first
         | assumption
         | exact ⟨N, hN, rfl⟩
         | exact Int.emod_nonneg _ (by omega)
         | exact Int.emod_lt_of_pos _ hp)))

set_option hygiene false in
/-- Closes the comparison of the values of the two sides of an arm, on integers. -/
macro "cc_close" : tactic => `(tactic| (
  (try replace hs := hs ‹_›)
  (try replace hu := hu ‹_›)
  (try simp only [hA, ty_mk, size_of_ty_TBitVector, z_lsl_one, Int.toNat_natCast,
    natCast_sub_one_toNat, signed_extract_zero hn, Bool.or_eq_true, decide_eq_true_eq,
    Bool.not_eq_true,
    Bool.or_eq_false_iff, decide_eq_false_iff_not, not_or, gt_iff_lt, Int.not_lt] at cmp_hc)
  (try simp only [BitVec.ult, BitVec.slt, BitVec.ule, BitVec.sle, decide_eq_decide, Bool.true_eq,
    Bool.false_eq, decide_eq_true_eq, decide_eq_false_iff_not])
  (try simp only [sadd_ok, ssub_ok, uadd_ok, usub_ok] at hs)
  (try simp only [sadd_ok, ssub_ok, uadd_ok, usub_ok] at hu)
  have hK := toNat_ofInt_of_lt k0 k1
  have hC := toNat_ofInt_of_lt c0 c1
  have hP : ((2 ^ n : Nat) : Int) = 2 ^ n := by push_cast; rfl
  (try simp (disch := omega) only [cc_toNat_add, cc_toNat_sub, cc_toInt_add, cc_toInt_sub])
  omega))

set_option hygiene false in
/-- An arm comparing a sum or a difference of a term and a constant with a constant. -/
macro "cc_arm" : tactic => `(tactic| (
  mul_lift
  all_goals first
    | bv_vacuous
    | (simp only [Bool.false_eq_true, Bool.true_eq_false] at *; done)
    | exact Kanon.Sem.Refines.refl
    | (refine Kanon.Sem.Refines.intro ?_ (fun ρ v w _ e => ?_)
       · cc_wt
       · cc_lhs
         cc_close)))

end BitvecMod
