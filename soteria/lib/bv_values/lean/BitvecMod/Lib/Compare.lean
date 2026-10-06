import BitvecMod.Lib.Resize

/-!
# Comparisons

The lemmas and tactics of the arms of `Bitvec.lt`, `leq`, `lt_zero`, over the
interface: the counterparts of the language's `Kanon/Lib/Msb.lean` and
`Compare.lean`. They build on the steps of `bv_rs` (`Lib/Resize.lean`): the
lifting, the natural widths and the sorts of the operands.

- `bv_cmp_sem_core` reduces the value half of a boolean refinement
  (`Refines.denB`) to the values of the atoms, the literals kept as values
  (`BitVec.ofInt n z`);
- `bv_msb` is the tactic of `Bitvec.lt_zero`: `v <s 0` is the sign bit of `v`.
-/

namespace BitvecMod

open Classical Kanon

set_option linter.unusedSectionVars false

namespace Lib

variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
  {LBool : KanonBool.Syntax B} {LCore : CoreMod.Syntax B} {L : Syntax B LBool LCore}
  [KanonBool.Sem LBool] [CoreMod.Sem LCore] [Sem L]

/-- `ite g p p` is `p`. -/
theorem cmp_refines_ite_same {g p : S.Term} {t : S.Ty} :
    S.Refines (B.node (LBool.IteK g p p) t) p := by
  refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · rw [LBool.WT_Ite] at w
    exact ⟨w.2.2.1, by rw [B.ty_node, w.1.2.2]⟩
  · rw [KanonBool.Sem.ev_Ite] at e
    unfold KanonBool.pite at e
    split at e
    · exact e
    · split at e
      · exact e
      · cases e

end Lib

open Lib

set_option hygiene false in
/-- The value half of `Refines.denB`, reduced to the values of the atoms, the
literals kept as values (`BitVec.ofInt n z`); its hypothesis is `e`. -/
macro "bv_cmp_sem_core" : tactic => `(tactic| (
  intro w ρ x e
  bv_rs_facts
  (try bv_rs_nat)
  bv_rs_nat_eqs
  (try simp only [bv_den, bv_lits] at e ⊢)
  (try bv_rs_rw_tys)
  (try simp only [bv_lits, BitvecMod.Lib.TBitVector_inj_iff, Int.ofNat_inj] at *)
  (try subst_vars)
  (try simp (disch := omega) only [ite_eq_left, Int.toNat_natCast,
    BitvecMod.Lib.rs_toNat_natCast_add] at e ⊢)
  run_tac Kanon.Proof.caseAllAtoms (some #[``BitvecMod.Lib.den_cases, ``BitvecMod.Lib.denB_cases])
  all_goals (try bv_bool_vars)
  all_goals (try simp only [Option.map_some, Option.map_none, Option.some.injEq,
    reduceCtorEq, BitvecMod.ckOp_some, BitvecMod.binOp_some, BitvecMod.negOp_some,
    BitvecMod.binB_some, BitvecMod.binB_none_l, BitvecMod.binB_none_r] at e ⊢)
  all_goals (try subst e)
  all_goals (try (split at e <;> simp only [Option.map_some, Option.map_none, Option.some.injEq,
    reduceCtorEq] at e <;> subst e))))

/-- The boolean literals of the bool module as nodes. -/
macro "bv_cmp_bools" : tactic => `(tactic| (
  (try simp only [KanonBool.Sem.v_false_eq, KanonBool.Sem.v_true_eq,
    KanonBool.Syntax.bool_of_bool_eq])
  (repeat' split)))

set_option hygiene false in
/-- The value half of a sign test (`v <s 0`), on the sign bit of `v`. -/
macro "bv_msb_sem" : tactic => `(tactic| (
  bv_cmp_sem_core
  all_goals simp only [BitvecMod.Lib.rs_ofInt_zero, BitVec.slt_zero_eq_msb] at *
  all_goals (try simp only [← Int.natCast_add, Int.natCast_pos] at *)
  all_goals (try simp_all [BitVec.msb_signExtend, BitVec.msb_not, BitVec.msb_append,
    BitVec.msb_setWidth, BitVec.msb_srem])
  all_goals first
    | done
    | (simp_all [BitVec.msb]; done)
    | (split at e
       all_goals (try simp (disch := omega) only [Nat.sub_eq_zero_of_le] at e)
       all_goals simpa [BitVec.msb] using e)
    | (simp (disch := omega) [BitVec.getLsbD_of_ge] at e; done)
    | (split at e
       · omega
       · exact e)))

/-- The rule tactic of `Bitvec.lt_zero`: `v <s 0` is the sign bit of `v`. -/
macro "bv_msb" : tactic => `(tactic| (
  bv_rs_rule_lift
  bv_rule_apply
  all_goals bv_cmp_bools
  all_goals first
    | (bv_rs_wt; done)
    | bv_msb_sem
    | skip))

attribute [kanon_tactic "bv_msb"] Bitvec.lt_zero.spec

end BitvecMod

namespace BitvecMod
namespace Lib

open Prim

/-! ## The helpers on literals -/

theorem cmp_toNat_lit {n p : Nat} (hp : (p : Int) < 2 ^ n) :
    ((BitVec.ofInt n (p : Int)).toNat : Int) = p := by
  rw [rs_toNat_ofInt_nat hp]

theorem cmp_signed_extract_lit {n p : Nat} (hn : 0 < n) :
    Prim.signed_extract (p : Int) 0 (n : Int) = (BitVec.ofInt n (p : Int)).toInt :=
  rs_sext_of hn _

section
variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
  {LBool : KanonBool.Syntax B} {LCore : CoreMod.Syntax B} {L : Syntax B LBool LCore}
  [KanonBool.Sem LBool] [CoreMod.Sem LCore] [Sem L]

theorem cmp_to_z {n p : Nat} (hn : 0 < n) (hp : (p : Int) < 2 ^ n) (s : Bool) :
    L.bitvec_to_z s (n : Int) (p : Int) = iv s (BitVec.ofInt n (p : Int)) := by
  rw [Syntax.bitvec_to_z_eq, Sem.signed_extract_eq]
  cases s
  · show (p : Int) = ((BitVec.ofInt n (p : Int)).toNat : Int); rw [rs_toNat_ofInt_nat hp]
  · simp [cmp_signed_extract_lit hn]

section
variable {n : Nat} (hn : 0 < n) {l r : Nat} (hl : (l : Int) < 2 ^ n) (hr : (r : Int) < 2 ^ n)
include hn hl hr

theorem cmp_overflows_add (s : Bool) :
    L.bitvec_overflows_add s (n : Int) (l : Int) (r : Int) =
      if s then (BitVec.ofInt n (l : Int)).saddOverflow (BitVec.ofInt n (r : Int))
      else (BitVec.ofInt n (l : Int)).uaddOverflow (BitVec.ofInt n (r : Int)) := by
  rw [Syntax.bitvec_overflows_add_eq, cmp_to_z hn hl, cmp_to_z hn hr]
  cases s
  · simp only [min_for_false, max_for_false, BitVec.uaddOverflow, iv,
      rs_toNat_ofInt_nat hl, rs_toNat_ofInt_nat hr, Bool.false_eq_true, ite_false]
    have e3 : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega
  · have := BitVec.le_toInt (BitVec.ofInt n (l : Int))
    have := BitVec.toInt_lt (x := BitVec.ofInt n (l : Int))
    simp only [min_for_true hn, max_for_true hn, BitVec.saddOverflow, iv]
    rw [Bool.eq_iff_iff]; simp; omega

theorem cmp_overflows_sub (s : Bool) :
    L.bitvec_overflows_sub s (n : Int) (l : Int) (r : Int) =
      if s then (BitVec.ofInt n (l : Int)).ssubOverflow (BitVec.ofInt n (r : Int))
      else (BitVec.ofInt n (l : Int)).usubOverflow (BitVec.ofInt n (r : Int)) := by
  rw [Syntax.bitvec_overflows_sub_eq, cmp_to_z hn hl, cmp_to_z hn hr]
  cases s
  · simp only [min_for_false, max_for_false, BitVec.usubOverflow, iv,
      rs_toNat_ofInt_nat hl, rs_toNat_ofInt_nat hr, Bool.false_eq_true, ite_false]
    have e3 : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega
  · have := BitVec.le_toInt (BitVec.ofInt n (l : Int))
    have := BitVec.toInt_lt (x := BitVec.ofInt n (l : Int))
    simp only [min_for_true hn, max_for_true hn, BitVec.ssubOverflow, iv]
    rw [Bool.eq_iff_iff]; simp; omega

theorem cmp_overflows_mul (s : Bool) :
    L.bitvec_overflows_mul s (n : Int) (l : Int) (r : Int) =
      if s then (BitVec.ofInt n (l : Int)).smulOverflow (BitVec.ofInt n (r : Int))
      else (BitVec.ofInt n (l : Int)).umulOverflow (BitVec.ofInt n (r : Int)) := by
  rw [Syntax.bitvec_overflows_mul_eq, cmp_to_z hn hl, cmp_to_z hn hr]
  cases s
  · simp only [min_for_false, max_for_false, BitVec.umulOverflow, iv,
      rs_toNat_ofInt_nat hl, rs_toNat_ofInt_nat hr, Bool.false_eq_true, ite_false]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq, ge_iff_le]
    have e2 : ((l * r : Nat) : Int) = (l : Int) * r := by push_cast; rfl
    have e3 : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
    constructor
    · rintro (h | h)
      · have : (0 : Int) ≤ l * r := Int.mul_nonneg (Int.natCast_nonneg l) (Int.natCast_nonneg r)
        omega
      · have : ((2 ^ n : Nat) : Int) ≤ ((l * r : Nat) : Int) := by omega
        exact_mod_cast this
    · intro h; right
      have : ((2 ^ n : Nat) : Int) ≤ ((l * r : Nat) : Int) := by exact_mod_cast h
      omega
  · simp only [min_for_true hn, max_for_true hn, BitVec.smulOverflow, iv]
    rw [Bool.eq_iff_iff]; simp; omega

end

theorem cmp_is_int_min {n p : Nat} (hn : 0 < n) (hp : (p : Int) < 2 ^ n) :
    L.bitvec_is_int_min (n : Int) (p : Int) =
      decide (BitVec.ofInt n (p : Int) = BitVec.intMin n) := by
  rw [Syntax.bitvec_is_int_min_eq, cmp_to_z hn hp, min_for_true hn,
    ← BitVec.toInt_intMin_of_pos hn]
  simp only [iv, ite_true, BitVec.toInt_inj]

theorem cmp_is_min_of {n p : Nat} (hn : 0 < n) (hp : (p : Int) < 2 ^ n) (s : Bool) :
    L.bitvec_is_min_of s (n : Int) (p : Int) =
      decide (if s then (BitVec.ofInt n (p : Int)).toInt = -2 ^ (n - 1)
        else (BitVec.ofInt n (p : Int)).toNat = 0) := by
  rw [Syntax.bitvec_is_min_of_eq, cmp_to_z hn hp]
  cases s
  · simp only [min_for_false, iv, Bool.false_eq_true, ite_false, decide_eq_decide]; omega
  · simp [min_for_true hn, iv]

theorem cmp_is_max_of {n p : Nat} (hn : 0 < n) (hp : (p : Int) < 2 ^ n) (s : Bool) :
    L.bitvec_is_max_of s (n : Int) (p : Int) =
      decide (if s then (BitVec.ofInt n (p : Int)).toInt = 2 ^ (n - 1) - 1
        else ((BitVec.ofInt n (p : Int)).toNat : Int) = 2 ^ n - 1) := by
  rw [Syntax.bitvec_is_max_of_eq, cmp_to_z hn hp]
  cases s
  · simp [max_for_false, iv]
  · simp [max_for_true hn, iv]

theorem cmp_const_keeps_in_range {n x y : Nat} (hn : 0 < n) (hx : (x : Int) < 2 ^ n)
    (hy : (y : Int) < 2 ^ n) (s : Bool) :
    L.bitvec_const_keeps_in_range s (n : Int) (x : Int) (y : Int) =
      decide ((0 ≤ iv s (BitVec.ofInt n (x : Int)) ∧
          0 ≤ iv s (BitVec.ofInt n (x : Int)) - iv s (BitVec.ofInt n (y : Int)) ∧
          iv s (BitVec.ofInt n (x : Int)) - iv s (BitVec.ofInt n (y : Int)) ≤
            iv s (BitVec.ofInt n (x : Int))) ∨
        (iv s (BitVec.ofInt n (x : Int)) ≤ 0 ∧
          iv s (BitVec.ofInt n (x : Int)) ≤
            iv s (BitVec.ofInt n (x : Int)) - iv s (BitVec.ofInt n (y : Int)) ∧
          iv s (BitVec.ofInt n (x : Int)) - iv s (BitVec.ofInt n (y : Int)) ≤ 0)) := by
  simp only [Syntax.bitvec_const_keeps_in_range_eq, Syntax.bitvec_zmin_eq, Syntax.bitvec_zmax_eq,
    cmp_to_z hn hx, cmp_to_z hn hy]
  generalize iv s (BitVec.ofInt n (x : Int)) = a
  generalize iv s (BitVec.ofInt n (y : Int)) = b
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  split <;> split <;> omega

/-- A literal that is not zero is in the subsort `Nonzero`. -/
theorem cmp_nonzero_lit {z : Int} {t : S.Ty} (w : S.WT (B.node (L.BitVecK z) t)) (hz : ¬z = 0) :
    L.Nonzero (B.node (L.BitVecK z) t) := by
  rw [Syntax.WT_BitVec, Sem.bv_wf_BitVec] at w
  obtain ⟨⟨m, hm, rfl⟩, h0, h1⟩ := w
  apply Sem.nonzero_BitVec
  intro n hn
  rw [Sem.size_of_ty_TBitVector] at hn h1
  subst hn
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  intro e
  have := congrArg BitVec.toNat e
  rw [rs_toNat_ofInt_nat (by simpa using h1)] at this
  simp at this
  omega

/-- `Sem.den_msb`, on integers. -/
theorem cmp_den_msb {ρ : S.Env} {v : S.Term} {n : Nat} (w : S.WT v)
    (ht : S.ty v = L.TBitVector (n : Int)) :
    ∀ x, Sem.den L ρ n v = some x → (x.toNat : Int) < 2 ^ (L.bitvec_msb_of v + 1).toNat := by
  intro x h
  exact_mod_cast Sem.den_msb ρ v n x w ht h

/-- The cancellable factors are positive (as signed integers when `s`). -/
theorem cmp_cancellable_den {ρ : S.Env} {s : Bool} {a : S.Term} {n : Nat} (w : S.WT a)
    (ht : S.ty a = L.TBitVector (n : Int)) (h : L.bitvec_cancellable s a = true) :
    ∀ A, Sem.den L ρ n a = some A → if s then 0 < A.toInt else 0 < A.toNat := by
  intro A hA
  have hn : 0 < n := by
    have := (Sem.ev_bv ρ a (Sem.vbv L n A) (n : Int) w ht ((Sem.den_iff ρ n a A w ht).1 hA)).1
    omega
  rw [Syntax.bitvec_cancellable_eq] at h
  cases s
  · simp only [Bool.false_eq_true, ite_false] at h ⊢
    rw [Syntax.bitvec_size_eq, ht, Sem.size_of_ty_TBitVector, Sem.bv_zero_eq] at h
    have wz : S.WT (B.node (L.BitVecK 0) (L.TBitVector (n : Int))) := by
      rw [Syntax.WT_BitVec, Sem.bv_wf_BitVec, Sem.size_of_ty_TBitVector]
      exact ⟨⟨_, by omega, rfl⟩, by omega,
        by simp [Int.toNat_natCast]; exact Int.pow_pos (by decide)⟩
    refine Nat.pos_of_ne_zero fun h0 => KanonBool.Sem.sure_neq_sound ρ _ _ _ h
      (by rw [ht, Kanon.Base.ty_node]) w wz ((Sem.den_iff ρ n a A w ht).1 hA) ?_
    rw [Sem.ev_BitVec, Sem.size_of_ty_TBitVector, Int.toNat_natCast]
    congr 2
    apply BitVec.eq_of_toNat_eq; simp [h0]
  · simp only [ite_true] at h ⊢
    cases e : L.asBitVec a with
    | none => simp [e, Kanon.firstSome] at h
    | some z =>
      simp only [e, Kanon.firstSome] at h
      have ha := L.asBitVec_sound a z e
      rw [ha, Sem.den_BitVec, Option.some.injEq] at hA
      subst hA
      rw [ha] at w
      rw [Syntax.bitvec_to_z_eq, Sem.signed_extract_eq, Syntax.bitvec_size_eq, ht,
        Sem.size_of_ty_TBitVector] at h
      simp only [HOrElse.hOrElse, OrElse.orElse, Option.orElse, ite_true, Option.getD_some,
        decide_eq_true_eq, gt_iff_lt] at h
      rw [← rs_sext_of hn]; exact h

end

/-- The sign bit of `signed_to_unsigned_cmp`. -/
theorem cmp_sign_bit {n : Nat} (hn : 0 < n) :
    BitVec.ofInt n (2 ^ ((n : Int) - 1).toNat) = BitVec.intMin n := by
  have e : (2 : Int) ^ ((n : Int) - 1).toNat = ((2 ^ (n - 1) : Nat) : Int) := by
    push_cast; congr 1; omega
  rw [e, BitVec.ofInt_natCast, ← BitVec.toNat_inj, BitVec.toNat_intMin_of_pos hn,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.two_pow_pred_lt_two_pow hn)]

theorem cmp_binB_ite_l {α : Type} {f : α → α → Bool} {c : Prop} [Decidable c]
    (a a' b : Option α) :
    binB f (if c then a else a') b = if c then binB f a b else binB f a' b := by
  split <;> rfl

theorem cmp_binB_ite_r {α : Type} {f : α → α → Bool} {c : Prop} [Decidable c]
    (a b b' : Option α) :
    binB f a (if c then b else b') = if c then binB f a b else binB f a b' := by
  split <;> rfl

theorem cmp_eq_intMin_iff {n : Nat} (hn : 0 < n) (x : BitVec n) :
    x = BitVec.intMin n ↔ x.toInt = -2 ^ (n - 1) := by
  rw [← BitVec.toInt_inj, BitVec.toInt_intMin_of_pos hn]

/-! ## Facts for `omega` -/

/-- A quotient by `d` is at most `n` when `n * d` overflows. -/
theorem cmp_smtUDiv_ule_of_umulOverflow {w : Nat} {x n d : BitVec w} (h : n.umulOverflow d = true) :
    (x.smtUDiv d).ule n = true := by
  simp only [BitVec.umulOverflow, decide_eq_true_eq] at h
  have hd : d.toNat ≠ 0 := by intro e; rw [e] at h; have := Nat.two_pow_pos w; omega
  have := x.isLt
  simp only [BitVec.ule, decide_eq_true_eq, smtUDiv_toNat hd]
  have : x.toNat < (n.toNat + 1) * d.toNat := by rw [Nat.add_mul]; omega
  have := (Nat.div_lt_iff_lt_mul (by omega)).2 this
  omega

/-! ## Facts for `omega` -/

theorem cmp_toInt_neg_cases {w : Nat} (x : BitVec w) :
    (-x).toInt = -x.toInt ∨ ((-x).toInt = x.toInt ∧ x.toInt = -2 ^ (w - 1)) := by
  rw [BitVec.toInt_neg_eq_ite]
  split
  · next h => subst h; rcases Nat.eq_zero_or_pos w with rfl | hw <;>
      simp [BitVec.toInt_zero_length, BitVec.toInt_intMin_of_pos, *]
  · exact .inl rfl

theorem cmp_toNat_neg_cases {w : Nat} (x : BitVec w) :
    (x.toNat = 0 ∧ (-x).toNat = 0) ∨
      (0 < x.toNat ∧ ((-x).toNat : Int) = 2 ^ w - x.toNat) := by
  rw [BitVec.toNat_neg]
  have := x.isLt
  by_cases h : x.toNat = 0
  · left; simp [h]
  · right; rw [Nat.mod_eq_of_lt (by omega), Int.ofNat_sub (by omega)]; push_cast; omega

theorem cmp_toNat_add_cases {w : Nat} (x y : BitVec w) :
    ((x + y).toNat : Int) = x.toNat + y.toNat ∨
      ((x + y).toNat : Int) = x.toNat + y.toNat - 2 ^ w := by
  have := x.isLt; have := y.isLt
  have e : ((2 ^ w : Nat) : Int) = 2 ^ w := by push_cast; rfl
  rw [BitVec.toNat_add]
  by_cases h : x.toNat + y.toNat < 2 ^ w
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem cmp_toNat_sub_cases {w : Nat} (x y : BitVec w) :
    ((x - y).toNat : Int) = x.toNat - y.toNat ∨
      ((x - y).toNat : Int) = x.toNat - y.toNat + 2 ^ w := by
  have := x.isLt; have := y.isLt
  have e : ((2 ^ w : Nat) : Int) = 2 ^ w := by push_cast; rfl
  rw [BitVec.toNat_sub]
  by_cases h : y.toNat ≤ x.toNat
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem cmp_toNat_bounds {w : Nat} (x : BitVec w) : (x.toNat : Int) < 2 ^ w := by
  have := x.isLt; exact_mod_cast this

theorem cmp_toInt_toNat_cases {w : Nat} (x : BitVec w) :
    (2 * (x.toNat : Int) < 2 ^ w ∧ x.toInt = x.toNat) ∨
      (2 ^ w ≤ 2 * (x.toNat : Int) ∧ x.toInt = x.toNat - 2 ^ w) := by
  have e : ((2 ^ w : Nat) : Int) = 2 ^ w := by push_cast; rfl
  rw [BitVec.toInt_eq_toNat_cond, e]; split <;> omega

/-- The powers of two of a width, for `omega`. -/
theorem cmp_two_pow_facts (w : Nat) :
    ((2 ^ w : Nat) : Int) = (2 : Int) ^ w ∧ ((2 ^ (w - 1) : Nat) : Int) = (2 : Int) ^ (w - 1) ∧
      ((2 : Int) ^ w = 2 * 2 ^ (w - 1) ∨ w = 0) ∧ (0 : Int) < 2 ^ (w - 1) := by
  refine ⟨by push_cast; rfl, by push_cast; rfl, ?_, Int.pow_pos (by decide)⟩
  rcases Nat.eq_zero_or_pos w with h | h
  · exact .inr h
  · exact .inl (by rw [← Int.pow_succ', Nat.sub_add_cancel h])

/-- Cancelling a positive factor, for `omega`. -/
theorem cmp_mul_cmp_facts (p q r : Int) :
    0 < p → (p * q < p * r ↔ q < r) ∧ (p * q ≤ p * r ↔ q ≤ r) := fun h =>
  ⟨Int.mul_lt_mul_left h, Int.mul_le_mul_left h⟩

theorem cmp_nat_mul_cmp_facts (p q r : Nat) :
    0 < p → (p * q < p * r ↔ q < r) ∧ (p * q ≤ p * r ↔ q ≤ r) := fun h =>
  ⟨Nat.mul_lt_mul_left h, Nat.mul_le_mul_left_iff h⟩

/-- `cmp_tdiv_facts`, for natural numbers. -/
theorem cmp_div_facts (C2 C1 X : Nat) : C1 ≠ 0 →
    C2 = C2 / C1 * C1 + C2 % C1 ∧ C2 % C1 < C1 ∧
    (X + 1 ≤ C2 / C1 → X * C1 + C1 ≤ C2 / C1 * C1) ∧
    (C2 / C1 + 1 ≤ X → C2 / C1 * C1 + C1 ≤ X * C1) ∧
    (X = C2 / C1 → X * C1 = C2 / C1 * C1) := by
  intro h
  have e := Nat.div_add_mod C2 C1
  refine ⟨by rw [Nat.mul_comm]; omega, Nat.mod_lt _ (by omega), fun hx => ?_, fun hx => ?_,
    fun hx => by rw [hx]⟩
  · have := Nat.mul_le_mul_right C1 hx; rw [Nat.add_mul, Nat.one_mul] at this; exact this
  · have := Nat.mul_le_mul_right C1 hx; rw [Nat.add_mul, Nat.one_mul] at this; exact this

/-- The truncated quotient `D` of `C2` by `C1` (and its remainder), and how the
products `X * C1` compare to `D * C1`, for `omega`. -/
theorem cmp_tdiv_facts (C2 C1 X : Int) : C1 ≠ 0 →
    C2 = C2.tdiv C1 * C1 + C2.tmod C1 ∧ (0 ≤ C2 → 0 ≤ C2.tmod C1) ∧
    (C2 ≤ 0 → C2.tmod C1 ≤ 0) ∧
    (0 < C1 → -C1 < C2.tmod C1 ∧ C2.tmod C1 < C1) ∧
    (C1 < 0 → C1 < C2.tmod C1 ∧ C2.tmod C1 < -C1) ∧
    (X ≤ C2.tdiv C1 - 1 → (0 < C1 → X * C1 ≤ C2.tdiv C1 * C1 - C1) ∧
      (C1 < 0 → C2.tdiv C1 * C1 - C1 ≤ X * C1)) ∧
    (C2.tdiv C1 + 1 ≤ X → (0 < C1 → C2.tdiv C1 * C1 + C1 ≤ X * C1) ∧
      (C1 < 0 → X * C1 ≤ C2.tdiv C1 * C1 + C1)) ∧
    (X = C2.tdiv C1 → X * C1 = C2.tdiv C1 * C1) := by
  intro h
  have e := Int.tmod_add_tdiv_mul C2 C1
  refine ⟨by omega, fun h => Int.tmod_nonneg _ h, fun h => ?_, fun h => ?_, fun h => ?_,
    fun hx => ⟨fun hc => ?_, fun hc => ?_⟩, fun hx => ⟨fun hc => ?_, fun hc => ?_⟩,
    fun hx => by rw [hx]⟩
  · have := Int.tmod_nonneg C1 (show 0 ≤ -C2 by omega)
    rw [Int.neg_tmod] at this; omega
  · exact ⟨Int.lt_tmod_of_pos _ h, Int.tmod_lt_of_pos _ h⟩
  · have h1 := Int.lt_tmod_of_pos C2 (show 0 < -C1 by omega)
    have h2 := Int.tmod_lt_of_pos C2 (show 0 < -C1 by omega)
    rw [Int.tmod_neg] at h1 h2; omega
  · have := Int.mul_le_mul_of_nonneg_right hx (Int.le_of_lt hc)
    rw [Int.sub_mul, Int.one_mul] at this; exact this
  · have := Int.mul_le_mul_of_nonpos_right hx (Int.le_of_lt hc)
    rw [Int.sub_mul, Int.one_mul] at this; exact this
  · have := Int.mul_le_mul_of_nonneg_right hx (Int.le_of_lt hc)
    rw [Int.add_mul, Int.one_mul] at this; exact this
  · have := Int.mul_le_mul_of_nonpos_right hx (Int.le_of_lt hc)
    rw [Int.add_mul, Int.one_mul] at this; exact this

theorem cmp_toInt_smtSDiv_facts {w : Nat} (a b : BitVec w) : b.toInt ≠ 0 →
    ¬(a.toInt = -2 ^ (w - 1) ∧ b.toInt = -1) → (a.smtSDiv b).toInt = a.toInt.tdiv b.toInt := by
  intro hb hov
  have hb0 : b ≠ 0#w := by rintro rfl; simp at hb
  have hw : 0 < w := by
    rcases Nat.eq_zero_or_pos w with rfl | h
    · simp [BitVec.toInt_zero_length] at hb
    · exact h
  have hb' : -b ≠ 0#w := fun h => hb0 (BitVec.neg_eq_zero_iff.1 h)
  have e : a.smtSDiv b = a.sdiv b := by
    rw [BitVec.smtSDiv_eq, BitVec.sdiv]
    rcases a.msb <;> rcases b.msb <;> simp [BitVec.smtUDiv_eq, hb0, hb']
  rw [e]
  apply BitVec.toInt_sdiv_of_ne_or_ne
  by_cases ha : a = BitVec.intMin w
  · right; rintro rfl
    apply hov
    refine ⟨by rw [ha, BitVec.toInt_intMin_of_pos hw], ?_⟩
    simp [BitVec.neg_one_eq_allOnes, BitVec.toInt_allOnes, hw]
  · exact .inl ha

theorem cmp_toNat_smtUDiv_facts {w : Nat} (a b : BitVec w) : b.toNat ≠ 0 →
    (a.smtUDiv b).toNat = a.toNat / b.toNat := smtUDiv_toNat

/-! ## Adding the facts -/

open Lean Meta in
/-- The subterms `x` of the goal and hypotheses (bit-vectors of any width) such
that `f x` is a subterm, where `p` recognizes `f x` and returns `x`. -/
def cmp_collectArgs (g : MVarId) (p : Expr → Option Expr) : MetaM (Array Expr) := g.withContext do
  let mut exprs : Array Expr := #[← instantiateMVars (← g.getType)]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then exprs := exprs.push (← instantiateMVars d.type)
  let atoms ← IO.mkRef (#[] : Array Expr)
  for e in exprs do
    e.forEach' fun sub => do
      if let some x := p sub then
        unless x.hasLooseBVars || (← atoms.get).contains x do atoms.modify (·.push x)
      return true
  atoms.get

open Lean Meta in
/-- Adds `lem x` for each of the `xs`. -/
def cmp_addFacts (g : MVarId) (lems : List Name) (xs : Array Expr) : MetaM MVarId := do
  let mut g := g
  for x in xs do
    for lem in lems do
      let pf ← g.withContext (mkAppM lem #[x])
      let (_, g') ← (← g.assert `hbd (← g.withContext (inferType pf)) pf).intro1P
      g := g'
  return g

open Lean Meta in
/-- `cmp_collectArgs`, for binary functions. -/
def cmp_collectArgs2 (g : MVarId) (p : Expr → Option (Expr × Expr)) :
    MetaM (Array (Expr × Expr)) := g.withContext do
  let mut exprs : Array Expr := #[← instantiateMVars (← g.getType)]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then exprs := exprs.push (← instantiateMVars d.type)
  let atoms ← IO.mkRef (#[] : Array (Expr × Expr))
  for e in exprs do
    e.forEach' fun sub => do
      if let some (x, y) := p sub then
        unless x.hasLooseBVars || y.hasLooseBVars || (← atoms.get).contains (x, y) do
          atoms.modify (·.push (x, y))
      return true
  atoms.get

open Lean Meta in
/-- Adds `lem x y` for each of the `xys`. -/
def cmp_addFacts2 (g : MVarId) (lem : Name) (xys : Array (Expr × Expr)) : MetaM MVarId := do
  let mut g := g
  for (x, y) in xys do
    let pf ← g.withContext (mkAppM lem #[x, y])
    let (_, g') ← (← g.assert `hbd (← g.withContext (inferType pf)) pf).intro1P
    g := g'
  return g

theorem cmp_toNat_ofInt_fact {n : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ n) :
    ((BitVec.ofInt n z).toNat : Int) = z := by
  rw [toNat_ofInt_of_lt h0 h1]; omega

theorem cmp_toInt_ofInt_fact {n : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ n) :
    ((BitVec.ofInt n z).toInt = z ∧ 2 * z < 2 ^ n) ∨
      ((BitVec.ofInt n z).toInt = z - 2 ^ n ∧ 2 ^ n ≤ 2 * z) := by
  have e : ((BitVec.ofInt n z).toNat : Int) = z := cmp_toNat_ofInt_fact h0 h1
  have hp : ((2 ^ n : Nat) : Int) = 2 ^ n := by push_cast; rfl
  rw [BitVec.toInt_eq_toNat_cond]
  split
  · rename_i h
    have h' : 2 * ((BitVec.ofInt n z).toNat : Int) < ((2 ^ n : Nat) : Int) := by exact_mod_cast h
    left; refine ⟨e, ?_⟩; omega
  · rename_i h
    have h' : ((2 ^ n : Nat) : Int) ≤ 2 * ((BitVec.ofInt n z).toNat : Int) := by
      exact_mod_cast Nat.le_of_not_lt h
    right; refine ⟨?_, ?_⟩
    · omega
    · omega

theorem cmp_bmod_ofInt_fact {n : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ n) :
    (z.bmod (2 ^ n) = z ∧ 2 * z < 2 ^ n) ∨
      (z.bmod (2 ^ n) = z - 2 ^ n ∧ 2 ^ n ≤ 2 * z) := by
  have := cmp_toInt_ofInt_fact h0 h1
  rwa [BitVec.toInt_ofInt] at this

open Lean Meta Elab Tactic in
/-- A hypothesis of type `t`, or else a proof of it by `omega` (the range facts
of the literals, which `simp` may have rewritten). -/
def cmpFindFact (t : Expr) : TacticM (Option Expr) := do
  if let some h ← Kanon.Proof.findHyp t then return some h
  let mv ← mkFreshExprMVar t
  try
    let gs ← Tactic.run mv.mvarId! (evalTactic (← `(tactic| omega)))
    if gs.isEmpty then return some (← instantiateMVars mv) else return none
  catch _ => return none

open Lean Meta Elab Tactic in
/-- Adds the values (`toNat`, `toInt`) of the literals `BitVec.ofInt n z` of the goal and
hypotheses, from their range. -/
elab "bv_cmp_lit_facts" : tactic => withMainContext do
  let g ← getMainGoal
  let atoms ← cmp_collectArgs g fun e =>
    if (e.isAppOfArity ``BitVec.toNat 2 || e.isAppOfArity ``BitVec.toInt 2) &&
        e.appArg!.isAppOfArity ``BitVec.ofInt 2 then some e.appArg! else none
  let bmods ← cmp_collectArgs g fun e =>
    if e.isAppOfArity ``Int.bmod 2 then some e else none
  for a in bmods do
    let c ← mkConstWithFreshMVarLevels ``cmp_bmod_ofInt_fact
    let (mvs, _, _) ← forallMetaTelescopeReducing (← inferType c)
    unless (← isDefEq mvs[1]! (a.getArg! 0)) do continue
    let mut ok := true
    for mv in mvs[2:] do
      match ← cmpFindFact (← instantiateMVars (← inferType mv)) with
      | some h => unless ← isDefEq mv h do ok := false
      | none => ok := false
    if ok then
      let pf ← instantiateMVars (mkAppN c mvs)
      let (_, g') ← (← (← getMainGoal).assert `hlf (← inferType pf) pf).intro1P
      replaceMainGoal [g']
  for a in atoms do
    for lem in [``cmp_toNat_ofInt_fact, ``cmp_toInt_ofInt_fact] do
      let c ← mkConstWithFreshMVarLevels lem
      let (mvs, _, _) ← forallMetaTelescopeReducing (← inferType c)
      unless (← isDefEq mvs[0]! a.appFn!.appArg!) && (← isDefEq mvs[1]! a.appArg!) do continue
      let mut ok := true
      for mv in mvs[2:] do
        match ← cmpFindFact (← instantiateMVars (← inferType mv)) with
        | some h => unless ← isDefEq mv h do ok := false
        | none => ok := false
      if ok then
        let pf ← instantiateMVars (mkAppN c mvs)
        let (_, g') ← (← (← getMainGoal).assert `hlf (← inferType pf) pf).intro1P
        replaceMainGoal [g']

open Lean Meta Elab Tactic in
/-- Adds the facts on the values of the bit-vectors of the goal and hypotheses
that `omega` needs: their bounds, those of their negations, and the relation
between their signed and unsigned values (when both occur). -/
elab "bv_cmp_cmp_bounds" : tactic => liftMetaTactic fun g => do
  let arg (f : Name) (e : Expr) : Option Expr :=
    if e.isAppOfArity f 2 then some e.appArg! else none
  let neg (f : Name) (e : Expr) : Option Expr :=
    (arg f e).bind fun x => if x.isAppOfArity ``Neg.neg 3 then some x.appArg! else none
  let g ← cmp_addFacts g [``cmp_toInt_neg_cases] (← cmp_collectArgs g (neg ``BitVec.toInt))
  let g ← cmp_addFacts g [``cmp_toNat_neg_cases] (← cmp_collectArgs g (neg ``BitVec.toNat))
  let bin (op : Name) (e : Expr) : Option (Expr × Expr) :=
    (arg ``BitVec.toInt e <|> arg ``BitVec.toNat e).bind fun x =>
      if x.isAppOfArity op 6 then some (x.getArg! 4, x.getArg! 5) else none
  -- the sums and differences whose value is already given (by an overflow fact)
  let known ← g.withContext do
    (← getLCtx).foldlM (init := #[]) fun acc d => do
      let some (_, lhs, _) := (← instantiateMVars d.type).eq? | return acc
      return match arg ``BitVec.toInt lhs <|> arg ``BitVec.toNat lhs with
        | some x => acc.push x
        | none => acc
  let unknown (op : Name) (xys : Array (Expr × Expr)) : MetaM (Array (Expr × Expr)) :=
    g.withContext <| xys.filterM fun (x, y) => do
      let e ← mkAppM op #[x, y]
      return !(← known.anyM (isDefEq e ·))
  let g ← cmp_addFacts2 g ``cmp_toNat_add_cases
    (← unknown ``HAdd.hAdd (← cmp_collectArgs2 g (bin ``HAdd.hAdd)))
  let g ← cmp_addFacts2 g ``cmp_toNat_sub_cases
    (← unknown ``HSub.hSub (← cmp_collectArgs2 g (bin ``HSub.hSub)))
  let dedup (xs : Array Expr) : MetaM (Array Expr) := g.withContext do
    xs.foldlM (init := #[]) fun acc x => do
      if ← acc.anyM (isDefEq x ·) then return acc else return acc.push x
  let is ← dedup (← cmp_collectArgs g (arg ``BitVec.toInt))
  let ns ← dedup (← cmp_collectArgs g (arg ``BitVec.toNat))
  let g ← cmp_addFacts g [``toInt_bounds] is
  let g ← cmp_addFacts g [``cmp_toNat_bounds] ns
  return [← cmp_addFacts g [``cmp_toInt_toNat_cases] (is.filter ns.contains)]

open Lean Meta Elab Tactic in
/-- Adds the facts on the powers of two of the widths of the bit-vectors of the
context. -/
elab "bv_cmp_pow_facts" : tactic => liftMetaTactic fun g => g.withContext do
  let mut ws : Array Expr := #[]
  for d in (← getLCtx) do
    let ty ← whnfR (← instantiateMVars d.type)
    if ty.isAppOfArity ``BitVec 1 && !ws.contains ty.appArg! then ws := ws.push ty.appArg!
  return [← cmp_addFacts g [``cmp_two_pow_facts] ws]

open Lean Meta in
/-- Generalizes the values (`toInt`, `toNat`) of the bit-vectors of the goal
and hypotheses, and the powers of two, so that `omega` treats them as atoms. -/
partial def cmp_genValues (g : MVarId) : MetaM MVarId := g.withContext do
  let isVal (e : Expr) : Bool := !e.hasLooseBVars &&
    (e.isAppOfArity ``BitVec.toInt 2 || e.isAppOfArity ``BitVec.toNat 2 ||
      (e.isAppOfArity ``HPow.hPow 6 && (e.getArg! 5).nat?.isNone))
  let mut cand : Option Expr := (← instantiateMVars (← g.getType)).find? isVal
  for d in (← getLCtx) do
    if cand.isNone && !d.isImplementationDetail then
      cand := (← instantiateMVars d.type).find? isVal
  let some v := cand | return g
  -- the occurrences are found up to instances, so all the facts are generalized
  let hyps ← (← getLCtx).foldlM (init := #[]) fun acc d => do
    if d.isImplementationDetail then return acc
    if ← isProp d.type then return acc.push d.fvarId
    return acc
  let (_, _, g) ← g.generalizeHyp #[{ expr := v, xName? := `v }] hyps
  cmp_genValues g

open Lean Meta Elab Tactic in
elab "bv_cmp_gen_values" : tactic => liftMetaTactic fun g => return [← cmp_genValues g]

open Lean Meta in
/-- The products `p * q` of integers (or natural numbers) of the goal and
hypotheses. -/
def cmp_collectProducts (g : MVarId) (int : Bool) : MetaM (Array (Expr × Expr)) :=
  cmp_collectArgs2 g fun e =>
    if e.isAppOfArity ``HMul.hMul 6 && (e.getArg! 0).isConstOf (if int then ``Int else ``Nat) &&
        (e.getArg! 4).int?.isNone && (e.getArg! 5).int?.isNone &&
        (e.getArg! 4).nat?.isNone && (e.getArg! 5).nat?.isNone then
      some (e.getArg! 4, e.getArg! 5)
    else none

open Lean Meta Elab Tactic in
/-- Adds the facts on the products and quotients of the goal and hypotheses
that `omega` needs: cancelling a common factor of two products, and the
quotients by a divisor that also multiplies. -/
elab "bv_cmp_mul_facts" : tactic => liftMetaTactic fun g => do
  let mut g := g
  -- cancelling a factor common to two products (in any position: with the
  -- commutativity of the products whose factors are swapped)
  for (int, lem, comm) in [(true, ``cmp_mul_cmp_facts, ``Int.mul_comm),
      (false, ``cmp_nat_mul_cmp_facts, ``Nat.mul_comm)] do
    let ps ← cmp_collectProducts g int
    for i in [0:ps.size] do
      for j in [i+1:ps.size] do
        let (a, b) := ps[i]!
        let (c, d) := ps[j]!
        let cands : List (Bool × Expr × Expr × Expr × List (Expr × Expr)) :=
          [(a == c, a, b, d, []), (b == d, b, a, c, [(a, b), (c, d)]),
           (a == d, a, b, c, [(c, d)]), (b == c, b, a, d, [(a, b)])]
        for (common, p, q, r, swaps) in cands do
          unless common && q != r do continue
          for (x, y) in swaps do
            let pf ← g.withContext (mkAppM comm #[x, y])
            let (_, g') ← (← g.assert `hcomm (← g.withContext (inferType pf)) pf).intro1P
            g := g'
          let pf ← g.withContext (mkAppM lem #[p, q, r])
          let (_, g') ← (← g.assert `hmul (← g.withContext (inferType pf)) pf).intro1P
          g := g'
  let divs (f : Name) := cmp_collectArgs2 g fun e =>
    if e.isAppOfArity f 3 then some (e.getArg! 1, e.getArg! 2) else none
  let sdivs ← divs ``BitVec.smtSDiv
  let udivs ← divs ``BitVec.smtUDiv
  g ← cmp_addFacts2 g ``cmp_toInt_smtSDiv_facts sdivs
  g ← cmp_addFacts2 g ``cmp_toNat_smtUDiv_facts udivs
  for (int, ds, val, lem, comm) in [(true, sdivs, ``BitVec.toInt, ``cmp_tdiv_facts, ``Int.mul_comm),
      (false, udivs, ``BitVec.toNat, ``cmp_div_facts, ``Nat.mul_comm)] do
    let ps ← cmp_collectProducts g int
    for (a, b) in ds do
      let (c2, c1) ← g.withContext do return (← mkAppM val #[a], ← mkAppM val #[b])
      let mut done : Array Expr := #[]
      for (x, q) in ps do
        -- the product `x * c1`, or `c1 * x` with its commutativity
        let (x, swapped) ←
          if ← g.withContext (isDefEq q c1) then pure (x, false)
          else if ← g.withContext (isDefEq x c1) then pure (q, true)
          else continue
        if done.contains x then continue
        done := done.push x
        if swapped then
          let pf ← g.withContext (mkAppM comm #[c1, x])
          let (_, g') ← (← g.assert `hcomm (← g.withContext (inferType pf)) pf).intro1P
          g := g'
        let pf ← g.withContext (mkAppM lem #[c2, c1, x])
        let (_, g') ← (← g.assert `hdiv (← g.withContext (inferType pf)) pf).intro1P
        g := g'
  return [g]

open Lean Meta Elab Tactic in
/-- Clears the facts that only hold under an unknown checked flag
(`c.signed = true → _`), which `omega` cannot use. -/
elab "bv_cmp_clear_flags" : tactic => liftMetaTactic fun g => g.withContext do
  let mut g := g
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let .forallE _ dom _ _ := ty then
      if let some (_, lhs, _) := dom.eq? then
        if lhs.isAppOfArity ``CoreMod.Checked.signed 1 ||
            lhs.isAppOfArity ``CoreMod.Checked.unsigned 1 then
          g ← g.clear d.fvarId
  return [g]

open Lean Meta Elab Tactic in
elab "bv_cmp_ovf_eqs" : tactic => liftMetaTactic fun g => return [← ovfEqs g]

/-! ## Facts on the terms -/

open Lean Meta Elab Tactic in
/-- The pairs of a well-typed term `v` of the context and the hypothesis giving
its sort `TBitVector ↑n` (as `S.ty v = _`). -/
def cmpTypedTerms (g : MVarId) : MetaM (Array (Expr × Expr × Expr × Expr)) := g.withContext do
  -- the sorts `S.ty v = TBitVector ↑n` that the hypotheses give, through `S.ty v = S.ty u`
  let mut sorts : Array (Expr × Expr × Expr) := #[]
  let eqs ← (← getLCtx).foldlM (init := #[]) fun acc d => do
    if d.isImplementationDetail then return acc
    let some (_, a, b) := (← instantiateMVars d.type).eq? | return acc
    return acc.push (a, b, d.toExpr)
  for _ in [0:3] do
    for (a, b, h) in eqs do
      for (lhs, rhs, pf) in [(a, b, pure h), (b, a, mkEqSymm h)] do
        unless lhs.isAppOfArity ``Kanon.Sem.ty 2 do continue
        let v := lhs.appArg!
        if ← sorts.anyM (fun (u, _, _) => isDefEq u v) then continue
        if rhs.isAppOfArity ``Kanon.Sem.ty 2 then
          let some (_, hu, n) ← sorts.findM? (fun (u, _, _) => isDefEq u rhs.appArg!) | continue
          sorts := sorts.push (v, ← mkEqTrans (← pf) hu, n)
        else
          let rhs ← whnfR rhs
          unless rhs.getAppNumArgs ≥ 1 do continue
          let n := rhs.appArg!
          unless n.isAppOfArity ``Nat.cast 3 do continue
          sorts := sorts.push (v, ← pf, n.appArg!)
  let mut out := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOfArity ``Kanon.Sem.WT 2 do continue
    let v := ty.appArg!
    if ← out.anyM (fun (u, _, _, _) => isDefEq u v) then continue
    if let some (_, ht, n) ← sorts.findM? (fun (u, _, _) => isDefEq u v) then
      out := out.push (v, d.toExpr, ht, n)
  return out

open Lean Meta Elab Tactic in
/-- Adds, for the terms `v` whose `Bitvec.msb_of` occurs, the bound of their
values (`Sem.den_msb`), and for the cancellable factors, their sign
(`cmp_cancellable_den`). -/
elab "bv_cmp_term_facts" : tactic => withMainContext do
  let g ← getMainGoal
  let some ρ := (← getLCtx).findDecl? fun d =>
      if d.type.isAppOfArity ``Kanon.Sem.Env 1 then some d.toExpr else none
    | return
  let terms ← cmpTypedTerms g
  let mut exprs : Array Expr := #[← instantiateMVars (← g.getType)]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then exprs := exprs.push (← instantiateMVars d.type)
  for (v, w, ht, n) in terms do
    let msb := exprs.any fun e => (e.find? fun s =>
      s.isAppOf ``BitvecMod.Syntax.bitvec_msb_of && s.getAppNumArgs == 8 && s.appArg! == v).isSome
    if msb then
      let (ρs, vs, ns, ws, hts) := (← Term.exprToSyntax ρ, ← Term.exprToSyntax v,
        ← Term.exprToSyntax n, ← Term.exprToSyntax w, ← Term.exprToSyntax ht)
      evalTactic (← `(tactic|
        have := BitvecMod.Lib.cmp_den_msb (ρ := $ρs) (v := $vs) (n := $ns) $ws $hts))
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let some (_, lhs, _) := (← instantiateMVars d.type).eq? | continue
    unless lhs.isAppOf ``BitvecMod.Syntax.bitvec_cancellable && lhs.getAppNumArgs == 9 do continue
    let a := lhs.appArg!
    for (v, w, ht, _) in terms do
      if v == a then
        let (ρs, ws, hts, hs) := (← Term.exprToSyntax ρ, ← Term.exprToSyntax w,
          ← Term.exprToSyntax ht, ← Term.exprToSyntax d.toExpr)
        evalTactic (← `(tactic|
          have := BitvecMod.Lib.cmp_cancellable_den (ρ := $ρs) $ws $hts $hs))
        break

end Lib
open Lib

set_option hygiene false in
/-- The value half of `Refines.denB` of a comparison, reduced to the values of
the atoms, the literals kept as values (`BitVec.ofInt n z`) and the helpers on
them as operations on these values; its hypothesis is `e`. -/
macro "bv_cmp_sem" : tactic => `(tactic| (
  intro w ρ x e
  bv_rs_facts
  (try bv_rs_nat)
  bv_rs_nat_eqs
  (try simp only [bv_den, bv_lits] at e ⊢)
  (try bv_rs_rw_tys)
  (try simp only [bv_lits, BitvecMod.Lib.TBitVector_inj_iff, Int.ofNat_inj] at *)
  (try subst_vars)
  (try simp (disch := omega) only [ite_eq_left, Int.toNat_natCast,
    BitvecMod.Lib.rs_toNat_natCast_add] at e ⊢)
  (try simp (disch := first | assumption | omega) only [BitvecMod.Lib.cmp_to_z,
    BitvecMod.Lib.cmp_overflows_add, BitvecMod.Lib.cmp_overflows_sub,
    BitvecMod.Lib.cmp_overflows_mul, BitvecMod.Lib.cmp_is_int_min, BitvecMod.Lib.cmp_is_min_of,
    BitvecMod.Lib.cmp_is_max_of, BitvecMod.Lib.cmp_const_keeps_in_range,
    BitvecMod.Syntax.bitvec_unsigned_ub_eq, BitvecMod.Sem.z_lsl_eq, BitvecMod.Lib.z_lsl_one,
    BitvecMod.Sem.divisible_eq, BitvecMod.Prim.divisible] at *)
  (try simp (disch := first | assumption | omega) only [BitvecMod.Lib.rs_ofInt_emod,
    BitvecMod.Lib.rs_ofInt_emod_nat, BitvecMod.Lib.ofInt_masked, BitvecMod.Lib.cmp_sign_bit] at *)
  bv_lit_ops
  bv_cmp_term_facts
  run_tac Kanon.Proof.caseAllAtoms (some #[``BitvecMod.Lib.den_cases, ``BitvecMod.Lib.denB_cases])
  all_goals (try bv_bool_vars)
  all_goals (try simp only [Option.map_some, Option.map_none, Option.some.injEq, forall_eq,
    forall_eq', reduceCtorEq, BitvecMod.ckOp_some, BitvecMod.binOp_some, BitvecMod.negOp_some,
    BitvecMod.negOp_none, BitvecMod.ckOp_none_l, BitvecMod.ckOp_none_r, BitvecMod.binOp_none_l,
    BitvecMod.binOp_none_r, BitvecMod.binB_some, BitvecMod.binB_none_l,
    BitvecMod.binB_none_r, BitvecMod.andB_some, BitvecMod.orB_some] at *)
  all_goals (try (simp [BitvecMod.ckOp] at e; done))
  all_goals (try (repeat' split at e))))

/-- Reduces the goals left by `bv_cmp_sem` to facts on the integer values of
the atoms. -/
macro "bv_cmp_pre" : tactic => `(tactic| (
  (try bv_rs_clear_tys)
  (try simp (disch := first | assumption | omega) only [BitvecMod.negOp_some,
    cmp_eq_intMin_iff] at *)
  all_goals simp_all [iv, BitVec.slt_eq_decide, BitVec.ult_eq_decide, BitVec.sle_eq_decide,
    BitVec.ule_eq_decide, ← BitVec.toNat_inj, cmp_binB_ite_l, cmp_binB_ite_r,
    -BitVec.ofInt_natCast, -BitVec.toInt_ofInt, -BitVec.toNat_ofInt, -BitVec.toNat_neg,
    -BitVec.toNat_add,
    -BitVec.toNat_sub, -BitVec.toNat_mul, -BitVec.toInt_add, -BitVec.toInt_sub, -BitVec.toInt_mul,
    -BitVec.toNat_udiv, -BitVec.toNat_umod, -BitVec.toInt_srem, -BitVec.toNat_intMin]
  all_goals (try simp only [Int.natCast_dvd_natCast, Nat.dvd_iff_mod_eq_zero] at *)
  all_goals (try simp only [Int.dvd_iff_tmod_eq_zero] at *)
  all_goals (try simp (disch := first | assumption | omega) only [BitVec.toNat_intMin_of_pos,
    BitVec.toInt_intMin_of_pos] at *)
  all_goals kanon_split
  all_goals bv_cmp_ovf_eqs
  all_goals (try simp only [sadd_ok, ssub_ok, smul_ok, uadd_ok, usub_ok,
    umul_ok] at *)
  all_goals (try simp only [BitVec.saddOverflow, BitVec.ssubOverflow, BitVec.smulOverflow,
    BitVec.uaddOverflow, BitVec.usubOverflow, BitVec.umulOverflow, decide_eq_true_eq,
    Bool.or_eq_true] at *)
  all_goals kanon_split
  all_goals bv_cmp_clear_flags
  all_goals bv_cmp_mul_facts
  all_goals bv_cmp_lit_facts
  all_goals bv_cmp_cmp_bounds
  all_goals (try push_cast at *)))

theorem cmp_nat_mul_zero (x y : Nat) : (x = 0 → x * y = 0) ∧ (y = 0 → x * y = 0) :=
  ⟨fun h => by simp [h], fun h => by simp [h]⟩

/-- The factors of the products of naturals in `e`, outside binders' scope. -/
partial def cmpMulNats (e : Lean.Expr) (acc : Array (Lean.Expr × Lean.Expr) := #[]) :
    Array (Lean.Expr × Lean.Expr) :=
  let acc :=
    if e.isAppOfArity ``HMul.hMul 6 && e.getArg! 0 == .const ``Nat [] &&
        !e.hasLooseBVars && !acc.contains (e.getArg! 4, e.getArg! 5) then
      acc.push (e.getArg! 4, e.getArg! 5)
    else acc
  match e with
  | .app f a => cmpMulNats a (cmpMulNats f acc)
  | .lam _ t b _ | .forallE _ t b _ => cmpMulNats b (cmpMulNats t acc)
  | .mdata _ b => cmpMulNats b acc
  | _ => acc

open Lean Meta Elab Tactic in
/-- Adds that the products of naturals in the hypotheses are zero when a factor
is: `omega` treats a product as an atom. -/
elab "bv_cmp_mul_zero" : tactic => withMainContext do
  let mut ps : Array (Expr × Expr) := #[]
  for d in (← getLCtx) do
    unless d.isImplementationDetail do ps := cmpMulNats (← instantiateMVars d.type) ps
  for (a, b) in ps do
    let pf ← mkAppM ``BitvecMod.cmp_nat_mul_zero #[a, b]
    let (_, g) ← (← getMainGoal).note `hmz pf
    replaceMainGoal [g]

/-- The conjuncts of a conjunction. -/
partial def cmpConjs (e : Lean.Expr) : List Lean.Expr :=
  if e.isAppOfArity ``And 2 then cmpConjs e.appFn!.appArg! ++ cmpConjs e.appArg! else [e]

open Lean Meta Elab Tactic in
/-- Clears the disjunctions equal to an earlier hypothesis up to the order of
their conjuncts: the facts of a literal can come twice, and each disjunction
doubles the case splits of `omega`. -/
elab "bv_cmp_dedup_or" : tactic => withMainContext do
  let key (e : Expr) : MetaM (List String) := do
    let l ← (cmpConjs e).mapM fun c => do pure (toString (← ppExpr c))
    pure (l.mergeSort (· ≤ ·))
  let mut seen : Std.HashSet String := {}
  let mut dups : Array FVarId := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``Or 2 then
      let k := toString (← key t.appFn!.appArg!) ++ "|" ++ toString (← key t.appArg!)
      if seen.contains k then dups := dups.push d.fvarId else seen := seen.insert k
  replaceMainGoal [← (← getMainGoal).tryClearMany dups]

/-- Closes the goals left by `bv_cmp_sem`, by reasoning on the integer values
of the atoms. -/
macro "bv_cmp_omega" : tactic => `(tactic| (
  bv_cmp_pre
  all_goals bv_cmp_pow_facts
  all_goals bv_cmp_gen_values
  all_goals (try simp only [Int.natCast_inj] at *)
  all_goals (try subst_vars)
  all_goals bv_cmp_dedup_or
  all_goals omega))

/-- Proves an arm of `Bitvec.lt` or `Bitvec.leq`, as far as it can. -/
macro "bv_cmp" : tactic => `(tactic| (
  intro _
  intros
  (try simp only [BitvecMod.Ops.Sound.bitvec_signed_to_unsigned_cmp_eq ‹BitvecMod.Ops.Sound _›])
  bv_rs_rule_lift_core
  bv_rule_apply
  all_goals bv_cmp_bools
  all_goals first
    | (apply cmp_nonzero_lit
       · simp only [bv_wt] at *
         kanon_split
         subst_vars
         refine ⟨⟨?_, ?wa, ?wb⟩, ?wc, ?wd⟩
         case wb => assumption
         case wa => assumption
         case wc => assumption
         case wd => assumption
       · assumption)
    | (bv_cmp_sem
       all_goals (try (bv_cmp_omega; done)))
    | (bv_rs_wt; done)
    | skip))

attribute [kanon_tactic "bv_cmp"] Bitvec.lt.spec Bitvec.leq.spec

end BitvecMod
