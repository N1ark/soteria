import Kanon.Lib.Meta
import Kanon.Lifts
import Kanon.Lib.Lit
import Kanon.Lib.Ovf
import Kanon.Lib.LitOps
import Kanon.Lib.Float
import Kanon.Model.Bitvec.checked_both
import Kanon.Model.Bitvec.checked_has
import Kanon.Model.Bitvec.checked_meet
import Kanon.Model.Bitvec.checked_of_signed
import Kanon.Model.Bitvec.checked_signed
import Kanon.Model.Bitvec.checked_unsigned
import Kanon.Model.Bitvec.is_checked
import Kanon.Model.Bitvec.is_pow2
import Kanon.Model.Bitvec.signed_to_unsigned_cmp
import Kanon.Model.Bitvec.unchecked
import Kanon.Model.Bool.of_bool
import Kanon.Model.mk_commut_binop

/-!
# Tactics for the rule proofs

Kanon's rule tactics (`KanonCore.Proof`), given the lemmas of Bv_values by
their attributes, with the rule tactics of its own:

- `kanon_rule_bv` proves the statement of an alternative of a `[@cases]` rule:
  it takes its guard and lifts the calls of its body to their specs
  (`kanon_rule_lift`), reduces the refinement to the structural values of the
  terms (`Refines.den`, `Refines.denB`), proves the typing half
  (`kanon_wt_bv`), and reduces the value half to the values of the atoms
  (`kanon_sem_bv`), closing what `simp_all` (with the `kanon_close_simp`
  lemmas), `grind` and `kanon_ovf` can, or a `kanon_close_lemma` (its side
  goals by `kanon_nat`).
- `kanon_rule_sem` does the same, but leaves the value goals as
  `kanon_sem_core_bv` leaves them, for the alternatives that need a lemma of
  their own.
- `kanon_nat` proves facts on the natural values of constants in range.
-/

namespace Kanon.Lib

open CoreMod

open Lean Meta Elab Tactic

@[simp] theorem two_pow_pos_int (n : Nat) : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)

@[simp] theorem one_lt_two_pow_int {k : Nat} : (1 : Int) < 2 ^ k ↔ 0 < k := by
  norm_cast; exact Nat.one_lt_two_pow_iff.trans Nat.pos_iff_ne_zero.symm

theorem ssubOverflow_zero_left {n : Nat} (hn : 0 < n) (x : BitVec n) :
    (0#n).ssubOverflow x = decide (x = BitVec.intMin n) := by
  have := BitVec.le_toInt x; have := BitVec.toInt_lt (x := x)
  rw [Bool.eq_iff_iff]
  simp [BitVec.ssubOverflow, ← BitVec.toInt_inj, BitVec.toInt_intMin_of_pos hn]; omega

@[simp] theorem smtUDiv_one {n : Nat} (x : BitVec n) : x.smtUDiv 1#n = x := by
  rcases n with _ | n
  · exact Subsingleton.elim _ _
  · simp [BitVec.smtUDiv_eq]

@[simp] theorem smtSDiv_one {n : Nat} (x : BitVec n) : x.smtSDiv 1#n = x := by
  rcases n with _ | _ | n
  · exact Subsingleton.elim _ _
  · revert x; decide
  · cases h : x.msb <;> simp [BitVec.smtSDiv_eq, BitVec.smtUDiv_eq, h]

@[simp] theorem WT_bitVec_bv {z m : Int} :
    (Term.mk (.BitVec z) (.TBitVector m)).WT ↔ 0 < m ∧ 0 ≤ z ∧ z < 2 ^ m.toNat := by
  rw [WT_bitVec]
  constructor
  · rintro ⟨k, hk, h, h1, h2⟩
    simp at h
    subst h; simp; omega
  · rintro ⟨h0, h1, h2⟩
    exact ⟨m.toNat, by omega, by simp; omega, h1, h2⟩

@[simp] theorem WT_locLit_loc {z m : Int} :
    (Term.mk (.LocLit z) (.TLoc m)).WT ↔ 0 < m ∧ 0 ≤ z ∧ z < 2 ^ m.toNat := by
  rw [WT_locLit]
  constructor
  · rintro ⟨k, hk, h, h1, h2⟩
    simp at h
    subst h; simp; omega
  · rintro ⟨h0, h1, h2⟩
    exact ⟨m.toNat, by omega, by simp; omega, h1, h2⟩

set_option hygiene false in
/-- Closes a goal `Nonzero v` left by the lifting (`kanon_lift_body`, which provides the
hypothesis `kw` that the spec is well-typed): `v` is the divisor of the spec or a literal
that is not zero. -/
macro "kanon_nonzero" : tactic => `(tactic| first
  | assumption
  | exact Kanon.Lib.nonzero_zext_masked kw ‹_› ‹_›
  | exact Kanon.Lib.nonzero_extract_pow2 ‹_› ‹_› (by omega)
  | exact Kanon.Lib.nonzero_div_mul kw ‹_› ‹_› ‹_›
  | exact Kanon.Lib.nonzero_div_mul' kw ‹_› ‹_› ‹_›
  | exact Kanon.Lib.nonzero_div_div kw ‹_› ‹_› ‹_›
  | (have w1 := kw
     simp only [sem, Term.WT, Op2.WT] at w1
     kanon_split
     refine Kanon.Lib.nonzero_bitVec (by first | assumption | omega) ?_
     simp only [Term.WT]
     exact ⟨_, ‹_›, ‹_›, ‹_›, ‹_›⟩))

/-- `kanon_rule_lift` (Kanon's), with `kanon_nonzero` on the goals of the subsorts it leaves. -/
macro "kanon_rule_lift_side" : tactic => `(tactic| (
  kanon_rule_lift
  all_goals (try kanon_nonzero)))

/-- The typing lemmas of the nodes. -/
macro "kanon_wt_simp_bv" : tactic => `(tactic|
  simp [WT_op2, WT_op1, WT_op3, Op2.WT, Op1.WT, Op3.WT, bv_zero, bv_one,
    mk_masked, mk_bv] at *)

/-- Normalizes the typing facts of the hypotheses: splits them, and substitutes
the types they determine. -/
macro "kanon_facts" : tactic => `(tactic| (
  (try kanon_wt_simp_bv)
  (try kanon_split)
  (try kanon_destruct_tys)
  (try simp only [Term.ty_mk] at *)
  (try subst_vars)
  (try simp only [Ty.TBitVector.injEq, Ty.TLoc.injEq] at *)
  (try subst_vars)
  (try kanon_wt_simp_bv)
  (try kanon_split)
  (try subst_vars)))

open Lean Meta Elab Tactic in
/-- Case splits on the first proposition `p` of a `decide p` or an `if p` of
the goal. -/
elab "kanon_split_decide" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let some e := t.find? (fun e => !e.hasLooseBVars &&
      (e.isAppOfArity ``Decidable.decide 2 || e.isAppOfArity ``ite 5))
    | throwError "kanon_split_decide: no decide"
  let p ← Term.exprToSyntax (if e.isAppOfArity ``ite 5 then e.getArg! 1 else e.getArg! 0)
  evalTactic (← `(tactic| by_cases hp : $p <;> simp only [hp, decide_true, decide_false,
    ↓reduceIte, Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.and_true,
    Bool.and_false, Bool.true_or, Bool.false_or, Bool.or_true, Bool.or_false] at ⊢))

/-- Proves an equality of bit-vectors bit by bit, the indices being linear. -/
macro "kanon_bits" : tactic => `(tactic| (
  ext i hi
  simp [BitVec.getElem_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getElem_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
  repeat' kanon_split_decide
  all_goals first | rfl | (exfalso; omega) | (simp; done) | (congr 1; omega)))

/-- The integers read from literals in range (`to_z false`) are their values.
(By `rw`, since they may occur in the widths of bit-vectors.) -/
macro "kanon_zlits" : tactic => `(tactic| (
  (repeat' rw [emod_two_pow_of_lt (by assumption) (by assumption)] at *)
  (repeat' rw [Int.max_eq_left (by assumption)] at *)))

/-- Writes a power of two of the guards (`Bitvec.is_pow2 z`) as `2 ^ k`. -/
macro "kanon_pow2" : tactic => `(tactic| (
  obtain ⟨_, h⟩ := is_pow2_exists ‹_›
  subst h
  simp only [log2_two_pow] at *))

/-- Proves the typing half of a refinement between raw terms. -/
macro "kanon_wt_bv" : tactic => `(tactic| (
  intro w
  kanon_facts
  kanon_zlits
  (try simp_all [WT_bitVec, WT_mk_masked, emod_two_pow_nonneg, emod_two_pow_lt,
    lit_add_nonneg, lit_add_lt, lit_sub_nonneg, lit_sub_lt, lit_mul_nonneg, lit_mul_lt,
    lit_neg_nonneg, lit_neg_lt, lit_not_nonneg, lit_not_lt, lit_and_nonneg, lit_and_lt,
    lit_or_nonneg, lit_or_lt, lit_xor_nonneg, lit_xor_lt, lit_shl_nonneg, lit_shl_lt,
    lit_lshr_nonneg, lit_lshr_lt, lit_ashr_nonneg, lit_ashr_lt, lit_udiv_nonneg, lit_udiv_lt,
    lit_sdiv_nonneg, lit_sdiv_lt, lit_urem_nonneg, lit_urem_lt, lit_srem_nonneg, lit_srem_lt,
    lit_smod_nonneg, lit_smod_lt, lit_extract_nonneg, lit_extract_lt, lit_sext_nonneg,
    lit_sext_lt, lit_zext_nonneg, lit_zext_lt, lit_concat_nonneg, lit_concat_lt, lit_concat_nonneg', lit_concat_lt'])
  all_goals grind [size_of_ty, WT_bitVec]))

/-! ## The lemmas of Kanon's rule tactics (`KanonCore.Proof`)

The literals and the arithmetic on them (`kanon_lits`), the checked flags and
the types in the guards (`kanon_guards`), and the bodies of the rules
(`kanon_body`). -/

attribute [kanon_lits] den denB BitVec.setWidth_eq Term.ty_mk bv_zero bv_one mk_masked mk_bv
  v_true v_false Bool.of_bool size_of_ty_bitVector Int.toNat_natCast Int.reduceToNat

attribute [kanon_guards] Bitvec.unchecked Bitvec.checked_both Bitvec.checked_signed Bitvec.checked_unsigned Bitvec.checked_meet
  Bitvec.checked_has Bitvec.checked_of_signed Bitvec.is_checked ty_eq Term.ty_mk is_bv_iff

attribute [kanon_body] ty_eq mk_commut_binop Bitvec.signed_to_unsigned_cmp

set_option hygiene false in
/-- The operations and helpers on literals in range, as the operations on the
values of bit-vectors (`Lib/LitOps.lean`, `Lib/Ovf.lean`, ...). -/
macro "kanon_lit_ops" : tactic => `(tactic| (try simp (disch := first | assumption | simp only [Kanon.size_of_ty] | exact Kanon.Lib.lit_lshr_nonneg _ _ | exact Kanon.Lib.ones_nonneg _ | exact Kanon.Lib.ones_lt _ | (refine lt_of_lt_of_eq (Kanon.Lib.lit_lshr_lt _ _) ?_; rw [Int.toNat_natCast]) | exact Kanon.Lib.lit_shl_nonneg _ _ | (refine lt_of_lt_of_eq (Kanon.Lib.lit_shl_lt _ _) ?_; rw [Int.toNat_natCast])) only [
  Kanon.Lib.ofInt_lit_add, Kanon.Lib.ofInt_lit_sub, Kanon.Lib.ofInt_lit_mul, Kanon.Lib.ofInt_lit_neg, Kanon.Lib.ofInt_lit_not, Kanon.Lib.ofInt_lit_and,
  Kanon.Lib.ofInt_lit_or, Kanon.Lib.ofInt_lit_xor, Kanon.Lib.ofInt_lit_shl, Kanon.Lib.ofInt_lit_lshr, Kanon.Lib.ofInt_lit_ashr, Kanon.Lib.ofInt_lit_udiv,
  Kanon.Lib.ofInt_lit_urem, Kanon.Lib.ofInt_lit_sdiv, Kanon.Lib.ofInt_lit_srem, Kanon.Lib.ofInt_lit_smod, Kanon.Lib.ofInt_lit_extract, Kanon.Lib.ofInt_lit_extract_zero, Kanon.Lib.ofInt_emod_two_pow_toNat,
  Kanon.Lib.ofInt_lit_concat, Kanon.Lib.ofInt_lit_concat', Kanon.Lib.ofInt_lit_zext, Kanon.Lib.ofInt_lit_zext', Kanon.Lib.ofInt_lit_sext', Kanon.Lib.ofInt_lit_sext, Kanon.Lib.overflows_add_ofInt, Kanon.Lib.overflows_sub_ofInt,
  Kanon.Lib.overflows_mul_ofInt, Kanon.Lib.add_overflows_ofInt, Kanon.Lib.sub_overflows_ofInt,
  Kanon.Lib.mul_overflows_ofInt, Kanon.Lib.fold_checked_ofInt, Kanon.Lib.is_int_min_ofInt, Kanon.Lib.udivides_ofInt, Kanon.Lib.bv_to_z_ofInt,
  Kanon.Lib.is_min_of_ofInt, Kanon.Lib.is_max_of_ofInt, Kanon.Lib.const_keeps_in_range_ofInt, Kanon.Lib.is_ones_ofInt, Kanon.Lib.bits_in_ofInt,
  Kanon.Lib.disjoint_ofInt, Kanon.Lib.ofInt_ones, Kanon.BitVec.ofInt_emod_two_pow] at *))

/-- The value half of `Refines.den`, reduced to the facts on the values of the
atoms. -/
macro "kanon_sem_core_bv" : tactic => `(tactic| (
  first
    | (intro n w ht ρ x h
       have w' := w
       kanon_facts
       kanon_nat_widths
       kanon_lits
       kanon_lit_ops
       kanon_cases)
    | (intro w ρ x h
       have w' := w
       kanon_facts
       kanon_nat_widths
       kanon_lits
       kanon_lit_ops
       kanon_cases
       all_goals kanon_bool_vars)
  all_goals (try simp_all [Bitvec.unchecked, Bitvec.checked_signed, Bitvec.checked_unsigned, Bitvec.checked_meet])
  all_goals (try (repeat' split at h))
  all_goals (try simp_all [ssubOverflow_zero_left])
  all_goals (try (repeat' apply And.intro))))

/-- The value half of `Refines.den`: splits by the atoms, and closes what
`simp_all` and `grind` can. -/
macro "kanon_sem_bv" : tactic => `(tactic| (
  kanon_sem_core_bv
  all_goals kanon_zlits
  all_goals (first
    | (simp only [BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle, decide_eq_true_eq,
        decide_eq_false_iff_not, Bool.not_eq_true, Bool.not_eq_false] at *; omega)
    | ((try kanon_split); (try subst_vars); (try kanon_pow2); kanon_close_lemmas)
    | (simp_all [kanon_close_simp]; done)
    | (grind [BitVec.neg_eq_not_add]; done)
    | (kanon_ovf; done)
    | (simp_all [BitVec.add_assoc, BitVec.add_comm, BitVec.add_left_comm]; done)
    | ((try kanon_split); subst_vars; kanon_bits; done)
    | skip)))

/-- Proves a fact on the natural values of constants in range. -/
macro "kanon_nat" : tactic => `(tactic| (
  (try simp (disch := assumption) only [emod_two_pow_of_lt, toNat_ofInt_of_lt] at *)
  first | assumption | omega))

/-- The side goals of the `kanon_close_lemma` lemmas. -/
macro_rules | `(tactic| kanon_close_side) => `(tactic| kanon_nat)

/-- The refinements that `kanon_rule_lift` closes: equalities at any type. -/
macro_rules | `(tactic| kanon_rule_close) => `(tactic| first
  | exact Refines.eq_same
  | exact Refines.eq_ite_ite
  | exact Refines.eq_ite_l
  | exact Refines.eq_ite_r
  | exact Refines.eq_lits
  | exact Refines.eq_locLits
  | exact Refines.eq_floats
  | exact Refines.eq_ptrs)

/-- Reduces the refinements to their typing and value halves, on the structural
values of the terms. -/
macro "kanon_rule_apply" : tactic => `(tactic|
  all_goals (try first
    | apply Refines.denB (fun _ => rfl)
    | apply Refines.den
    | apply Refines.denB))

/-- `kanon_rule_lift`, then the reduction of the refinement to its typing and
value halves, on the structural values of the terms. -/
macro "kanon_rule_core" : tactic => `(tactic| (
  kanon_rule_lift_side
  kanon_rule_apply))

/-- Proves the statement of an alternative of a `[@cases]` rule, as far as it
can: lifts the calls of its body to their specs, reduces the refinement to the
values of the atoms, and leaves what `simp_all` and `grind` do not close. -/
macro "kanon_rule_bv" : tactic => `(tactic| (
  kanon_rule_core
  all_goals first
    | (kanon_wt_bv; done)
    | kanon_sem_bv
    | skip))

/-- `kanon_rule_bv`, leaving the value goals after `kanon_sem_core_bv`. -/
macro "kanon_rule_sem" : tactic => `(tactic| (
  kanon_rule_core
  all_goals first
    | (kanon_wt_bv; done)
    | kanon_sem_core_bv))

end Kanon.Lib
