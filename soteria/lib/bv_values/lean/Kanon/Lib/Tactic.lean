import Kanon.Lib.Meta
import Kanon.Lifts
import Kanon.Lib.Lit
import Kanon.Lib.Ovf
import Kanon.Lib.Float

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
    rcases h with h | h <;> simp at h
    subst h; simp; omega
  · rintro ⟨h0, h1, h2⟩
    exact ⟨m.toNat, by omega, .inl (by simp; omega), h1, h2⟩

/-- The typing lemmas of the nodes. -/
macro "kanon_wt_simp_bv" : tactic => `(tactic|
  simp [WT_binop, WT_unop, WT_triop, Binop.WT, Unop.WT, Triop.WT, bv_zero, bv_one,
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

/-- Writes a power of two of the guards (`is_pow2 z`) as `2 ^ k`. -/
macro "kanon_pow2" : tactic => `(tactic| (
  obtain ⟨_, h⟩ := is_pow2_exists ‹_›
  subst h
  simp only [log2_two_pow] at *))

/-- Proves the typing half of a refinement between raw terms. -/
macro "kanon_wt_bv" : tactic => `(tactic| (
  intro w
  kanon_facts
  kanon_zlits
  (try simp_all [WT_bitVec, WT_mk_masked, emod_two_pow_nonneg, emod_two_pow_lt])
  all_goals grind [size_of_ty, WT_bitVec]))

/-! ## The lemmas of Kanon's rule tactics (`KanonCore.Proof`)

The literals and the arithmetic on them (`kanon_lits`), the checked flags and
the types in the guards (`kanon_guards`), and the bodies of the rules
(`kanon_body`). -/

attribute [kanon_lits] den denB den_lit ty_lit bv_of_lit_bv bv_of_lit_bv' of_z_nat lit_add_mk
  lit_sub_mk lit_mul_mk lit_neg_mk lit_udiv_mk lit_sdiv_mk lit_and_mk lit_or_mk lit_xor_mk
  lit_not_mk lit_shl_mk lit_lshr_mk lit_ashr_mk lit_urem_mk lit_srem_mk lit_smod_mk
  lit_extract_mk lit_zext_mk lit_sext_mk lit_concat_mk bv_equal_mk at_mk at_mk'
  BitVec.setWidth_eq at_of_z_self width_mk Term.ty_mk to_z_mk bv_zero bv_one mk_masked mk_bv
  v_true v_false of_bool size_of_ty_bitVector Int.toNat_natCast Int.reduceToNat

attribute [kanon_guards] unchecked checked_both checked_signed checked_unsigned checked_meet
  checked_has checked_of_signed is_checked equal ty_eq Term.ty_mk is_bv_iff

attribute [kanon_body] ty_eq mk_commut_binop signed_to_unsigned_cmp

/-- The value half of `Refines.den`, reduced to the facts on the values of the
atoms. -/
macro "kanon_sem_core_bv" : tactic => `(tactic| (
  first
    | (intro n w ht ρ x h
       have w' := w
       kanon_facts
       kanon_lits
       kanon_cases)
    | (intro w ρ x h
       have w' := w
       kanon_facts
       kanon_lits
       kanon_cases
       all_goals kanon_bool_vars)
  all_goals (try simp_all [unchecked, checked_signed, checked_unsigned, checked_meet])
  all_goals (try (repeat' split at h))
  all_goals (try simp_all [ssubOverflow_zero_left])
  all_goals (try simp only [fold_checked_mk (by assumption), add_overflows_mk (hn := by assumption),
    sub_overflows_mk (hn := by assumption), mul_overflows_mk (hn := by assumption),
    is_int_min_mk (hn := by assumption)] at *)
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
  kanon_rule_lift
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
