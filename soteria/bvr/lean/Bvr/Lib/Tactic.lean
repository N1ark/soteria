import Bvr.Lib.Meta
import Bvr.Lifts
import Bvr.Lib.Lit
import Bvr.Lib.Ovf

/-!
# Tactics for the rule proofs

- `bvr_rule` proves the statement of an alternative of a `[@cases]` rule: it
  lifts the calls of the body to their specs (`bvr_lift_body`), proves the
  typing half (`bvr_wt`), and reduces the value half to the values of the atoms
  (`bvr_sem`), closing what `simp_all`, `grind` and `bvr_ovf` can.
- `bvr_rule_sem` does the same, but leaves the value goals as `bvr_sem_core`
  leaves them, for the alternatives that need a lemma of their own.
- `bvr_nat` proves facts on the natural values of constants in range.
-/

namespace Bvr.Lib

open Lean Meta Elab Tactic

@[simp] theorem two_pow_pos_int (n : Nat) : (0 : Int) < 2 ^ n := two_pow_pos' n

@[simp] theorem one_lt_two_pow_int {k : Nat} : (1 : Int) < 2 ^ k ↔ 0 < k := by
  constructor
  · intro h; rcases k with _ | k
    · simp at h
    · omega
  · intro h
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have := two_pow_pos' k
    rw [Int.pow_succ]; omega

theorem ssubOverflow_zero_left {n : Nat} (hn : 0 < n) (x : BitVec n) :
    (0#n).ssubOverflow x = decide (x = BitVec.intMin n) := by
  have h1 := BitVec.toInt_lt (x := x); have h2 := BitVec.le_toInt (x := x)
  simp only [BitVec.ssubOverflow, BitVec.toInt_zero, Int.zero_sub]
  by_cases h : x = BitVec.intMin n
  · subst h; simp [BitVec.toInt_intMin, hn]
  · have : x.toInt ≠ -2 ^ (n - 1) := by
      intro e; apply h; apply BitVec.eq_of_toInt_eq; rw [e, BitVec.toInt_intMin]; simp [hn]
    simp [h]; omega

@[simp] theorem smtUDiv_one {n : Nat} (x : BitVec n) : x.smtUDiv 1#n = x := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  · rw [BitVec.smtUDiv_eq, ite_eq_right_iff.mpr (fun h => absurd h ?_), BitVec.udiv_one]
    intro h; have := congrArg BitVec.toNat h
    simp at this; omega

@[simp] theorem smtSDiv_one {n : Nat} (x : BitVec n) : x.smtSDiv 1#n = x := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  · simp only [BitVec.smtSDiv, BitVec.msb_one]
    by_cases h1 : n = 1
    · subst h1; revert x; decide
    · simp only [h1, decide_false]
      split <;> simp_all [BitVec.neg_neg]

@[simp] theorem WT_bitVec_bv {z m : Int} :
    (Term.mk (.bitVec z) (.bitVector m)).WT ↔ 0 < m ∧ 0 ≤ z ∧ z < 2 ^ m.toNat := by
  rw [WT_bitVec]
  constructor
  · rintro ⟨k, hk, h, h1, h2⟩
    rcases h with h | h <;> simp at h
    subst h; simp; omega
  · rintro ⟨h0, h1, h2⟩
    exact ⟨m.toNat, by omega, .inl (by simp; omega), h1, h2⟩

/-- The typing lemmas of the nodes. -/
macro "bvr_wt_simp" : tactic => `(tactic|
  simp [WT_binop, WT_unop, WT_triop, Binop.WT, Unop.WT, Triop.WT, bv_zero, bv_one,
    mk_masked, mk_bv] at *)

/-- Normalizes the typing facts of the hypotheses: splits them, and substitutes
the types they determine. -/
macro "bvr_facts" : tactic => `(tactic| (
  (try bvr_wt_simp)
  (try bvr_split)
  (try bvr_destruct_tys)
  (try simp only [Term.ty_mk] at *)
  (try subst_vars)
  (try simp only [Ty.bitVector.injEq, Ty.loc.injEq] at *)
  (try subst_vars)
  (try bvr_wt_simp)
  (try bvr_split)
  (try subst_vars)))

/-- Proves the typing half of a refinement between raw terms. -/
macro "bvr_wt" : tactic => `(tactic| (
  intro w
  bvr_facts
  (try simp_all [WT_bitVec])
  all_goals grind [size_of_ty, WT_bitVec]))

/-- Unfolds the literals and the arithmetic on them. -/
macro "bvr_lits" : tactic => `(tactic|
  simp only [den, denB, den_lit, ty_lit, bv_of_lit_bv, bv_of_lit_bv', of_z_nat, lit_add_mk, lit_sub_mk, lit_mul_mk,
    lit_neg_mk, lit_udiv_mk, lit_sdiv_mk, lit_and_mk, lit_or_mk, lit_xor_mk, lit_not_mk,
    lit_shl_mk, lit_lshr_mk, lit_ashr_mk, lit_urem_mk, lit_srem_mk, lit_smod_mk, lit_extract_mk,
    lit_zext_mk, lit_sext_mk, lit_concat_mk, bv_equal_mk, at_mk, at_mk', BitVec.setWidth_eq, at_of_z_self, width_mk, Term.ty_mk, to_z_mk, bv_zero, bv_one, mk_masked,
    mk_bv, v_true, v_false, of_bool, size_of_ty_bitVector, Int.toNat_natCast, Int.reduceToNat] at *)

/-- The checked flags, and the booleans of the guards. -/
macro "bvr_flags" : tactic => `(tactic|
  simp only [unchecked, checked_both, checked_signed, checked_unsigned, checked_meet,
    checked_has, checked_of_signed, is_checked, decide_eq_true_eq, Bool.and_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', equal] at *)

/-- The value half of `Refines.den`, reduced to the facts on the values of the
atoms. -/
macro "bvr_sem_core" : tactic => `(tactic| (
  first
    | (intro n w ht ρ x h
       have w' := w
       bvr_facts
       bvr_lits
       bvr_cases)
    | (intro w ρ x h
       have w' := w
       bvr_facts
       bvr_lits
       bvr_cases
       all_goals bvr_bool_vars)
  all_goals (try simp_all [unchecked, checked_signed, checked_unsigned, checked_meet])
  all_goals (try (repeat' split at h))
  all_goals (try simp_all [ssubOverflow_zero_left])
  all_goals (try simp only [fold_checked_mk (by assumption), add_overflows_mk (hn := by assumption),
    sub_overflows_mk (hn := by assumption), mul_overflows_mk (hn := by assumption),
    is_int_min_mk (hn := by assumption)] at *)
  all_goals (try (repeat' apply And.intro))))

/-- The value half of `Refines.den`: splits by the atoms, and closes what
`simp_all` and `grind` can. -/
macro "bvr_sem" : tactic => `(tactic| (
  bvr_sem_core
  all_goals (first
    | (simp only [BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle, decide_eq_true_eq,
        decide_eq_false_iff_not, Bool.not_eq_true, Bool.not_eq_false] at *; omega)
    | (grind [BitVec.neg_eq_not_add]; done)
    | (bvr_ovf; done)
    | skip)))

/-- Proves `Refines FS ?S body`, where `?S` is `body` with every call
`O.f args` replaced by `f.spec args` (by the `lift_f` lemmas). -/
partial def liftGoal : TacticM Unit := do
  let g ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let rhs := ty.getArg! 2
  let fn := rhs.getAppFn
  let lem := match fn with
    | .const n _ =>
        match n with
        | .str (.str (.str .anonymous "Bvr") "Ops") f => some (Name.mkStr (Name.mkStr (Name.mkStr .anonymous "Bvr") "Lib") ("lift_" ++ f))
        | _ => none
    | _ => none
  match lem with
  | some l =>
    if (← getEnv).contains l then
      evalTactic (← `(tactic| apply $(mkIdent l) ‹Ops.Sound _ _›))
      let gs ← getGoals
      for g' in gs do
        unless ← g'.isAssigned do
          setGoals [g']
          liftGoal
      setGoals []
      return
    evalTactic (← `(tactic| exact Refines.refl))
  | none => evalTactic (← `(tactic| exact Refines.refl))

elab "bvr_lift" : tactic => do
  let gs ← getGoals
  let mut rest := []
  for g in gs do
    setGoals [g]
    liftGoal
    rest := rest ++ (← getGoals)
  setGoals rest

/-- Replaces the goal `Refines FS s body` by `Refines FS s S`, with the calls of
`body` lifted to their specs in `S`. -/
macro "bvr_lift_body" : tactic => `(tactic| (apply Refines.of_lift; case hl => bvr_lift))

/-- Proves a fact on the natural values of constants in range. -/
macro "bvr_nat" : tactic => `(tactic| (
  (try simp (disch := assumption) only [emod_two_pow_of_lt, toNat_ofInt_of_lt] at *)
  first | assumption | omega))

/-- Proves the statement of an alternative of a `[@cases]` rule, as far as it
can: lifts the calls of its body to their specs, reduces the refinement to the
values of the atoms, and leaves what `simp_all` and `grind` do not close. -/
macro "bvr_rule_core" : tactic => `(tactic| (
  intro FS O hO
  intros
  (try bvr_flags)
  (try subst_vars)
  simp only [bvr_spec, ty, mk_commut_binop]
  (try split)
  all_goals (try bvr_lift_body)
  all_goals (try simp only [bvr_spec, ty])
  all_goals (try (first | exact Refines.refl | (bvr_comm; done)))
  all_goals (try first
    | apply Refines.denB (fun _ => rfl)
    | apply Refines.den
    | apply Refines.denB)))

macro "bvr_rule" : tactic => `(tactic| (
  bvr_rule_core
  all_goals first
    | (bvr_wt; done)
    | bvr_sem
    | skip))

/-- `bvr_rule`, leaving the value goals after `bvr_sem_core`. -/
macro "bvr_rule_sem" : tactic => `(tactic| (
  bvr_rule_core
  all_goals first
    | (bvr_wt; done)
    | bvr_sem_core))

end Bvr.Lib
