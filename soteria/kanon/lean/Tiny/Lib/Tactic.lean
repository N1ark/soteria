import Tiny.Lifts
import Tiny.Lib.Cases
import Tiny.Lib.Meta

/-!
# Tactics for the rule proofs

- `kanon_rule_lift` takes the guard of an alternative, unfolds its spec, splits
  the conditionals of its body, lifts the calls of the body to their specs
  (`kanon_lift_body`), and closes the refinements that are reflexivity or
  commutativity.
- `kanon_rule` then proves the typing half of the refinement (`kanon_wt`) and
  reduces its value half to the values of the atoms (`kanon_sem`), closing what
  `simp_all` and `omega` can.
-/

namespace Tiny.Lib

open Lean Meta Elab Tactic

/-! ## Lifting the calls to rule functions to their specs

The body of a rule calls rule functions through `O`, which only refine their
specs. `kanon_lift` proves `Refines S body`, where `S` is `body` with every
call `O.f args` replaced by `f.spec args` (it is found by unification, with the
`lift_f` lemmas of `Lifts.lean`), so that the rest of a proof is about raw
terms only. -/

partial def liftGoal : TacticM Unit := do
  let g ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let rhs := ty.getArg! 2
  let lem := match rhs.getAppFn with
    | .const (.str (.str (.str .anonymous "Tiny") "Ops") f) _ =>
        some (Name.mkStr (Name.mkStr (Name.mkStr .anonymous "Tiny") "Lib") ("lift_" ++ f))
    | _ => none
  match lem with
  | some l =>
    if (← getEnv).contains l then
      evalTactic (← `(tactic| apply $(mkIdent l) ‹Ops.Sound _›))
      for g' in ← getGoals do
        unless ← g'.isAssigned do
          setGoals [g']
          liftGoal
      setGoals []
      return
    evalTactic (← `(tactic| exact Refines.refl))
  | none => evalTactic (← `(tactic| exact Refines.refl))

elab "kanon_lift" : tactic => do
  let gs ← getGoals
  let mut rest := []
  for g in gs do
    setGoals [g]
    liftGoal
    rest := rest ++ (← getGoals)
  setGoals rest

/-- Replaces the goal `Refines s body` by `Refines s S`, with the calls of
`body` lifted to their specs in `S`. -/
macro "kanon_lift_body" : tactic => `(tactic| (apply Refines.of_lift; case hl => kanon_lift))

/-! ## The rule tactics -/

/-- The primitives and literals, unfolded. -/
macro "kanon_lits" : tactic => `(tactic| try
  simp only [v_true, v_false, int_z, zero, one, tdiv, trem, ediv, erem, divisible,
    abs_eq_max, Term.ty_mk, ty_eq] at *)

/-- The guards, as propositions. -/
macro "kanon_guards" : tactic => `(tactic|
  simp only [equal, var_equal, divisible, decide_eq_true_eq, Bool.and_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, ty_eq] at *)

/-- The first steps of the proof of an alternative: takes its guard, unfolds
its spec, splits the conditionals of its body, lifts the calls of the body to
their specs, and closes the refinement if it is one of reflexivity or
commutativity. -/
macro "kanon_rule_lift" : tactic => `(tactic| (
  intro O hO
  intros
  (try kanon_guards)
  (try kanon_split)
  (try subst_vars)
  simp only [kanon_spec, ty_eq, mk_commut_binop, of_bool]
  (repeat' split)
  all_goals (try kanon_lift_body)
  all_goals (try simp only [kanon_spec, ty_eq])
  all_goals (try first
    | exact Refines.refl
    | (kanon_comm; done))))

/-- The typing lemmas of the nodes. -/
macro "kanon_wt_simp" : tactic => `(tactic| try
  simp only [WT_binop, WT_unop, WT_ite, WT_bool, WT_int, WT_var, Binop.WT, Unop.WT,
    Term.ty_mk, ty_eq, true_and, and_true] at *)

/-- Proves the typing half of a refinement between raw terms. -/
macro "kanon_wt" : tactic => `(tactic| (
  intro w
  kanon_lits
  kanon_wt_simp
  (try kanon_split)
  (try subst_vars)
  (try simp_all)))

set_option hygiene false in
/-- The value half of a refinement between raw terms, split on the values of
its atoms. -/
macro "kanon_sem_core" : tactic => `(tactic| (
  intro ρ v w w' e
  kanon_lits
  kanon_wt_simp
  (try kanon_split)
  (try subst_vars)
  (try simp only [ev, evBinop, evUnop] at e ⊢)
  kanon_cases
  all_goals (try simp only [intOp_some, intOp_none_l, intOp_none_r, intOp_bool_l, intOp_bool_r,
    divOp_some, divOp_none_l, divOp_none_r, divOp_bool_l, divOp_bool_r, eqOp_some, eqOp_none_l,
    eqOp_none_r, evUnop_bool, evUnop_none, evUnop_int, intOp_ite_l, intOp_ite_r, divOp_ite_l,
    divOp_ite_r, eqOp_ite_l, eqOp_ite_r, pand_ite_l, pand_ite_r, por_ite_l, por_ite_r,
    evUnop_ite] at e ⊢)
  all_goals (try simp only [pand, por, Val.ty, Option.some.injEq, Val.bool.injEq,
    Val.int.injEq, reduceCtorEq, false_and, and_false, ite_true, ite_false, Bool.not_true,
    Bool.not_false, Option.ite_none_left_eq_some, Option.ite_none_right_eq_some] at e ⊢)
  all_goals (try subst e)
  all_goals (try (kanon_split; subst_vars))))

/-- Closes a goal on integers and booleans. -/
macro "kanon_close" : tactic => `(tactic| first
  | (simp_all; done)
  | (simp_all; omega)
  | omega)

set_option hygiene false in
/-- The value half: `kanon_sem_core`, then `simp_all` and `omega`, splitting the
conditionals if need be. -/
macro "kanon_sem" : tactic => `(tactic| (
  kanon_sem_core
  all_goals first
    | kanon_close
    | ((repeat' split at e) <;> (repeat' split) <;> kanon_close)
    | skip))

/-- Proves the statement of an alternative, as far as it can. -/
macro "kanon_rule" : tactic => `(tactic| (
  kanon_rule_lift
  all_goals (
    refine Refines.intro ?_ ?_
    · kanon_wt
    · kanon_sem)))

end Tiny.Lib
