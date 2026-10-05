import BitvecMod.Lib.Den
import BitvecMod.Lib.LitOps

/-!
# The rule tactics of the bitvec module

The arms of the rules are proved over the interface, by the structural values
of the terms (`Refines.den`, `Refines.denB`), as the closed proofs of a
language would be (Kanon's rule tactics, `KanonCore.Proof`), with the lemmas of
the module given by the simp sets of `Lib/Attr.lean`:

- `bv_facts` normalizes the typing facts of the hypotheses (`bv_wt`: the typing
  of the nodes, the facts on sorts), splits them and substitutes the sorts they
  determine, then the widths of bit-vector sorts are made natural numbers
  (`bv_nat_widths`);
- `bv_wt` proves the typing half of a refinement;
- `bv_sem_core` reduces the value half (on `Sem.den`, `Sem.denB`) to the values
  of the atoms (`den_cases`, `denB_cases`), with the equations of the nodes
  (`bv_den`) and of the primitives (`bv_lits`), and the operations on literals
  as those on bit-vectors (`bv_ofInt`); `bv_sem` closes what `simp_all` and
  `omega` can;
- `bv_rule` proves an arm: `kanon_rule_lift` (Kanon's), then the reduction to
  the structural values, then `bv_wt` and `bv_sem`. It is the tactic of the
  rule functions of the module (`Lib/Rule.lean`).
-/

namespace BitvecMod

open Classical Kanon Kanon.Sem

set_option linter.unusedSectionVars false

namespace Lib

variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
  {LBool : KanonBool.Syntax B} {LCore : CoreMod.Syntax B} {L : Syntax B LBool LCore}
  [KanonBool.Sem LBool] [CoreMod.Sem LCore] [Sem L]

/-! ## The atoms -/

theorem den_cases {ρ : S.Env} {n : Nat} {t : S.Term} :
    Sem.den L ρ n t = none ∨ ∃ x, Sem.den L ρ n t = some x := Option.eq_none_or_eq_some _
theorem denB_cases {ρ : S.Env} {t : S.Term} :
    Sem.denB L ρ t = none ∨ ∃ b, Sem.denB L ρ t = some b := Option.eq_none_or_eq_some _

/-! ## The simp sets -/

attribute [bv_wt] Kanon.Base.ty_node KanonBool.Syntax.WT_Bool KanonBool.Syntax.WT_Not
  KanonBool.Syntax.WT_And KanonBool.Syntax.WT_Or KanonBool.Syntax.WT_Eq KanonBool.Syntax.WT_Ite
  Syntax.WT_BitVec Syntax.WT_LocLit Syntax.WT_Add Syntax.WT_Sub Syntax.WT_Mul Syntax.WT_Div
  Syntax.WT_Rem Syntax.WT_Mod Syntax.WT_BitAnd Syntax.WT_BitOr Syntax.WT_BitXor Syntax.WT_Shl
  Syntax.WT_LShr Syntax.WT_AShr Syntax.WT_Neg Syntax.WT_BvNot Syntax.WT_Lt Syntax.WT_Leq
  Syntax.WT_AddOvf Syntax.WT_SubOvf Syntax.WT_MulOvf Syntax.WT_BvOfBool Syntax.WT_BvExtract
  Syntax.WT_BvExtend Syntax.WT_BvConcat Sem.bv_wf_BitVec Sem.bv_wf_LocLit TBitVector_inj_iff
  TLoc_inj_iff TBitVector_ne_TBool TBool_ne_TBitVector TBitVector_ne_TLoc TLoc_ne_TBitVector

attribute [bv_lits] Kanon.Base.ty_node Syntax.bitvec_size_eq Sem.size_of_ty_TBitVector
  Sem.size_of_ty_TLoc Sem.mk_masked_eq Sem.mk_bv_eq Sem.bv_zero_eq Sem.bv_one_eq Sem.lit_add_eq
  Sem.lit_sub_eq Sem.lit_mul_eq Sem.lit_neg_eq Sem.lit_udiv_eq Sem.lit_sdiv_eq Sem.lit_and_eq
  Sem.lit_or_eq Sem.lit_xor_eq Sem.lit_not_eq Sem.lit_shl_eq Sem.lit_lshr_eq Sem.lit_ashr_eq
  Sem.lit_urem_eq Sem.lit_srem_eq Sem.lit_smod_eq Sem.lit_extract_eq Sem.lit_zext_eq
  Sem.lit_sext_eq Sem.lit_concat_eq Sem.signed_extract_eq Sem.popcount_eq Sem.log2_eq
  Sem.tdiv_eq Sem.trem_eq Sem.divisible_eq Sem.z_land_eq Sem.z_lsl_eq Syntax.asTBitVector_sort
  Syntax.asTLoc_sort Int.toNat_natCast

-- the helpers of the guards that are not recursive, and the sorts
attribute [kanon_guards] Syntax.bitvec_unchecked_eq Syntax.bitvec_checked_both_eq
  Syntax.bitvec_checked_signed_eq Syntax.bitvec_checked_unsigned_eq
  Syntax.bitvec_checked_of_signed_eq Syntax.bitvec_checked_has_eq Syntax.bitvec_is_checked_eq
  Syntax.bitvec_checked_meet_eq Kanon.Base.ty_node

end Lib

/-! ## Meta-level tactics -/

namespace Lib

open Lean Meta Elab Tactic

/-- Replaces the integer variables `w` with a hypothesis `0 < w` (the widths of
bit-vector sorts) by natural numbers. -/
partial def natWidths (g : MVarId) : MetaM MVarId := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOfArity ``LT.lt 4 && (ty.getArg! 3).isFVar do continue
    unless ← isDefEq (ty.getArg! 0) (mkConst ``Int) do continue
    unless ← isDefEq (ty.getArg! 2) (toExpr (0 : Int)) do continue
    let pf ← mkAppM ``Int.eq_ofNat_of_zero_le #[← mkAppM ``Int.le_of_lt #[d.toExpr]]
    let (h, g) ← (← g.assert `hw (← inferType pf) pf).intro1P
    let [sg] := (← g.cases h).toList | return g
    let heq := sg.fields[1]!.fvarId!
    let some sg' ← observing? (subst sg.mvarId heq) | return sg.mvarId
    return ← natWidths sg'
  return g

elab "bv_nat_widths" : tactic => liftMetaTactic fun g => return [← natWidths g]

/-- The hypotheses `S.ty x = e` (or `e = S.ty x`) on a term variable `x`. -/
def tyHyps (g : MVarId) : MetaM (Array FVarId) := g.withContext do
  let isTyVar (e : Expr) : Bool :=
    e.isAppOfArity ``Kanon.Sem.ty 2 && e.appArg!.isFVar
  let mut out := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let some (_, a, b) := ty.eq? then
      if (isTyVar a && !b.containsFVar a.appArg!.fvarId!) ||
          (isTyVar b && !a.containsFVar b.appArg!.fvarId!) then
        out := out.push d.fvarId
  return out

/-- Rewrites, in the other hypotheses and the goal, the sorts of the term
variables that a hypothesis gives (`S.ty x = e`), so that the matches on them
reduce; the hypothesis is kept. -/
elab "bv_rw_tys" : tactic => do
  for h in ← tyHyps (← getMainGoal) do
    withMainContext do
    let some d := (← getLCtx).find? h | return
    let some (_, a, _) := (← instantiateMVars d.type).eq? | return
    let hs ← Term.exprToSyntax d.toExpr
    let stx ← if a.isAppOfArity ``Kanon.Sem.ty 2 then `(tactic| simp only [$hs:term])
      else `(tactic| simp only [← $hs:term])
    let { ctx, simprocs, dischargeWrapper, .. } ← mkSimpContext stx (eraseLocal := false)
    let others := (← (← getMainGoal).getNondepPropHyps).filter (· != h)
    try
      dischargeWrapper.with fun dis? => do
        let (r, _) ← simpGoal (← getMainGoal) ctx simprocs dis? true others
        replaceMainGoal (match r with | none => [] | some (_, g) => [g])
    catch _ => pure ()

open Lean Meta Elab Tactic in
/-- Splits the goal on the boolean variables of the context. -/
partial def boolVars (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if (← instantiateMVars d.type).isConstOf ``Bool && d.isLet == false then
      let gs ← g.cases d.fvarId
      return ← gs.toList.foldlM (init := []) fun acc sg => return acc ++ (← boolVars sg.mvarId)
  return [g]

open Lean Elab Tactic in
elab "bv_bool_vars" : tactic => liftMetaTactic boolVars


end Lib

/-- Normalizes the typing facts of the hypotheses: rewrites the typing of the
nodes, splits them, and substitutes the sorts they determine. -/
macro "bv_facts" : tactic => `(tactic| (
  (try simp only [bv_wt, bv_lits, true_and, and_true] at *)
  (try kanon_split)
  (try subst_vars)
  (try bv_rw_tys)
  (try simp only [bv_wt, bv_lits, true_and, and_true] at *)
  (try kanon_split)
  (try subst_vars)))

/-- Proves the typing half of a refinement between terms. -/
macro "bv_wt" : tactic => `(tactic| (
  intro w
  bv_facts
  (try bv_nat_widths)
  (try simp_all [bv_range])
  all_goals first | done | grind))

/-- The operations on literals as those on bit-vectors (`bv_ofInt`). -/
macro "bv_lit_ops" : tactic => `(tactic| try simp only [bv_ofInt] at *)

set_option hygiene false in
/-- The value half of `Refines.den` (or `Refines.denB`), reduced to the facts on
the values of the atoms; its hypothesis is `e`. -/
macro "bv_sem_core" : tactic => `(tactic| (
  first
    | intro n w ht ρ x e
    | intro w ρ x e
  bv_facts
  (try bv_nat_widths)
  (try simp only [bv_den, bv_lits] at e ⊢)
  bv_lit_ops
  run_tac Kanon.Proof.caseAllAtoms (some #[``BitvecMod.Lib.den_cases, ``BitvecMod.Lib.denB_cases])
  all_goals (try bv_bool_vars)
  all_goals (try simp only [Option.map_some, Option.map_none, Option.some.injEq,
    reduceCtorEq, BitvecMod.ckOp_some, BitvecMod.binOp_some, BitvecMod.negOp_some] at e ⊢)
  all_goals (try subst e)))

/-- The value half: `bv_sem_core`, then what `simp_all` and `omega` close. -/
macro "bv_sem" : tactic => `(tactic| (
  bv_sem_core
  all_goals first
    | done
    | (simp_all; done)
    | omega
    | skip))

namespace Lib

open Lean Meta Elab Tactic in
/-- The interface of the bitvec module in the context. -/
def findSyntax : TacticM Expr := withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if (← whnfR (← instantiateMVars d.type)).isAppOf ``BitvecMod.Syntax then return d.toExpr
  throwError "no interface of the bitvec module in the context"

open Lean Meta Elab Tactic in
/-- Applies `Refines.denB` (to a boolean refinement) or `Refines.den`, for the
interface of the bitvec module of the context. -/
elab "bv_apply_den" : tactic => withMainContext do
  let l ← Term.exprToSyntax (← findSyntax)
  evalTactic (← `(tactic| first
    | (refine BitvecMod.Lib.Refines.denB (L := $l) ?_ ?_ ?_
       · intro w; bv_facts; all_goals first | rfl | (simp_all; done))
    | (refine BitvecMod.Lib.Refines.den (L := $l) ?_ ?_ ?_
       · intro w; bv_facts; all_goals exact ⟨_, rfl⟩)))

end Lib

/-- Reduces the refinements between terms to their typing and value halves, on
the structural values of the terms. -/
macro "bv_rule_apply" : tactic => `(tactic|
  all_goals kanon_on_refines bv_apply_den)

/-- Proves an arm of the module, as far as it can. -/
macro "bv_rule" : tactic => `(tactic| (
  kanon_rule_lift
  bv_rule_apply
  all_goals first
    | (bv_wt; done)
    | bv_sem
    | skip))

end BitvecMod
