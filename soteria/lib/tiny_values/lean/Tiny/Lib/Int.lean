import Tiny.Lifts
import Tiny.Lib.Cases

/-!
# Lemmas and tactics for the integer rules

`kanon_arith` closes goals of linear integer arithmetic that also involve
truncated division (`Int.tdiv`, `Int.tmod`), Euclidean remainders (`%`) and
products of two variables, by adding to the context the facts that relate them
(`tdiv_facts`, `emod_facts`, `mul_split`), and calling `omega`, which treats
them as atoms.
-/

namespace Tiny.Lib

open Lean Meta Elab Tactic

/-- The truncated division `b.tdiv a` and remainder `b.tmod a`: the remainder
has the sign of `b` and is smaller than `a` in absolute value. -/
theorem tdiv_facts (a b : Int) :
    b = a * b.tdiv a + b.tmod a ∧ (0 ≤ b → 0 ≤ b.tmod a) ∧ (b ≤ 0 → b.tmod a ≤ 0) ∧
      (0 < a → b.tmod a < a ∧ -a < b.tmod a) ∧ (a < 0 → b.tmod a < -a ∧ a < b.tmod a) := by
  refine ⟨(Int.mul_tdiv_add_tmod b a).symm, Int.tmod_nonneg a, fun h => ?_,
    fun h => ⟨Int.tmod_lt_of_pos b h, Int.lt_tmod_of_pos b h⟩, fun h => ?_⟩
  · have := Int.tmod_nonneg a (a := -b) (by omega)
    rw [Int.neg_tmod] at this; omega
  · have h1 := Int.tmod_lt_of_pos b (b := -a) (by omega)
    have h2 := Int.lt_tmod_of_pos b (b := -a) (by omega)
    rw [Int.tmod_neg] at h1 h2
    omega

/-- The Euclidean remainder `x % y`, for a non-zero `y`: `0 ≤ x % y < |y|`. -/
theorem emod_facts (x y : Int) :
    y ≠ 0 → 0 ≤ x % y ∧ (0 < y → x % y < y) ∧ (y < 0 → x % y < -y) := by
  intro h
  refine ⟨Int.emod_nonneg x h, fun hy => Int.emod_lt_of_pos x hy, fun hy => ?_⟩
  have := Int.emod_lt x h
  omega

/-- Splitting `a * w` around `a * q`: `a * (w - q)` is `0` or at least `|a|`
in absolute value. -/
theorem mul_split (a w q : Int) :
    a * w = a * q + a * (w - q) ∧
      (0 < a → 1 ≤ w - q → a ≤ a * (w - q)) ∧ (0 < a → w - q ≤ -1 → a * (w - q) ≤ -a) ∧
      (a < 0 → 1 ≤ w - q → a * (w - q) ≤ a) ∧ (a < 0 → w - q ≤ -1 → -a ≤ a * (w - q)) ∧
      (w - q = 0 → a * (w - q) = 0) := by
  refine ⟨by rw [Int.mul_sub]; omega, fun ha hk => ?_, fun ha hk => ?_, fun ha hk => ?_,
    fun ha hk => ?_, fun hk => by rw [hk, Int.mul_zero]⟩
  · have := Int.mul_le_mul_of_nonneg_left hk (Int.le_of_lt ha); omega
  · have := Int.mul_le_mul_of_nonneg_left hk (Int.le_of_lt ha)
    rw [Int.mul_neg, Int.mul_one] at this; omega
  · have := Int.mul_le_mul_of_nonneg_left hk (show (0 : Int) ≤ -a by omega)
    rw [Int.neg_mul, Int.neg_mul, Int.mul_one] at this; omega
  · have := Int.mul_le_mul_of_nonneg_left hk (show (0 : Int) ≤ -a by omega)
    rw [Int.neg_mul, Int.neg_mul, Int.mul_neg, Int.mul_one, Int.neg_neg] at this; omega

/-- Z3's `rem`, from the Euclidean remainder. -/
theorem zrem_facts (x y : Int) : (0 ≤ y → zrem x y = x % y) ∧ (y < 0 → zrem x y = -(x % y)) := by
  unfold zrem; constructor <;> intro h <;> split <;> first | rfl | omega

private partial def subterms (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc := acc.push e
  match e with
  | .app f a => subterms a (subterms f acc)
  | .mdata _ b => subterms b acc
  | _ => acc

private def isIntOp (n : Name) (e : Expr) : Bool :=
  e.isAppOfArity n 6 && (e.getArg! 0).isConstOf ``Int

/-- Adds the facts on the divisions, remainders and products of the goal and
hypotheses. -/
def arithFacts : TacticM Unit := withMainContext do
  let mut exprs := #[← instantiateMVars (← getMainTarget)]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then exprs := exprs.push (← instantiateMVars d.type)
  let mut subs : Array Expr := #[]
  for e in exprs do
    for s in subterms e #[] do
      if !s.hasLooseBVars && !subs.contains s then subs := subs.push s
  let tdivs := (subs.filter fun s => s.isAppOfArity ``Int.tdiv 2 || s.isAppOfArity ``Int.tmod 2).map
    fun s => mkApp2 (mkConst ``Int.tdiv) (s.getArg! 0) (s.getArg! 1)
  let tdivs := tdivs.foldl (init := #[]) fun acc t => if acc.contains t then acc else acc.push t
  let emods := subs.filter (isIntOp ``HMod.hMod)
  let muls := subs.filter (isIntOp ``HMul.hMul)
  let mut facts : Array Expr := #[]
  for t in tdivs do
    let b := t.getArg! 0
    let a := t.getArg! 1
    facts := facts.push (← mkAppM ``tdiv_facts #[a, b])
    for m in muls do
      let x := m.getArg! 4
      let y := m.getArg! 5
      if x == a then facts := facts.push (← mkAppM ``mul_split #[a, y, t])
      if y == a then
        facts := facts.push (← mkAppM ``mul_split #[a, x, t])
        facts := facts.push (← mkAppM ``Int.mul_comm #[x, a])
  for m in emods do
    facts := facts.push (← mkAppM ``emod_facts #[m.getArg! 4, m.getArg! 5])
  for m in subs.filter (·.isAppOfArity ``Tiny.zrem 2) do
    facts := facts.push (← mkAppM ``zrem_facts #[m.getArg! 0, m.getArg! 1])
    facts := facts.push (← mkAppM ``emod_facts #[m.getArg! 0, m.getArg! 1])
  let g ← getMainGoal
  let mut g := g
  for f in facts do
    let (_, g') ← (← g.assert `kanon_fact (← inferType f) f).intro1P
    g := g'
  replaceMainGoal [g]

elab "kanon_arith_facts" : tactic => arithFacts

/-- Closes a goal of integer arithmetic with divisions and products. -/
macro "kanon_arith" : tactic => `(tactic| (
  (try simp only [Val.bool.injEq, Val.int.injEq, decide_eq_decide, ← decide_not,
    Int.dvd_iff_tmod_eq_zero, ge_iff_le, gt_iff_lt, Bool.false_eq, Bool.true_eq,
    decide_eq_false_iff_not, decide_eq_true_eq] at *)
  kanon_arith_facts
  omega))

/-! ## Multiples and remainders -/

/-- `is_mod v n`: `v` is a multiple of `n`. -/
theorem is_mod_sound {ρ : Env} {n : Int} (hn : n ≠ 0) :
    ∀ {v : Term} {z : Int}, is_mod v n = true → ev ρ v = some (.int z) → n ∣ z
  | .mk (.Var _) _, _, h, _ => by unfold is_mod at h; simp [Kanon.firstSome] at h
  | .mk (.Bool _) _, _, h, _ => by unfold is_mod at h; simp [Kanon.firstSome] at h
  | .mk (.Int i) _, z, h, e => by
      unfold is_mod at h; simp [Kanon.firstSome, trem] at h
      simp only [ev, Option.some.injEq, Val.int.injEq] at e; subst e
      exact Int.dvd_iff_tmod_eq_zero.2 (of_decide_eq_true h)
  | .mk (.Unop _ _) _, _, h, _ => by unfold is_mod at h; simp [Kanon.firstSome] at h
  | .mk (.Binop op a b) _, z, h, e => by
      unfold is_mod at h
      cases op <;> simp [Kanon.firstSome] at h
      all_goals simp only [ev, evBinop] at e; obtain ⟨x, y, ha, hb, hz⟩ := intOp_eq_some.1 e
      all_goals simp only [Val.int.injEq] at hz; subst hz
      · exact Int.dvd_add (is_mod_sound hn h.1 ha) (is_mod_sound hn h.2 hb)
      · exact Int.dvd_sub (is_mod_sound hn h.1 ha) (is_mod_sound hn h.2 hb)
      · rcases h with h | h
        · exact Int.dvd_trans (is_mod_sound hn h ha) (Int.dvd_mul_right _ _)
        · exact Int.dvd_trans (is_mod_sound hn h hb) (Int.dvd_mul_left _ _)
  | .mk (.Nop _ _) _, _, h, _ => by unfold is_mod at h; simp [Kanon.firstSome] at h
  | .mk (.Ite _ _ _) _, _, h, _ => by unfold is_mod at h; simp [Kanon.firstSome] at h

theorem zrem_mul_pos {x y n : Int} (h : 0 < n) : zrem (x * n) (y * n) = n * zrem x y := by
  have e : x * n % (y * n) = n * (x % y) := by
    rw [Int.mul_comm x, Int.mul_comm y]; exact Int.mul_emod_mul_of_pos x y h
  unfold zrem
  rw [e]
  by_cases hy : 0 ≤ y
  · have : 0 ≤ y * n := Int.mul_nonneg hy (Int.le_of_lt h)
    simp [hy, this]
  · have : ¬ 0 ≤ y * n := fun h' => hy (Int.nonneg_of_mul_nonneg_left h' h)
    simp [hy, this, Int.mul_neg]

theorem add_emod_emod_of_dvd {x y a b : Int} (h : b ∣ a) : (x + y % a) % b = (x + y) % b := by
  rw [Int.add_emod, Int.emod_emod_of_dvd _ h, ← Int.add_emod]

set_option hygiene false in
/-- `kanon_rule`, closing the value goals with `kanon_arith`. -/
macro "kanon_rule_arith" : tactic => `(tactic| (
  kanon_rule_lift
  all_goals (
    refine Kanon.Sem.Refines.intro ?_ ?_
    · kanon_wt
    · kanon_sem_core
      all_goals first
        | kanon_close
        | kanon_arith
        | ((repeat' split at e) <;> (repeat' split) <;> first | kanon_close | kanon_arith))))

end Tiny.Lib
