import Bvr.Lib.Msb

/-!
# Equality and the overflow checks

Tactics and lemmas for `Proofs/EqCases.lean` (`sem_eq`, `bv_neg`, `bv_mod`, `bv_rem`
and the overflow checks).

- `bvr_rule_b` is `bvr_rule` for boolean specs, and for `sem_eq` at any type: it
  splits all the conditionals of a body, proves the equalities of `ite`s,
  literals, floats and pointers by their evaluation (`Refines.eq_*`), and
  reduces the other value halves to the values of the atoms (`bvr_sem_b_core`),
  with natural widths (`bvr_nat_widths`) and opaque values for the literals
  (`bvr_gen_lits`), which the closing lemmas of `bvr_sem_b` are stated on.
- `bvr_rule_b_arith` first normalizes the integer expressions of the body (e.g.
  the widths of extractions); `bvr_rule_b_sem` leaves the value goals.
-/

namespace Bvr.Lib

open Classical

/-! ## Normalizing the value goals -/

theorem toNat_emod_eq {w : Nat} (z : Int) : (z % 2 ^ w).toNat = (BitVec.ofInt w z).toNat := by
  rw [BitVec.toNat_ofInt]; push_cast; rfl

theorem natCast_toNat_ofInt {w : Nat} (z : Int) :
    max (z % 2 ^ w) 0 = ((BitVec.ofInt w z).toNat : Int) := by
  rw [BitVec.toNat_ofInt]; push_cast; omega

open Lean Meta Elab Tactic in
/-- Generalizes the values `BitVec.ofInt n z` of the literals (`z` a variable) to
opaque bit-vectors. -/
partial def genLits (g : MVarId) : MetaM MVarId := g.withContext do
  let isLitVal (e : Expr) : Bool :=
    e.isAppOfArity ``BitVec.ofInt 2 && e.appArg!.isFVar && !e.hasLooseBVars
  let hyps := (← getLCtx).foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail then acc else acc.push d
  let mut cand : Option Expr := (← instantiateMVars (← g.getType)).find? isLitVal
  for d in hyps do
    if cand.isNone then cand := (← instantiateMVars d.type).find? isLitVal
  match cand with
  | none => return g
  | some a =>
    let (_, _, g) ← g.generalizeHyp #[{ expr := a, xName? := `k }] (hyps.map (·.fvarId))
    genLits g

open Lean Meta Elab Tactic in
/-- Replaces `(↑n : Int).toNat` by `n` everywhere, instances included. -/
def fixWidths (g : MVarId) : MetaM MVarId := g.withContext do
  let fix (e : Expr) : Expr := e.replace fun t =>
    if t.isAppOfArity ``Int.toNat 1 then
      let a := t.appArg!
      if a.isAppOfArity ``Nat.cast 3 then some a.appArg!
      else if a.isAppOfArity ``HAdd.hAdd 6 && (a.getArg! 4).isAppOfArity ``Nat.cast 3 &&
          (a.getArg! 5).isAppOfArity ``Nat.cast 3 then
        some (mkNatAdd (a.getArg! 4).appArg! (a.getArg! 5).appArg!)
      else none
    else none
  let mut g := g
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let ty' := fix ty
    if ty' != ty then g ← g.replaceLocalDeclDefEq d.fvarId ty'
  let t ← instantiateMVars (← g.getType)
  let t' := fix t
  if t' != t then g ← g.replaceTargetDefEq t'
  return g

open Lean Meta Elab Tactic in
elab "bvr_fix_widths" : tactic => liftMetaTactic fun g => return [← fixWidths g]

open Lean Meta Elab Tactic in
/-- Proves a goal on bit-vectors of small literal widths by enumerating them. -/
elab "bvr_decide_small" : tactic => do
  let g ← getMainGoal
  let fvs ← g.withContext do
    let mut small : Array FVarId := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← whnfR (← instantiateMVars d.type)
      if ty.isAppOfArity ``BitVec 1 then
        if let some n := (← instantiateMVars ty.appArg!).nat? then
          if n ≤ 4 then small := small.push d.fvarId
    let mut fvs := small
    for d in (← getLCtx) do
      if d.isImplementationDetail || small.contains d.fvarId then continue
      let ty ← instantiateMVars d.type
      unless ← isProp ty do continue
      let used := (collectFVars {} ty).fvarIds
      if used.all small.contains then fvs := fvs.push d.fvarId
    return fvs
  let (_, g') ← g.revert fvs
  replaceMainGoal [g']
  evalTactic (← `(tactic| decide))

open Lean Meta Elab Tactic in
elab "bvr_gen_lits" : tactic => liftMetaTactic fun g => return [← genLits g]


/-! ## Facts on values, as the value goals state them -/

section
variable {w : Nat} {k x : BitVec w}

theorem sadd_pos (hw : 0 < w) (h : 0 < k.toInt) :
    (BitVec.ofInt w (max_for true w - k.toInt)).slt x = k.saddOverflow x := by
  have := toInt_bounds k; have := toInt_bounds x
  rw [max_for_true hw, BitVec.slt, BitVec.toInt_ofInt_eq_self hw]
  · rw [Bool.eq_iff_iff]; simp [BitVec.saddOverflow]; omega
  all_goals omega

theorem sadd_nonpos (hw : 0 < w) (h : k.toInt ≤ 0) :
    x.slt (BitVec.ofInt w (min_for true w - k.toInt)) = k.saddOverflow x := by
  have := toInt_bounds k; have := toInt_bounds x
  rw [min_for_true hw, BitVec.slt, BitVec.toInt_ofInt_eq_self hw]
  · rw [Bool.eq_iff_iff]; simp [BitVec.saddOverflow]; omega
  all_goals omega

theorem uadd_not : (~~~k).ult x = k.uaddOverflow x := by
  have := k.isLt; have := x.isLt
  simp only [BitVec.uaddOverflow, BitVec.ult, BitVec.toNat_not]
  rw [Bool.eq_iff_iff]; simp; omega

theorem usub_self : x.usubOverflow x = false := by simp [BitVec.usubOverflow]

theorem ssub_self : x.ssubOverflow x = false := by
  have := toInt_bounds x
  simp [BitVec.ssubOverflow]; omega

theorem uadd_zero : (0#w).uaddOverflow x = false := by
  have := x.isLt; simp [BitVec.uaddOverflow]; omega

theorem sadd_zero : (0#w).saddOverflow x = false := by
  have := toInt_bounds x; simp [BitVec.saddOverflow]; omega

theorem sadd_pos' (hw : 0 < w) (h : 0 < k.toInt) :
    (BitVec.ofInt w (max_for true w - k.toInt)).slt x = x.saddOverflow k := by
  rw [sadd_pos hw h, (ovf_comm _ _).1]

theorem sadd_nonpos' (hw : 0 < w) (h : k.toInt ≤ 0) :
    x.slt (BitVec.ofInt w (min_for true w - k.toInt)) = x.saddOverflow k := by
  rw [sadd_nonpos hw h, (ovf_comm _ _).1]

theorem uadd_not' : (~~~k).ult x = x.uaddOverflow k := by
  rw [uadd_not, (ovf_comm _ _).2.1]

theorem uadd_zero' : x.uaddOverflow 0#w = false := by rw [(ovf_comm _ _).2.1, uadd_zero]

theorem sadd_zero' : x.saddOverflow 0#w = false := by rw [(ovf_comm _ _).1, sadd_zero]

theorem one_uadd (hw : 0 < w) : (1#w).uaddOverflow x = decide (x = BitVec.ofInt w (2 ^ w - 1)) := by
  have := x.isLt
  have h1 : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
  have hp : ((2 ^ w : Nat) : Int) = (2 : Int) ^ w := by push_cast; rfl
  have := Nat.one_lt_two_pow (n := w) (by omega)
  have e : x = BitVec.ofInt w (2 ^ w - 1) ↔ x.toNat = 2 ^ w - 1 := by
    rw [← BitVec.toNat_inj, BitVec.toNat_ofInt, hp, Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  rw [Bool.eq_iff_iff]; simp [BitVec.uaddOverflow, e, h1]; omega

theorem one_sadd (hw : (1 : Int) < w) :
    (1#w).saddOverflow x = decide (x = BitVec.ofInt w (max_for true w)) := by
  have := toInt_bounds x
  have e : x = BitVec.ofInt w (max_for true w) ↔ x.toInt = 2 ^ (w - 1) - 1 := by
    rw [← BitVec.toInt_inj, max_for_true (by omega), BitVec.toInt_ofInt_eq_self (by omega)] <;>
      omega
  rw [Bool.eq_iff_iff]; simp [BitVec.saddOverflow, e, BitVec.toInt_one (show 1 < w by omega)]; omega

theorem one_uadd' (hw : 0 < w) : x.uaddOverflow 1#w = decide (x = BitVec.ofInt w (2 ^ w - 1)) := by
  rw [(ovf_comm _ _).2.1, one_uadd hw]

theorem one_sadd' (hw : (1 : Int) < w) :
    x.saddOverflow 1#w = decide (x = BitVec.ofInt w (max_for true w)) := by
  rw [(ovf_comm _ _).1, one_sadd hw]

theorem one_uadd_one (hw : (1 : Int) < w) : (1#w).uaddOverflow 1#w = false := by
  have h4 : 4 ≤ 2 ^ w := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) (show 2 ≤ w by omega); simpa using this
  have h1 : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt (by omega)
  simp [BitVec.uaddOverflow, h1]; omega

theorem one_sadd_one (hw : (1 : Int) < w) (h2 : ¬(w : Int) = 2) : (1#w).saddOverflow 1#w = false := by
  have h4 : 4 ≤ 2 ^ (w - 1) := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) (show 2 ≤ w - 1 by omega); simpa using this
  have : (4 : Int) ≤ 2 ^ (w - 1) := by exact_mod_cast h4
  simp [BitVec.saddOverflow, BitVec.toInt_one (show 1 < w by omega)]; omega


theorem umul_udiv : x.umulOverflow (k.smtUDiv x) = false := by
  rw [umul_ok]
  by_cases hx : x.toNat = 0
  · simp [hx, Nat.two_pow_pos]
  · rw [smtUDiv_toNat hx]
    exact Nat.lt_of_le_of_lt (Nat.mul_div_le _ _) k.isLt


theorem umul_udiv' : (k.smtUDiv x).umulOverflow x = false := by
  rw [(ovf_comm _ _).2.2.2, umul_udiv]


theorem int_mul_pos_ovf {M z y : Int} (hz : 0 < z) :
    (M ≤ z * y ∨ z * y < -M) ↔ (y < -(M / z) ∨ (M - 1) / z < y) := by
  have e1 := Int.ediv_lt_iff_lt_mul (a := M) (b := -y) hz
  have e2 := Int.ediv_lt_iff_lt_mul (a := M - 1) (b := y) hz
  rw [Int.neg_mul, Int.mul_comm y] at e1
  rw [Int.mul_comm y] at e2
  constructor
  · rintro (h | h)
    · exact Or.inr (e2.2 (by omega))
    · exact Or.inl (by have := e1.2 (by omega); omega)
  · rintro (h | h)
    · exact Or.inr (by have := e1.1 (by omega); omega)
    · exact Or.inl (by have := e2.1 h; omega)

theorem int_mul_neg_ovf {M z y : Int} (hz : z < 0) :
    (M ≤ z * y ∨ z * y < -M) ↔ (y < -((M - 1) / -z) ∨ M / -z < y) := by
  have := int_mul_pos_ovf (M := M) (z := -z) (y := -y) (by omega)
  rw [Int.neg_mul_neg] at this
  constructor
  · intro h; rcases this.1 (by omega) with h' | h' <;> omega
  · intro h; rcases this.2 (by omega) with h' | h' <;> omega


theorem smul_pos (hw : 0 < w) (hk : 1 < k.toInt) :
    k.smulOverflow x = (x.slt (BitVec.ofInt w ((-2 ^ (w - 1) : Int).tdiv k.toInt)) ||
      (BitVec.ofInt w ((2 ^ (w - 1) - 1 : Int).tdiv k.toInt)).slt x) := by
  have hx := toInt_bounds x; have hkb := toInt_bounds k
  have hM := two_pow_pos' (w - 1)
  rw [Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg (by omega), Int.tdiv_eq_ediv_of_nonneg (by omega)]
  have q1 := Int.ediv_le_self k.toInt (by omega : (0 : Int) ≤ 2 ^ (w - 1))
  have q1' := Int.ediv_nonneg (by omega : (0 : Int) ≤ 2 ^ (w - 1)) (by omega : (0 : Int) ≤ k.toInt)
  have q2 := Int.ediv_le_self k.toInt (by omega : (0 : Int) ≤ 2 ^ (w - 1) - 1)
  have q2' := Int.ediv_nonneg (by omega : (0 : Int) ≤ 2 ^ (w - 1) - 1)
    (by omega : (0 : Int) ≤ k.toInt)
  simp only [BitVec.smulOverflow, BitVec.slt,
    BitVec.toInt_ofInt_eq_self hw (by omega : -2 ^ (w - 1) ≤ -(2 ^ (w - 1) / k.toInt)) (by omega),
    BitVec.toInt_ofInt_eq_self hw (by omega : -2 ^ (w - 1) ≤ (2 ^ (w - 1) - 1) / k.toInt) (by omega)]
  rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, decide_eq_true_eq, ge_iff_le]
  exact int_mul_pos_ovf (by omega)

theorem smul_neg (hw : 0 < w) (hk : k.toInt < -1) :
    k.smulOverflow x = (x.slt (BitVec.ofInt w ((2 ^ (w - 1) - 1 : Int).tdiv k.toInt)) ||
      (BitVec.ofInt w ((-2 ^ (w - 1) : Int).tdiv k.toInt)).slt x) := by
  have hx := toInt_bounds x; have hkb := toInt_bounds k
  have hM := two_pow_pos' (w - 1)
  have ek : k.toInt = -(-k.toInt) := by omega
  rw [ek, Int.neg_tdiv_neg, Int.tdiv_neg, Int.tdiv_eq_ediv_of_nonneg (by omega),
    Int.tdiv_eq_ediv_of_nonneg (by omega)]
  have q1 := Int.ediv_lt_of_lt_mul (a := 2 ^ (w - 1)) (b := 2 ^ (w - 1)) (c := -k.toInt)
    (by omega) (by
      have := Int.mul_le_mul_of_nonneg_left (show (2 : Int) ≤ -k.toInt by omega) (Int.le_of_lt hM)
      omega)
  have q1' := Int.ediv_nonneg (by omega : (0 : Int) ≤ 2 ^ (w - 1)) (by omega : (0 : Int) ≤ -k.toInt)
  have q2 := Int.ediv_le_self (-k.toInt) (by omega : (0 : Int) ≤ 2 ^ (w - 1) - 1)
  have q2' := Int.ediv_nonneg (by omega : (0 : Int) ≤ 2 ^ (w - 1) - 1)
    (by omega : (0 : Int) ≤ -k.toInt)
  simp only [BitVec.smulOverflow, BitVec.slt,
    BitVec.toInt_ofInt_eq_self hw
      (by omega : -2 ^ (w - 1) ≤ -((2 ^ (w - 1) - 1) / -k.toInt)) (by omega),
    BitVec.toInt_ofInt_eq_self hw (by omega : -2 ^ (w - 1) ≤ 2 ^ (w - 1) / -k.toInt) (by omega)]
  rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, decide_eq_true_eq, ge_iff_le]
  exact int_mul_neg_ovf (by omega)

theorem smul_neg_one (hw : 0 < w) (hk : k.toInt = -1) :
    k.smulOverflow x = decide (x = BitVec.ofInt w (-2 ^ (w - 1))) := by
  have hx := toInt_bounds x
  have e : x = BitVec.ofInt w (-2 ^ (w - 1)) ↔ x.toInt = -2 ^ (w - 1) := by
    rw [← BitVec.toInt_inj, BitVec.toInt_ofInt_eq_self hw] <;> omega
  rw [Bool.eq_iff_iff]; simp [BitVec.smulOverflow, e, hk]; omega

theorem umul_const (hk : 0 < k.toNat) :
    k.umulOverflow x = (BitVec.ofInt w ((2 ^ w - 1 : Int).tdiv k.toNat)).ult x := by
  have := x.isLt; have := k.isLt
  have hp : ((2 ^ w : Nat) : Int) = (2 : Int) ^ w := by push_cast; rfl
  have q := Int.ediv_le_self (k.toNat : Int) (by omega : (0 : Int) ≤ 2 ^ w - 1)
  have q' := Int.ediv_nonneg (by omega : (0 : Int) ≤ 2 ^ w - 1) (by omega : (0 : Int) ≤ k.toNat)
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
  simp only [BitVec.umulOverflow, BitVec.ult, BitVec.toNat_ofInt, hp,
    Int.emod_eq_of_lt q' (show (2 ^ w - 1) / (k.toNat : Int) < (2 : Int) ^ w by omega)]
  have e := Int.ediv_lt_iff_lt_mul (a := 2 ^ w - 1) (b := (x.toNat : Int))
    (by omega : (0 : Int) < k.toNat)
  rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq, ge_iff_le]
  have : ((k.toNat * x.toNat : Nat) : Int) = (x.toNat : Int) * k.toNat := by push_cast; rw [Int.mul_comm]
  omega


theorem umod_add_self {d v : BitVec w} (h : d.uaddOverflow v = false) : (d + v) % d = v % d := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, BitVec.toNat_umod, toNat_add_ok h, Nat.add_mod_left]

theorem umod_umod_of_le {v a b : BitVec w} (ha : 0 < a.toNat) (h : a.toNat ≤ b.toNat) :
    v % a % b = v % a := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_umod]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ ha) h)

theorem umod_umod_of_dvd {v a b : BitVec w} (h : b.toNat ∣ a.toNat) : v % a % b = v % b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_umod, Nat.mod_mod_of_dvd _ h]

theorem ne_and_of_mask {k m x : BitVec w} (h : ¬(k &&& ~~~m) = 0#w) : ¬k = m &&& x := by
  rintro rfl; apply h; ext i; simp; intro h1 _; exact h1

theorem mul_cancel_nat {M a b d : Nat} (hM : Nat.Coprime M a) (hb : b < M) (hd : d < M)
    (h : a * b % M = a * d % M) : b = d := by
  rcases Nat.le_total b d with hbd | hbd
  · have h1 := Nat.sub_mod_eq_zero_of_mod_eq h.symm
    rw [← Nat.mul_sub] at h1
    have h2 := hM.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero h1)
    have := Nat.eq_zero_of_dvd_of_lt h2 (by omega)
    omega
  · have h1 := Nat.sub_mod_eq_zero_of_mod_eq h
    rw [← Nat.mul_sub] at h1
    have h2 := hM.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero h1)
    have := Nat.eq_zero_of_dvd_of_lt h2 (by omega)
    omega

theorem mul_cancel_odd {k a b : BitVec w} (h : k.toNat % 2 = 1) : k * a = k * b ↔ a = b := by
  refine ⟨fun e => BitVec.eq_of_toNat_eq ?_, fun e => by rw [e]⟩
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_mul] at this
  refine mul_cancel_nat ?_ a.isLt b.isLt this
  apply Nat.Coprime.pow_left
  show Nat.gcd 2 k.toNat = 1
  rw [Nat.gcd_rec, h]; rfl

theorem mul_cancel_umul {k a b : BitVec w} (hk : k ≠ 0#w) (ha : k.umulOverflow a = false)
    (hb : k.umulOverflow b = false) : k * a = k * b ↔ a = b := by
  refine ⟨fun e => BitVec.eq_of_toNat_eq ?_, fun e => by rw [e]⟩
  have := congrArg BitVec.toNat e
  rw [toNat_mul_ok ha, toNat_mul_ok hb] at this
  have : 0 < k.toNat := by
    apply Nat.pos_of_ne_zero; intro h0; apply hk; exact BitVec.eq_of_toNat_eq (by simp [h0])
  exact Nat.eq_of_mul_eq_mul_left this ‹_›

theorem mul_cancel_smul {k a b : BitVec w} (hk : k ≠ 0#w) (ha : k.smulOverflow a = false)
    (hb : k.smulOverflow b = false) : k * a = k * b ↔ a = b := by
  refine ⟨fun e => BitVec.eq_of_toInt_eq ?_, fun e => by rw [e]⟩
  have := congrArg BitVec.toInt e
  rw [toInt_mul_ok ha, toInt_mul_ok hb] at this
  have : k.toInt ≠ 0 := by
    intro h0; apply hk; exact BitVec.eq_of_toInt_eq (by simp [h0])
  exact Int.eq_of_mul_eq_mul_left this ‹_›

theorem zshiftl_one_pred (hw : 0 < w) : zshiftl 1 ((w : Int) - 1) = 2 ^ (w - 1) := by
  simp only [zshiftl, Int.one_mul]; congr 1; omega

theorem zshiftl_one_nat : zshiftl 1 (w : Int) = 2 ^ w := by simp [zshiftl]

theorem toInt_pos_ne_one (h0 : 0 < k.toInt) (h1 : ¬(k.toNat : Int) = 1) :
    1 < k.toInt := by
  have h := BitVec.toInt_eq_toNat_cond k
  have := k.isLt
  have : ((2 ^ w : Nat) : Int) > k.toNat := by exact_mod_cast this
  split at h <;> omega

theorem umul_small (h : k.toNat = 0 ∨ (k.toNat : Int) = 1) : k.umulOverflow x = false := by
  have := x.isLt
  rw [umul_ok]; rcases h with h | h
  · simp [h, Nat.two_pow_pos]
  · have : k.toNat = 1 := by omega
    simp [this, x.isLt]

theorem smul_small (hw : (1 : Int) < w) (h : k.toNat = 0 ∨ (k.toNat : Int) = 1) :
    k.smulOverflow x = false := by
  have := toInt_bounds x
  have e : k.toInt = 0 ∨ k.toInt = 1 := by
    rw [BitVec.toInt_eq_toNat_cond]
    have : 4 ≤ 2 ^ w := by
      have := Nat.pow_le_pow_right (n := 2) (by omega) (show 2 ≤ w by omega); simpa using this
    split <;> omega
  have := two_pow_pos' (w - 1)
  rw [smul_ok]; rcases e with e | e <;> rw [e] <;> omega

theorem smul_const_pos (hw : (1 : Int) < w) (h0 : 0 < k.toInt) (h1 : ¬(k.toNat : Int) = 1) :
    k.smulOverflow x = (x.slt (BitVec.ofInt w (tdiv (-zshiftl 1 ((w : Int) - 1)) k.toInt)) ||
      (BitVec.ofInt w (tdiv (zshiftl 1 ((w : Int) - 1) - 1) k.toInt)).slt x) := by
  rw [zshiftl_one_pred (by omega), smul_pos (by omega) (toInt_pos_ne_one h0 h1)]; rfl

theorem smul_const_neg (hw : (1 : Int) < w) (h0 : ¬k.toNat = 0) (h1 : k.toInt ≤ 0)
    (h2 : ¬k.toInt = -1) :
    k.smulOverflow x = (x.slt (BitVec.ofInt w (tdiv (zshiftl 1 ((w : Int) - 1) - 1) k.toInt)) ||
      (BitVec.ofInt w (tdiv (-zshiftl 1 ((w : Int) - 1)) k.toInt)).slt x) := by
  have : k.toInt ≠ 0 := by
    intro e; apply h0; have := BitVec.eq_of_toInt_eq (x := k) (y := 0#w) (by simp [e]); simp [this]
  rw [zshiftl_one_pred (by omega), smul_neg (by omega) (by omega)]; rfl

theorem smul_const_neg_one (hw : (1 : Int) < w) (h : k.toInt = -1) :
    k.smulOverflow x = decide (x = BitVec.ofInt w (-zshiftl 1 ((w : Int) - 1))) := by
  rw [zshiftl_one_pred (by omega), smul_neg_one (by omega) h]

theorem umul_const_rule (h0 : ¬k.toNat = 0) :
    k.umulOverflow x = (BitVec.ofInt w (tdiv (zshiftl 1 (w : Int) - 1) k.toNat)).ult x := by
  rw [zshiftl_one_nat, umul_const (by omega)]; rfl

theorem umul_small' (h : k.toNat = 0 ∨ (k.toNat : Int) = 1) : x.umulOverflow k = false := by
  rw [(ovf_comm _ _).2.2.2, umul_small h]
theorem smul_small' (hw : (1 : Int) < w) (h : k.toNat = 0 ∨ (k.toNat : Int) = 1) :
    x.smulOverflow k = false := by
  rw [(ovf_comm _ _).2.2.1, smul_small hw h]
theorem smul_const_pos' (hw : (1 : Int) < w) (h0 : 0 < k.toInt) (h1 : ¬(k.toNat : Int) = 1) :
    x.smulOverflow k = (x.slt (BitVec.ofInt w (tdiv (-zshiftl 1 ((w : Int) - 1)) k.toInt)) ||
      (BitVec.ofInt w (tdiv (zshiftl 1 ((w : Int) - 1) - 1) k.toInt)).slt x) := by
  rw [(ovf_comm _ _).2.2.1, smul_const_pos hw h0 h1]
theorem smul_const_neg' (hw : (1 : Int) < w) (h0 : ¬k.toNat = 0) (h1 : k.toInt ≤ 0)
    (h2 : ¬k.toInt = -1) :
    x.smulOverflow k = (x.slt (BitVec.ofInt w (tdiv (zshiftl 1 ((w : Int) - 1) - 1) k.toInt)) ||
      (BitVec.ofInt w (tdiv (-zshiftl 1 ((w : Int) - 1)) k.toInt)).slt x) := by
  rw [(ovf_comm _ _).2.2.1, smul_const_neg hw h0 h1 h2]
theorem smul_const_neg_one' (hw : (1 : Int) < w) (h : k.toInt = -1) :
    x.smulOverflow k = decide (x = BitVec.ofInt w (-zshiftl 1 ((w : Int) - 1))) := by
  rw [(ovf_comm _ _).2.2.1, smul_const_neg_one hw h]
theorem umul_const_rule' (h0 : ¬k.toNat = 0) :
    x.umulOverflow k = (BitVec.ofInt w (tdiv (zshiftl 1 (w : Int) - 1) k.toNat)).ult x := by
  rw [(ovf_comm _ _).2.2.2, umul_const_rule h0]

theorem umod_umod_of_lt {v a b : BitVec w} (hb : 0 < b.toNat) (h : b.toNat < a.toNat)
    (hd : b.toNat ∣ a.toNat ∨ a.toNat ∣ b.toNat) : v % a % b = v % b := by
  rcases hd with hd | hd
  · exact umod_umod_of_dvd hd
  · have := Nat.le_of_dvd hb hd; omega

theorem ne_and_of_mask' {k m x : BitVec w} (h : ¬(k.toNat &&& (2 ^ w - 1 - m.toNat)) = 0) :
    ¬k = m &&& x := by
  apply ne_and_of_mask; intro e; apply h
  have := congrArg BitVec.toNat e
  simpa [BitVec.toNat_and, BitVec.toNat_not] using this

theorem append_inj {w' : Nat} {a c : BitVec w} {b d : BitVec w'} :
    a ++ b = c ++ d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have h1 := congrArg (fun x => x.extractLsb' w' w) h
    have h2 := congrArg (fun x => x.extractLsb' 0 w') h
    simp only [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem and_not_self_toNat {k v : BitVec w} : k.toNat &&& v.toNat &&& (2 ^ w - 1 - k.toNat) = 0 := by
  have : k &&& v &&& ~~~k = 0#w := by ext i; simp; intro h _; exact h
  simpa [BitVec.toNat_and, BitVec.toNat_not] using congrArg BitVec.toNat this

theorem toNat_eq_zero_iff {k : BitVec w} : k.toNat = 0 ↔ k = 0#w := by
  rw [← BitVec.toNat_inj]; simp

theorem natCast_toNat_eq_one (hw : 0 < w) {k : BitVec w} : ((k.toNat : Int) = 1) ↔ k = 1#w := by
  rw [← BitVec.toNat_inj]; simp [Nat.one_mod_two_pow hw]; omega

theorem zland_one (n : Nat) : zland (n : Int) 1 = ((n % 2 : Nat) : Int) := by
  show Int.ofNat (n &&& 1) = _
  rw [Nat.and_one_is_mod]; rfl

theorem mul_cancel_flags {k a b : BitVec w} {s1 u1 s2 u2 : Bool}
    (h : zland (k.toNat : Int) 1 = 1 ∨
      ¬k.toNat = 0 ∧ (s1 = true ∧ s2 = true ∨ u1 = true ∧ u2 = true))
    (h1 : (s1 = true → k.smulOverflow a = false) ∧ (u1 = true → k.umulOverflow a = false))
    (h2 : (s2 = true → k.smulOverflow b = false) ∧ (u2 = true → k.umulOverflow b = false)) :
    k * a = k * b ↔ a = b := by
  rw [zland_one] at h
  rcases h with h | ⟨h0, (⟨hs1, hs2⟩ | ⟨hu1, hu2⟩)⟩
  · exact mul_cancel_odd (by omega)
  · exact mul_cancel_smul (by rwa [ne_eq, ← toNat_eq_zero_iff]) (h1.1 hs1) (h2.1 hs2)
  · exact mul_cancel_umul (by rwa [ne_eq, ← toNat_eq_zero_iff]) (h1.2 hu1) (h2.2 hu2)

end

/-! ## Value goals -/

/-- The value half of `Refines.den` or `Refines.denB`, with the widths of the atoms natural
and the values of the literals opaque. -/
macro "bvr_sem_b_core" : tactic => `(tactic| (
  first
    | refine fun n w ht ρ (x : BitVec n) h => ?_
    | refine fun w ρ (x : Bool) h => ?_
  have w' := w
  bvr_facts
  bvr_nat_widths
  (try simp only [Int.toNat_natCast, Int.natCast_pos] at *)
  bvr_lits
  (try simp only [← BitVec.toInt_ofInt, natCast_toNat_ofInt, toNat_emod_eq,
    BitVec.ofInt_emod_two_pow] at *)
  bvr_gen_lits
  bvr_fix_widths
  (try simp only [Int.natCast_inj, Int.natCast_pos, BitVec.toNat_inj] at *)
  (try subst_vars)
  bvr_cases
  all_goals bvr_bool_vars
  all_goals (try simp_all [unchecked, checked_signed, checked_unsigned, checked_meet])
  all_goals (try (repeat' split at h))
  all_goals (try simp_all [ssubOverflow_zero_left])
  all_goals (try simp only [fold_checked_mk (by assumption), add_overflows_mk (hn := by assumption),
    sub_overflows_mk (hn := by assumption), mul_overflows_mk (hn := by assumption),
    is_int_min_mk (hn := by assumption)] at *)
  all_goals (try (repeat' apply And.intro))))

macro "bvr_sem_b" : tactic => `(tactic| (
  bvr_sem_b_core
  all_goals (first
    | (bvr_decide_small; done)
    | (simp_all [one_uadd_one, one_sadd_one]; done)
    | (simp_all [sadd_pos, sadd_nonpos, uadd_not, usub_self, ssub_self, uadd_zero, sadd_zero,
        umul_udiv, one_uadd, one_sadd]; done)
    | (simp_all [sadd_pos', sadd_nonpos', uadd_not', uadd_zero', sadd_zero', umul_udiv', one_uadd',
        one_sadd']; done)
    | (simp_all [umul_small, smul_small, smul_const_pos, smul_const_neg, smul_const_neg_one,
        umul_const_rule]; done)
    | (simp_all [umul_small', smul_small', smul_const_pos', smul_const_neg', smul_const_neg_one',
        umul_const_rule']; done)
    | (simp_all [umod_add_self]; done)
    | (simp_all [umod_umod_of_le, umod_umod_of_lt]; done)
    | (simp_all [ne_and_of_mask', and_not_self_toNat]; done)
    | (simp_all [append_inj]; done)
    | (simp_all [toNat_eq_zero_iff, natCast_toNat_eq_one]; done)
    | (simp only [BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle, decide_eq_true_eq,
        decide_eq_false_iff_not, Bool.not_eq_true, Bool.not_eq_false] at *; omega)
    | (grind [BitVec.neg_eq_not_add]; done)
    | (bvr_ovf; done)
    | skip)))

end Bvr.Lib

namespace Bvr.Lib.SemEq

open Classical

variable {FS : FloatSem}

/-! ## Significant bits -/

/-- The operands of a predicate on bit-vectors, of a natural width. -/
theorem WT_pred_nat {op : Binop} {a b : Term} {t : Ty}
    (hop : ∀ a b t, op.WT a b t ↔ (∃ n : Int, 0 < n ∧ a = .TBitVector n) ∧ b = a ∧ t = .TBool)
    (w : (Term.mk (.Binop op a b) t).WT) :
    ∃ n : Nat, 0 < n ∧ a.WT ∧ b.WT ∧ a.ty = .TBitVector (n : Int) ∧
      b.ty = .TBitVector (n : Int) := by
  obtain ⟨wa, wb, hb, m, hm, ha⟩ := WT_pred hop w
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hm)
  exact ⟨n, by omega, wa, wb, ha, by rw [hb, ha]⟩

/-- A multiplication of values of few significant bits does not overflow. -/
theorem Refines.mulOvf_msb {s : Bool} {v1 v2 : Term} {t : Ty}
    (h : (s && decide (msb_of v1 + msb_of v2 < size v1 - 2) ||
      !s && decide (msb_of v1 + msb_of v2 < size v1 - 1)) = true) :
    Refines FS (.mk (.Binop (.MulOvf s) v1 v2) t) v_false := by
  replace h : if s then msb_of v1 + msb_of v2 < size v1 - 2
      else msb_of v1 + msb_of v2 < size v1 - 1 := by
    cases s <;> simp only [Bool.true_and, Bool.false_and, Bool.not_true, Bool.not_false,
      Bool.or_false, Bool.false_or, ite_true, ite_false, Bool.false_eq_true] at h ⊢ <;>
      exact of_decide_eq_true h
  refine Refines.denB (fun w => ?_) (fun w => ?_) (fun w ρ b e => ?_)
  · exact (WT_binop.1 w).1.2.2
  · simp [((WT_binop.1 w).1.2.2).symm]
  · obtain ⟨n, hn, w1, w2, h1, h2⟩ := WT_pred_nat (fun _ _ _ => by simp [Binop.WT]) w
    simp only [denB, h1, Int.natCast_pos, hn, ite_true, Int.toNat_natCast] at e
    cases e1 : den FS ρ n v1 <;> cases e2 : den FS ρ n v2 <;> rw [e1, e2] at e <;>
      simp only [binB_some, binB_none_l, binB_none_r, reduceCtorEq, Option.some.injEq] at e
    rename_i x y
    have bx := den_msb w1 h1 e1
    have by' := den_msb w2 h2 e2
    simp only [size_eq, h1, size_of_ty_bitVector] at h
    subst e
    simp only [v_false, denB, Option.some.injEq]
    by_cases hx : x.toNat = 0
    · have : x = 0#n := BitVec.eq_of_toNat_eq (by simp [hx])
      subst this
      cases s <;> simp [BitVec.umulOverflow, BitVec.smulOverflow, Int.le_of_lt (two_pow_pos' _)]
    by_cases hy : y.toNat = 0
    · have : y = 0#n := BitVec.eq_of_toNat_eq (by simp [hy])
      subst this
      cases s <;> simp [BitVec.umulOverflow, BitVec.smulOverflow, Int.le_of_lt (two_pow_pos' _)]
    have ha : 0 ≤ msb_of v1 := by
      apply Int.not_lt.1; intro hc
      have : (msb_of v1 + 1).toNat = 0 := by omega
      rw [this] at bx; omega
    have hb : 0 ≤ msb_of v2 := by
      apply Int.not_lt.1; intro hc
      have : (msb_of v2 + 1).toNat = 0 := by omega
      rw [this] at by'; omega
    have hp : x.toNat * y.toNat < 2 ^ ((msb_of v1 + 1).toNat + (msb_of v2 + 1).toNat) := by
      rw [Nat.pow_add]; exact Nat.mul_lt_mul'' bx by'
    cases s
    · simp only [Bool.false_eq_true, ite_false] at h ⊢
      rw [eq_comm, umul_ok]
      exact Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (by omega) (by omega))
    · simp only [ite_true] at h ⊢
      have lx : 2 * x.toNat < 2 ^ n := by
        have := Nat.pow_le_pow_right (n := 2) (by omega) (show (msb_of v1 + 1).toNat + 1 ≤ n by omega)
        rw [Nat.pow_succ] at this; omega
      have ly : 2 * y.toNat < 2 ^ n := by
        have := Nat.pow_le_pow_right (n := 2) (by omega) (show (msb_of v2 + 1).toNat + 1 ≤ n by omega)
        rw [Nat.pow_succ] at this; omega
      have hq := Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (n := 2) (by omega)
        (show (msb_of v1 + 1).toNat + (msb_of v2 + 1).toNat ≤ n - 1 by omega))
      rw [eq_comm, smul_ok, BitVec.toInt_eq_toNat_of_lt lx, BitVec.toInt_eq_toNat_of_lt ly]
      have : ((2 ^ (n - 1) : Nat) : Int) = (2 : Int) ^ (n - 1) := by push_cast; rfl
      have : ((x.toNat * y.toNat : Nat) : Int) < 2 ^ (n - 1) := by omega
      push_cast at this
      constructor
      · have := Int.mul_nonneg (Int.natCast_nonneg x.toNat) (Int.natCast_nonneg y.toNat)
        have := two_pow_pos' (n - 1); omega
      · exact this

/-! ## Extensions and extractions -/

theorem nat_and_mask_eq_zero_iff {z N K : Nat} (hz : z < 2^(N+K)) :
    z &&& ((2^K - 1) * 2^N) = 0 ↔ z < 2^N := by
  rw [← Nat.shiftLeft_eq]
  constructor
  · intro h
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    cases hb : z.testBit i
    · rfl
    have hik : i < N + K := by
      have := Nat.ge_two_pow_of_testBit hb
      refine Nat.lt_of_not_le fun hc => ?_
      have : 2^(N+K) ≤ 2^i := Nat.pow_le_pow_right (by omega) hc
      omega
    have := congrArg (fun x => x.testBit i) h
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit, hb,
      Nat.testBit_two_pow_sub_one] at this
    simp at this
    omega
  · intro h
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit]
    by_cases hi : i < N
    · simp; omega
    · have : z.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [this]

theorem zland_mask_eq_zero_iff {z n k : Int} (hn : 0 ≤ n) (hk : 0 ≤ k) (h0 : 0 ≤ z)
    (h1 : z < 2 ^ (n + k).toNat) :
    zland z (zshiftl (zshiftl 1 k - 1) n) = 0 ↔ z < 2 ^ n.toNat := by
  obtain ⟨Z, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  have hm : zshiftl (zshiftl 1 k - 1) n = (((2 ^ k.toNat - 1) * 2 ^ n.toNat : Nat) : Int) := by
    have := Nat.one_le_two_pow (n := k.toNat)
    simp only [zshiftl, Int.one_mul]
    rw [Int.natCast_mul, Int.natCast_sub this]
    simp
  rw [hm]
  show Int.ofNat (Z &&& _) = 0 ↔ _
  have h1' : Z < 2 ^ (n.toNat + k.toNat) := by
    have : (n + k).toNat = n.toNat + k.toNat := by omega
    rw [this] at h1; exact_mod_cast h1
  rw [Int.ofNat_eq_natCast, Int.natCast_eq_zero, nat_and_mask_eq_zero_iff h1']
  constructor <;> intro h <;> exact_mod_cast h

theorem zext_mask {w : Nat} {b : Int} (hb : 0 ≤ b) {k : BitVec ((w : Int) + b).toNat} :
    zland (k.toNat : Int) (zshiftl (zshiftl 1 b - 1) w) = 0 ↔ k.toNat < 2 ^ w := by
  have := zland_mask_eq_zero_iff (z := (k.toNat : Int)) (n := (w : Int)) (k := b) (by omega) hb
    (by omega) (by have := k.isLt; exact_mod_cast this)
  rw [this]; simp only [Int.toNat_natCast]; exact_mod_cast Iff.rfl

theorem setWidth_eq_iff {w m : Nat} (h : w ≤ m) {v : BitVec w} {k : BitVec m} :
    v.setWidth m = k ↔ k.toNat < 2 ^ w ∧ v = k.setWidth w := by
  have := v.isLt
  constructor
  · rintro rfl
    have hm := Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) h)
    refine ⟨by simp [Nat.mod_eq_of_lt hm]; omega, ?_⟩
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) h)),
      Nat.mod_eq_of_lt this]
  · rintro ⟨hk, rfl⟩
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt hk,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by omega) h))]

theorem setWidth_eq_iff' {w : Nat} {b : Int} (hb : 0 ≤ b) {v : BitVec w}
    {k : BitVec ((w : Int) + b).toNat} :
    v.setWidth ((w : Int) + b).toNat = k ↔ k.toNat < 2 ^ w ∧ v = k.setWidth w :=
  setWidth_eq_iff (by omega)

theorem le_zmax_left (a b : Int) : a ≤ zmax a b := by
  simp only [zmax]; split <;> rename_i h <;> simp at h <;> omega
theorem le_zmax_right (a b : Int) : b ≤ zmax a b := by
  simp only [zmax]; split <;> rename_i h <;> simp at h <;> omega

theorem extract_low_inj {n m : Nat} {x y : BitVec n} (hx : x.toNat < 2 ^ m) (hy : y.toNat < 2 ^ m) :
    x.extractLsb' 0 m = y.extractLsb' 0 m ↔ x = y := by
  refine ⟨fun e => BitVec.eq_of_toNat_eq ?_, fun e => by rw [e]⟩
  have := congrArg BitVec.toNat e
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hy] at this
  exact this

/-- An equality of bit-vectors with no significant bits above [M]. -/
theorem Refines.eq_low {a b : Term} {M : Int} {t : Ty} (hbv : is_bv a.ty = true) (hM0 : 0 ≤ M)
    (ha : msb_of a ≤ M) (hb : msb_of b ≤ M) (hM : M < size a - 1) :
    Refines FS (.mk (.Binop .Eq a b) t)
      (.mk (.Binop .Eq (.mk (.Unop (.BvExtract 0 M) a) (.TBitVector (M - 0 + 1)))
        (.mk (.Unop (.BvExtract 0 M) b) (.TBitVector (M - 0 + 1)))) .TBool) := by
  have hty : ∃ n : Int, a.ty = .TBitVector n := by
    revert hbv; cases a.ty <;> simp [is_bv, firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse]
  obtain ⟨n, hn⟩ := hty
  simp only [size_eq, hn, size_of_ty_bitVector] at hM
  refine Refines.denB (fun w => (WT_eq.1 w).2.1) (fun w => ?_) (fun w ρ c e => ?_)
  · obtain ⟨hab, ht, wa, wb⟩ := WT_eq.1 w
    simp [WT_eq, WT_unop, Unop.WT, wa, wb, ← hab, hn, ht]; omega
  · obtain ⟨hab, -, wa, wb⟩ := WT_eq.1 w
    obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ n by omega)
    have hb' : b.ty = .TBitVector (N : Int) := by rw [← hab, hn]
    simp only [denB, hn, Term.ty_mk, den, hb', Int.toNat_natCast] at e ⊢
    have hp : 0 < (N : Int) := by omega
    simp only [hp, ite_true] at e
    have hq : 0 < M - 0 + 1 := by omega
    simp only [hq, ite_true]
    cases ea : den FS ρ N a <;> cases eb : den FS ρ N b <;> rw [ea, eb] at e <;>
      simp only [binB_some, binB_none_l, binB_none_r, reduceCtorEq, Option.some.injEq,
        Option.map_some] at e ⊢
    rename_i x y
    have bx := den_msb_aux _ a (Nat.lt_succ_self _) wa hn x ea M ha
    have by' := den_msb_aux _ b (Nat.lt_succ_self _) wb hb' y eb M hb
    have e1 : (M + 1).toNat = (M - 0 + 1).toNat := by omega
    rw [e1] at bx by'
    rw [← e, Int.toNat_zero]; simp only [extract_low_inj bx by']

/-- The remainder by a power of two keeps the low bits. -/
theorem Refines.rem_pow2 {v : Term} {r : Int} {T t : Ty}
    (hp : is_pow2 (to_z false (bv_of_lit (.mk (.BitVec r) T))) = true)
    (h1 : to_z false (bv_of_lit (.mk (.BitVec r) T)) > 1) :
    Refines FS (.mk (.Binop (.Rem false) v (.mk (.BitVec r) T)) t)
      (.mk (.Unop (.BvExtend false (size v - log2 (to_z false (bv_of_lit (.mk (.BitVec r) T)))))
        (.mk (.Unop (.BvExtract 0 (log2 (to_z false (bv_of_lit (.mk (.BitVec r) T))) - 1)) v)
          (.TBitVector (log2 (to_z false (bv_of_lit (.mk (.BitVec r) T))) - 1 - 0 + 1))))
        (.TBitVector (size (.mk (.Unop (.BvExtract 0 (log2 (to_z false (bv_of_lit (.mk (.BitVec r) T))) - 1)) v)
          (.TBitVector (log2 (to_z false (bv_of_lit (.mk (.BitVec r) T))) - 1 - 0 + 1))) +
          (size v - log2 (to_z false (bv_of_lit (.mk (.BitVec r) T))))))) := by
  generalize hz : to_z false (bv_of_lit (.mk (.BitVec r) T)) = z at *
  obtain ⟨hz2, hk0⟩ := is_pow2_eq hp
  generalize hk : log2 z = k at *
  have key : (Term.mk (.Binop (.Rem false) v (.mk (.BitVec r) T)) t).WT →
      ∃ n : Nat, 0 < n ∧ v.WT ∧ v.ty = .TBitVector n ∧ T = .TBitVector n ∧ t = .TBitVector n ∧
        z = r ∧ 0 ≤ r ∧ r < 2 ^ n ∧ 1 ≤ k ∧ k < n := by
    intro w
    obtain ⟨w1, wv, wl⟩ := WT_binop.1 w
    simp only [Binop.WT, Ty.sort_eq, Term.ty_mk] at w1
    obtain ⟨⟨m, hm, hv⟩, hT, ht⟩ := w1
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hm)
    have hT' : T = .TBitVector (n : Int) := by rw [hT, hv]
    rw [hT'] at wl hz; rw [hv] at ht
    obtain ⟨-, r0, r1⟩ := WT_bitVec_bv.1 wl
    simp only [Int.toNat_natCast] at r1
    simp only [bv_of_lit_bv, to_z_mk, Bool.false_eq_true, ite_false,
      toNat_ofInt_of_lt r0 r1] at hz
    have hzr : z = r := by omega
    subst hzr
    have hkn : 2 ^ k.toNat < 2 ^ n := by
      have : ((2 ^ k.toNat : Nat) : Int) < ((2 ^ n : Nat) : Int) := by push_cast; omega
      exact_mod_cast this
    rw [Nat.pow_lt_pow_iff_right (by omega)] at hkn
    have : k.toNat ≠ 0 := by intro h0; rw [h0] at hz2; omega
    exact ⟨n, by omega, wv, hv, hT', ht, rfl, r0, r1, by omega, by omega⟩
  refine Refines.den (fun w => ?_) (fun w => ?_) (fun n w ht ρ x e => ?_)
  · obtain ⟨n, -, -, -, -, ht, -⟩ := key w; exact ⟨n, ht⟩
  · obtain ⟨n, hn, wv, hv, -, ht, -, -, -, hk1, hkn⟩ := key w
    simp only [WT_unop, Unop.WT, Ty.sort_eq, Term.ty_mk, size_eq, size_of_ty_bitVector, hv, ht,
      wv, Ty.TBitVector.injEq]
    exact ⟨⟨⟨_, by omega, rfl, by omega, rfl⟩, ⟨_, rfl, Int.le_refl _, by omega, by omega, trivial⟩,
      trivial⟩, by omega⟩
  · obtain ⟨N, hn, wv, hv, hT, ht', hzr, r0, r1, hk1, hkn⟩ := key w
    subst hzr hT
    rw [ht'] at ht; simp only [Term.ty_mk, Ty.TBitVector.injEq, Int.natCast_inj] at ht
    obtain rfl : n = N := ht.symm
    simp only [den, hv, Term.ty_mk, Int.toNat_natCast, Bool.false_eq_true, ite_false] at e ⊢
    cases ev : den FS ρ n v <;> rw [ev] at e <;> simp at e
    rename_i y
    subst e
    simp only [Option.map_some, Option.some.injEq, Int.toNat_zero]
    have ek : (k - 1 - 0 + 1).toNat = k.toNat := by omega
    rw [ek]
    have hr : (BitVec.ofInt n z).toNat = 2 ^ k.toNat := by
      rw [toNat_ofInt_of_lt r0 r1, hz2, show ((2 : Int) ^ k.toNat) = ((2 ^ k.toNat : Nat) : Int) by
        push_cast; rfl, Int.toNat_natCast]
    have hkn' : 2 ^ k.toNat ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, BitVec.toNat_umod, hr, Nat.shiftRight_zero,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) hkn')]

/-! ## Constants times a value -/

/-- The integer that a bit-vector stands for, in a signedness. -/
abbrev iv (s : Bool) {w : Nat} (x : BitVec w) : Int := to_z s ⟨w, x⟩

theorem iv_inj {s : Bool} {w : Nat} {a b : BitVec w} : iv s a = iv s b ↔ a = b := by
  cases s <;> simp [iv, to_z_mk, BitVec.toInt_inj, Int.natCast_inj, BitVec.toNat_inj]

theorem iv_mul {s : Bool} {w : Nat} {a b : BitVec w}
    (h : if s then a.smulOverflow b = false else a.umulOverflow b = false) :
    iv s (a * b) = iv s a * iv s b := by
  cases s <;> simp only [iv, to_z_mk, ite_true, ite_false, Bool.false_eq_true] at h ⊢
  · rw [toNat_mul_ok h]; push_cast; rfl
  · exact toInt_mul_ok h

theorem iv_range {s : Bool} {w : Nat} (x : BitVec w) :
    if s then -2 ^ (w - 1) ≤ iv s x ∧ iv s x < 2 ^ (w - 1) else 0 ≤ iv s x ∧ iv s x < 2 ^ w := by
  cases s <;> simp only [iv, to_z_mk, ite_true, ite_false, Bool.false_eq_true]
  · have := x.isLt; exact ⟨by omega, by exact_mod_cast this⟩
  · exact toInt_bounds x

theorem iv_ofInt {s : Bool} {w : Nat} (hw : 0 < w) {q : Int}
    (h : if s then -2 ^ (w - 1) ≤ q ∧ q < 2 ^ (w - 1) else 0 ≤ q ∧ q < 2 ^ w) :
    iv s (BitVec.ofInt w q) = q := by
  cases s <;> simp only [iv, to_z_mk, ite_true, ite_false, Bool.false_eq_true] at h ⊢
  · rw [toNat_ofInt_of_lt h.1 h.2]; omega
  · exact BitVec.toInt_ofInt_eq_self hw h.1 h.2

theorem denB_eq_lit {ρ x} {W : Nat} {z : Int} {X : BitVec W} (hW : 0 < W) (hx : x.ty = .TBitVector W)
    (ex : den FS ρ W x = some X) :
    denB FS ρ (.mk (.Binop .Eq x (.mk (.BitVec z) (.TBitVector W))) .TBool) =
      some (decide (X = BitVec.ofInt W z)) := by
  simp [denB, den, hx, hW, ex]

theorem mul_eq_iff_tdiv {a c y : Int} (ha : a ≠ 0) (hd : a ∣ c) : c = a * y ↔ y = c.tdiv a := by
  obtain ⟨q, rfl⟩ := hd
  rw [Int.mul_tdiv_cancel_left _ ha]
  constructor
  · intro h; exact (Int.eq_of_mul_eq_mul_left ha h).symm
  · rintro rfl; rfl

theorem false_eq_decide {p : Prop} [Decidable p] : (false = decide p) = ¬p := by
  by_cases h : p <;> simp [h]

section
variable {s : Bool} {W : Nat} {X : BitVec W} {a c : Int}

theorem mulc_zero (ha : a ≠ 0) (hc : c = 0) : X = BitVec.ofInt W 0 ↔ c = a * iv s X := by
  rw [hc, show BitVec.ofInt W 0 = 0#W by apply BitVec.eq_of_toNat_eq; simp, ← iv_inj (s := s),
    show iv s (0#W) = 0 by cases s <;> simp [iv]]
  constructor
  · intro h; rw [h, Int.mul_zero]
  · intro h; exact (Int.mul_eq_zero.1 h.symm).resolve_left ha

theorem mulc_fits (hW : 0 < W) (ha : a ≠ 0) (hd : a ∣ c)
    (hfit : if s then -2 ^ (W - 1) ≤ c.tdiv a ∧ c.tdiv a < 2 ^ (W - 1)
      else 0 ≤ c.tdiv a ∧ c.tdiv a < 2 ^ W) :
    X = BitVec.ofInt W (c.tdiv a) ↔ c = a * iv s X := by
  rw [mul_eq_iff_tdiv ha hd, ← iv_inj (s := s), iv_ofInt hW hfit]

theorem mulc_nofit (ha : a ≠ 0) (hd : a ∣ c)
    (hfit : ¬if s then -2 ^ (W - 1) ≤ c.tdiv a ∧ c.tdiv a < 2 ^ (W - 1)
      else 0 ≤ c.tdiv a ∧ c.tdiv a < 2 ^ W) :
    ¬c = a * iv s X := by
  intro h; apply hfit; rw [← (mul_eq_iff_tdiv ha hd).1 h]; exact iv_range X

theorem mulc_nodvd (hd : ¬a ∣ c) : ¬c = a * iv s X := fun h => hd ⟨_, h⟩

end

/-- A constant equal to a checked product of a constant: the values of the rule in integers. -/
theorem Refines.eq_mul_const {n m : Int} {Tn Tm T t : Ty} {ck : Checked} {x r : Term}
    (hck : is_checked ck = true)
    (hsyn : ∀ W : Nat, 0 < W → x.ty = .TBitVector W → x.WT → size x = W → r.WT ∧ r.ty = .TBool)
    (hsem : ∀ (W : Nat) (N M X : BitVec W) ρ, 0 < W → x.ty = .TBitVector W → size x = W →
      to_z (!ck.unsigned) (bv_of_lit (.mk (.BitVec n) Tn)) = iv (!ck.unsigned) N →
      to_z (!ck.unsigned) (bv_of_lit (.mk (.BitVec m) Tm)) = iv (!ck.unsigned) M →
      den FS ρ W x = some X →
      denB FS ρ r = some (decide (iv (!ck.unsigned) N = iv (!ck.unsigned) M * iv (!ck.unsigned) X))) :
    Refines FS
      (.mk (.Binop .Eq (.mk (.BitVec n) Tn) (.mk (.Binop (.Mul ck) (.mk (.BitVec m) Tm) x) T)) t) r := by
  have key : (Term.mk (.Binop .Eq (.mk (.BitVec n) Tn)
      (.mk (.Binop (.Mul ck) (.mk (.BitVec m) Tm) x) T)) t).WT →
      ∃ W : Nat, 0 < W ∧ x.ty = .TBitVector W ∧ x.WT ∧ Tn = .TBitVector W ∧ Tm = .TBitVector W ∧
        T = .TBitVector W ∧ t = .TBool := by
    intro w
    obtain ⟨h1, ht, -, wm⟩ := WT_eq.1 w
    obtain ⟨w2, -, wx⟩ := WT_binop.1 wm
    simp only [Binop.WT, Ty.sort_eq, Term.ty_mk] at w2 h1
    obtain ⟨⟨W, hW, hm⟩, hx, hT⟩ := w2
    obtain ⟨W, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hW)
    exact ⟨W, by omega, by rw [hx, hm], wx, by rw [h1, hT, hm], hm, by rw [hT, hm], ht⟩
  refine Refines.denB (fun w => (WT_eq.1 w).2.1) (fun w => ?_) (fun w ρ b e => ?_)
  · obtain ⟨W, hW, hx, wx, -, -, -, ht⟩ := key w
    have := hsyn W hW hx wx (by simp [hx])
    simp [this, ht]
  · obtain ⟨W, hW, hx, wx, rfl, rfl, rfl, rfl⟩ := key w
    simp only [denB, den, Term.ty_mk, Int.natCast_pos, hW, ite_true, Int.toNat_natCast] at e
    cases ex : den FS ρ W x <;> rw [ex] at e <;> simp only [ckOp_none_r, binB_none_r, ckOp_some,
      reduceCtorEq] at e
    rename_i X
    split at e
    · simp at e
    rename_i hov
    simp only [binB_some, Option.some.injEq] at e
    subst e
    rw [hsem W (BitVec.ofInt W n) (BitVec.ofInt W m) X ρ hW hx (by simp [hx]) (by simp [iv])
      (by simp [iv]) ex]
    have hs : if !ck.unsigned then (BitVec.ofInt W m).smulOverflow X = false
        else (BitVec.ofInt W m).umulOverflow X = false := by
      obtain ⟨cs, cu⟩ := ck
      cases cu <;> simp_all [is_checked]
    simp only [← iv_mul hs, iv_inj]

/-! ## The rule tactics -/

/-- The typing and value halves, closed as far as possible. -/
macro "bvr_halves_b" : tactic => `(tactic|
  all_goals first
    | (bvr_wt; done)
    | bvr_sem_b
    | skip)

/-- `bvr_rule`, for the functions of boolean specs and `sem_eq`. -/
macro "bvr_rule_b" : tactic => `(tactic| (bvr_rule_core; bvr_halves_b))

/-- `bvr_rule_b`, with the (integer) widths of the body normalized first. -/
macro "bvr_rule_b_arith" : tactic => `(tactic| (
  bvr_rule_lift
  all_goals (try simp +arith only [])
  bvr_rule_apply
  bvr_halves_b))

/-- `bvr_rule_b`, leaving the value goals after `bvr_sem_b_core`. -/
macro "bvr_rule_b_sem" : tactic => `(tactic| (
  bvr_rule_core
  all_goals first
    | (bvr_wt; done)
    | bvr_sem_b_core))

end Bvr.Lib.SemEq
