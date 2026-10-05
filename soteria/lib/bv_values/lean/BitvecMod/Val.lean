import KanonBool.Sem
import CoreMod.Types

/-!
# Values of bit-vector and boolean terms

The operations, on `Option (BitVec n)` and `Option Bool` (`none` for poison),
with which the bitvec module computes the values of its nodes from those of
their operands (`Sem.den`), and the values of terms as bit-vectors (`evBV`) or
booleans (`evB`), given the bit-vectors among the values of the language
(`vbv`) and its booleans (`KanonBool.Sem.vbool`).
-/

namespace BitvecMod

open Classical

/-! ## Operations on bit-vectors and booleans, poisoned by their operands -/

/-- Checked arithmetic: poison when a checked flag overflows. -/
def ckOp {n : Nat} (c : CoreMod.Checked) (sovf uovf : BitVec n → BitVec n → Bool)
    (f : BitVec n → BitVec n → BitVec n) :
    Option (BitVec n) → Option (BitVec n) → Option (BitVec n)
  | some x, some y =>
    if (c.signed && sovf x y) || (c.unsigned && uovf x y) then none else some (f x y)
  | _, _ => none

/-- Plain binary operations. -/
def binOp {n : Nat} (f : BitVec n → BitVec n → BitVec n) :
    Option (BitVec n) → Option (BitVec n) → Option (BitVec n)
  | some x, some y => some (f x y)
  | _, _ => none

/-- Negation, checked against `INT_MIN`. -/
def negOp {n : Nat} (c : Bool) : Option (BitVec n) → Option (BitVec n)
  | some x => if c && x = BitVec.intMin n then none else some (-x)
  | none => none

/-- Parallel conjunction and disjunction: `false` (resp. `true`) wins over
poison. -/
def andB : Option Bool → Option Bool → Option Bool
  | some false, _ => some false
  | _, some false => some false
  | some true, some true => some true
  | _, _ => none

def orB : Option Bool → Option Bool → Option Bool
  | some true, _ => some true
  | _, some true => some true
  | some false, some false => some false
  | _, _ => none

/-- A binary predicate on values. -/
def binB {α : Type} (f : α → α → Bool) : Option α → Option α → Option Bool
  | some x, some y => some (f x y)
  | _, _ => none

@[simp] theorem ckOp_none_l {n c sovf uovf f} (b : Option (BitVec n)) :
    ckOp c sovf uovf f none b = none := rfl
@[simp] theorem ckOp_none_r {n c sovf uovf f} (a : Option (BitVec n)) :
    ckOp c sovf uovf f a none = none := by cases a <;> rfl
@[simp] theorem ckOp_some {n c sovf uovf f} (x y : BitVec n) :
    ckOp c sovf uovf f (some x) (some y) =
      if (c.signed && sovf x y) || (c.unsigned && uovf x y) then none else some (f x y) := rfl
@[simp] theorem binOp_none_l {n f} (b : Option (BitVec n)) : binOp f none b = none := rfl
@[simp] theorem binOp_none_r {n f} (a : Option (BitVec n)) : binOp f a none = none := by
  cases a <;> rfl
@[simp] theorem binOp_some {n f} (x y : BitVec n) : binOp f (some x) (some y) = some (f x y) :=
  rfl
@[simp] theorem negOp_none {n c} : negOp (n := n) c none = none := rfl
@[simp] theorem negOp_some {n c} (x : BitVec n) :
    negOp c (some x) = if c && x = BitVec.intMin n then none else some (-x) := rfl

@[simp] theorem binB_some {α f} (x y : α) : binB f (some x) (some y) = some (f x y) := rfl
@[simp] theorem binB_none_l {α f} (y : Option α) : binB f none y = none := rfl
@[simp] theorem binB_none_r {α f} (x : Option α) : binB f x none = none := by cases x <;> rfl

@[simp] theorem andB_some {x y : Bool} : andB (some x) (some y) = some (x && y) := by
  cases x <;> cases y <;> rfl
@[simp] theorem orB_some {x y : Bool} : orB (some x) (some y) = some (x || y) := by
  cases x <;> cases y <;> rfl
@[simp] theorem andB_false_l (b : Option Bool) : andB (some false) b = some false := rfl
@[simp] theorem andB_false_r (a : Option Bool) : andB a (some false) = some false := by
  rcases a with _ | _ | _ <;> rfl
@[simp] theorem andB_true_l (b : Option Bool) : andB (some true) b = b := by
  rcases b with _ | _ | _ <;> rfl
@[simp] theorem andB_true_r (a : Option Bool) : andB a (some true) = a := by
  rcases a with _ | _ | _ <;> rfl
@[simp] theorem andB_none_none : andB none none = none := rfl
@[simp] theorem orB_true_l (b : Option Bool) : orB (some true) b = some true := rfl
@[simp] theorem orB_true_r (a : Option Bool) : orB a (some true) = some true := by
  rcases a with _ | _ | _ <;> rfl
@[simp] theorem orB_false_l (b : Option Bool) : orB (some false) b = b := by
  rcases b with _ | _ | _ <;> rfl
@[simp] theorem orB_false_r (a : Option Bool) : orB a (some false) = a := by
  rcases a with _ | _ | _ <;> rfl
@[simp] theorem orB_none_none : orB none none = none := rfl

/-! ## The values of terms -/

section
variable {S : Kanon.Sem}

/-- The value of `t` as a bit-vector of width `n`, given the bit-vectors among
the values (`vbv`): `none` if `t` is poison, or not a bit-vector of width `n`. -/
noncomputable def evBVof (vbv : (n : Nat) → BitVec n → S.Val) (ρ : S.Env) (n : Nat)
    (t : S.Term) : Option (BitVec n) :=
  if h : ∃ x, S.eval ρ t = some (vbv n x) then some h.choose else none

theorem evBVof_eq_some {vbv : (n : Nat) → BitVec n → S.Val}
    (inj : ∀ n (x y : BitVec n), vbv n x = vbv n y → x = y) {ρ n t x} :
    evBVof vbv ρ n t = some x ↔ S.eval ρ t = some (vbv n x) := by
  unfold evBVof
  by_cases h : ∃ x, S.eval ρ t = some (vbv n x)
  · rw [dif_pos h]
    have hs := h.choose_spec
    constructor
    · intro e; obtain rfl := Option.some.inj e; exact hs
    · intro e
      exact congrArg some (inj _ _ _ (Option.some.inj (hs.symm.trans e)))
  · rw [dif_neg h]
    exact ⟨fun e => (by cases e), fun e => absurd ⟨x, e⟩ h⟩

variable [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}

/-- The value of `t` as a boolean: `none` if `t` is poison, or not a boolean. -/
noncomputable def evB (LBool : KanonBool.Syntax B) [KanonBool.Sem LBool] (ρ : S.Env)
    (t : S.Term) : Option Bool :=
  if h : ∃ b, S.eval ρ t = some (KanonBool.Sem.vbool LBool b) then some h.choose else none

theorem evB_eq_some {LBool : KanonBool.Syntax B} [KanonBool.Sem LBool] {ρ t b} :
    evB LBool ρ t = some b ↔ S.eval ρ t = some (KanonBool.Sem.vbool LBool b) := by
  unfold evB
  by_cases h : ∃ b, S.eval ρ t = some (KanonBool.Sem.vbool LBool b)
  · rw [dif_pos h]
    have hs := h.choose_spec
    constructor
    · intro e; obtain rfl := Option.some.inj e; exact hs
    · intro e
      exact congrArg some (KanonBool.Sem.vbool_eq_iff.1 (Option.some.inj (hs.symm.trans e)))
  · rw [dif_neg h]
    exact ⟨fun e => (by cases e), fun e => absurd ⟨b, e⟩ h⟩

end

/-! ## Bit-vectors among values

The operations of the modules that use the bitvec module on the values of
their operands: `decBV vbv o` is the bit-vector that the value `o` is, if any. -/

section
variable {V : Type} (vbv : (n : Nat) → BitVec n → V)

/-- The bit-vector that a value is, if it is one. -/
noncomputable def decBV (o : Option V) : Option (Σ n, BitVec n) :=
  if h : ∃ n x, o = some (vbv n x) then some ⟨h.choose, h.choose_spec.choose⟩ else none

/-- A unary operation on a bit-vector; poison otherwise. -/
noncomputable def bvUn (f : (n : Nat) → BitVec n → Option V) (a : Option V) : Option V :=
  match decBV vbv a with
  | some ⟨n, x⟩ => f n x
  | none => none

variable {vbv}

theorem decBV_some (inj : ∀ n m (x : BitVec n) (y : BitVec m), vbv n x = vbv m y →
      (⟨n, x⟩ : Σ n, BitVec n) = ⟨m, y⟩) (n : Nat) (x : BitVec n) :
    decBV vbv (some (vbv n x)) = some ⟨n, x⟩ := by
  have h : ∃ m y, some (vbv n x) = some (vbv m y) := ⟨n, x, rfl⟩
  rw [decBV, dif_pos h]
  have := h.choose_spec.choose_spec
  exact congrArg some (inj _ _ _ _ (Option.some.inj this)).symm

theorem decBV_none : decBV vbv none = none := by
  rw [decBV, dif_neg]; rintro ⟨_, _, h⟩; cases h

end

end BitvecMod
