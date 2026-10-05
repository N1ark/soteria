import CoreMod.FBits
import BitvecMod.Val

/-!
# Floats among values

The float module evaluates its nodes with the operations below, on the values
of their operands (`none` for poison), given the floats among the values of the
language (`vf`): `decF vf o` is the float (its precision and bit pattern) that
the value `o` is, if any.
-/

namespace FloatMod

open Classical CoreMod

variable {V : Type} (vf : (p : Fp) → FBits p → V)

/-- The float that a value is, if it is one. -/
noncomputable def decF (o : Option V) : Option (Σ p, FBits p) :=
  if h : ∃ p x, o = some (vf p x) then some ⟨h.choose, h.choose_spec.choose⟩ else none

/-- A unary operation on a float; poison otherwise. -/
noncomputable def fUn (f : (p : Fp) → FBits p → Option V) (a : Option V) : Option V :=
  match decF vf a with
  | some ⟨p, x⟩ => f p x
  | none => none

/-- A binary operation on floats of the same precision; poison otherwise. -/
noncomputable def fBin (f : (p : Fp) → FBits p → FBits p → Option V) (a b : Option V) :
    Option V :=
  match decF vf a, decF vf b with
  | some ⟨p, x⟩, some ⟨q, y⟩ => if h : q = p then f p x (h ▸ y) else none
  | _, _ => none

/-- A ternary operation on floats of the same precision; poison otherwise. -/
noncomputable def fTern (f : (p : Fp) → FBits p → FBits p → FBits p → Option V)
    (a b c : Option V) : Option V :=
  match decF vf a, decF vf b, decF vf c with
  | some ⟨p, x⟩, some ⟨q, y⟩, some ⟨r, z⟩ =>
    if h : q = p ∧ r = p then f p x (h.1 ▸ y) (h.2 ▸ z) else none
  | _, _, _ => none

variable {vf}

section
variable (inj : ∀ p q (x : FBits p) (y : FBits q), vf p x = vf q y →
  (⟨p, x⟩ : Σ p, FBits p) = ⟨q, y⟩)
include inj

theorem decF_some (p : Fp) (x : FBits p) : decF vf (some (vf p x)) = some ⟨p, x⟩ := by
  have h : ∃ q y, some (vf p x) = some (vf q y) := ⟨p, x, rfl⟩
  rw [decF, dif_pos h]
  have := h.choose_spec.choose_spec
  exact congrArg some (inj _ _ _ _ (Option.some.inj this)).symm

theorem fUn_some {f} (p : Fp) (x : FBits p) : fUn vf f (some (vf p x)) = f p x := by
  rw [fUn, decF_some inj]

theorem fBin_some {f} (p : Fp) (x y : FBits p) :
    fBin vf f (some (vf p x)) (some (vf p y)) = f p x y := by
  rw [fBin, decF_some inj, decF_some inj]; simp

theorem fTern_some {f} (p : Fp) (x y z : FBits p) :
    fTern vf f (some (vf p x)) (some (vf p y)) (some (vf p z)) = f p x y z := by
  rw [fTern, decF_some inj, decF_some inj, decF_some inj]; simp

end

@[simp] theorem decF_none : decF vf none = none := by
  rw [decF, dif_neg]; rintro ⟨_, _, h⟩; cases h

@[simp] theorem fUn_none {f} : fUn vf f none = none := by simp [fUn]
@[simp] theorem fBin_none_l {f} (b : Option V) : fBin vf f none b = none := by simp [fBin]
@[simp] theorem fBin_none_r {f} (a : Option V) : fBin vf f a none = none := by
  simp only [fBin, decF_none]; split <;> simp_all

end FloatMod
