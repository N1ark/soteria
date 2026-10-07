import Kanon.Syntax
import ExistsMod.Sem
import FloatMod.Sem
import PtrMod.Sem

/-!
# The values of the language

Booleans, bit-vectors (of the sorts of bit-vectors and of locations), pointers
(a location and an offset), floats (IEEE bit patterns) and sequences. An
environment gives each variable a value, or none (poison). The floating-point
arithmetic is opaque: the proofs hold of any (option B's `FloatSem`).
-/

noncomputable section

namespace Kanon

open CoreMod

/-- The values of the language. -/
inductive Val where
  | bool (b : Bool)
  | bv (n : Nat) (x : BitVec n)
  | ptr (n : Nat) (l o : BitVec n)
  | float (p : Fp) (x : FBits p)
  | seq (vs : List Val)

mutual
/-- The values of a sort. -/
def Val.Of : Val → Ty → Prop
  | .bool _, t => t = .bool .TBool
  | .bv n _, t => 0 < n ∧ (t = .bitvec (.TBitVector n) ∨ t = .bitvec (.TLoc n))
  | .ptr n _ _, t => 0 < n ∧ t = .ptr (.TPointer n)
  | .float p _, t => t = .float (.TFloat p)
  | .seq vs, t => ∃ e, t = .core (.TSeq e) ∧ Val.OfAll vs e

/-- The values all of a sort. -/
def Val.OfAll : List Val → Ty → Prop
  | [], _ => True
  | v :: vs, e => v.Of e ∧ Val.OfAll vs e
end

theorem Val.ofAll_iff : ∀ (vs : List Val) (e : Ty), Val.OfAll vs e ↔ ∀ v ∈ vs, v.Of e
  | [], _ => by simp [Val.OfAll]
  | v :: vs, e => by simp [Val.OfAll, Val.ofAll_iff vs e]

/-- The values of the variables; `none` for a poisoned variable. -/
abbrev Env := Int → Option Val

/-- The sorts, values and environments of the language. -/
abbrev dom : Kanon.Dom := { Ty := Ty, Val := Val, Env := Env }

/-- The width of a sort of bit-vectors, locations or pointers. -/
def Ty.width : Ty → Nat
  | .bitvec (.TBitVector n) | .bitvec (.TLoc n) | .ptr (.TPointer n) => n.toNat
  | _ => 0

/-- The environments that give the binders `bs` values of their sorts, and
agree with `ρ` on the other variables. -/
def Extends (ρ' ρ : Env) (bs : List (Int × Ty)) : Prop :=
  (∀ x, (∀ b ∈ bs, b.1 ≠ x) → ρ' x = ρ x) ∧ ∀ b ∈ bs, ∃ v, ρ' b.1 = some v ∧ v.Of b.2

/-! The floating-point arithmetic, opaque. -/
opaque fadd : (p : Fp) → FBits p → FBits p → FBits p
opaque fsub : (p : Fp) → FBits p → FBits p → FBits p
opaque fmul : (p : Fp) → FBits p → FBits p → FBits p
opaque fdiv : (p : Fp) → FBits p → FBits p → FBits p
opaque frem : (p : Fp) → FBits p → FBits p → FBits p
opaque fmin : (p : Fp) → FBits p → FBits p → FBits p
opaque fmax : (p : Fp) → FBits p → FBits p → FBits p
opaque ffma : (p : Fp) → FBits p → FBits p → FBits p → FBits p
opaque fsqrt : (p : Fp) → FBits p → FBits p
opaque fround : Rm → (p : Fp) → FBits p → FBits p
opaque fconvert : Rm → (p q : Fp) → FBits p → FBits q
opaque ftoBv : Rm → Bool → (n : Nat) → (p : Fp) → FBits p → BitVec n
opaque fofBv : Rm → Bool → (p : Fp) → (n : Nat) → BitVec n → FBits p

instance : KanonBool.Values dom where
  vbool := { inj := .bool, proj := fun | .bool b => some b | _ => none,
             proj_inj := fun _ => rfl,
             inj_proj := by intro v b h; cases v <;> cases h <;> rfl }

instance : CoreMod.Values dom where
  lookup ρ x := ρ x
  Of := Val.Of
  vseq := { inj := .seq, proj := fun | .seq vs => some vs | _ => none,
            proj_inj := fun _ => rfl,
            inj_proj := by intro v vs h; cases v <;> cases h <;> rfl }

instance : ExistsMod.Values dom where
  Extends := Extends
  extends_nil ρ' ρ := by
    simp only [Extends, List.not_mem_nil, false_implies, implies_true, true_implies, and_true]
    exact ⟨funext, fun h _ => h ▸ rfl⟩

instance : BitvecMod.Values dom where
  vbv := { inj := fun p => .bv p.1 p.2, proj := fun | .bv n x => some ⟨n, x⟩ | _ => none,
           proj_inj := fun _ => rfl,
           inj_proj := by intro v p h; cases v <;> cases h <;> rfl }
  width := Ty.width

instance : FloatMod.Values dom where
  vfloat := { inj := fun p => .float p.1 p.2, proj := fun | .float p x => some ⟨p, x⟩ | _ => none,
              proj_inj := fun _ => rfl,
              inj_proj := by intro v p h; cases v <;> cases h <;> rfl }
  add := fadd
  sub := fsub
  mul := fmul
  div := fdiv
  rem := frem
  min := fmin
  max := fmax
  fma := ffma
  sqrt := fsqrt
  round := fround
  convert := fconvert
  toBv := ftoBv
  ofBv := fofBv

instance : PtrMod.Values dom where
  vptr := { inj := fun p => .ptr p.1 p.2.1 p.2.2,
            proj := fun | .ptr n l o => some ⟨n, l, o⟩ | _ => none,
            proj_inj := fun _ => rfl,
            inj_proj := by intro v p h; cases v <;> cases h <;> rfl }

end Kanon
