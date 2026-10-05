import BitvecMod.Sem
import PtrMod.Syntax

/-!
# What the ptr module needs of the semantics of a language

A pointer is a location and an offset, bit-vectors of the same width. The
module needs, of the semantics `S` of a language, the pointers among the
values (`vptr`), which are different from each other and from the booleans and
bit-vectors, which the well-typed pointer terms evaluate to (`ev_ptr`), and the
evaluation of its nodes (`ev_Ptr`, …), by the operations below on the values of
their operands.
-/

namespace PtrMod

open Classical Kanon

section
variable {V : Type} (vptr : (n : Nat) → BitVec n → BitVec n → V)

/-- The pointer that a value is (its width, location and offset), if it is
one. -/
noncomputable def decPtr (o : Option V) : Option (Σ n, BitVec n × BitVec n) :=
  if h : ∃ n l o', o = some (vptr n l o') then
    some ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose⟩
  else none

variable {vptr}

theorem decPtr_some (inj : ∀ n m (l o : BitVec n) (l' o' : BitVec m),
      vptr n l o = vptr m l' o' → (⟨n, l, o⟩ : Σ n, BitVec n × BitVec n) = ⟨m, l', o'⟩)
    (n : Nat) (l o : BitVec n) : decPtr vptr (some (vptr n l o)) = some ⟨n, l, o⟩ := by
  have h : ∃ m l' o', some (vptr n l o) = some (vptr m l' o') := ⟨n, l, o, rfl⟩
  rw [decPtr, dif_pos h]
  have := h.choose_spec.choose_spec.choose_spec
  exact congrArg some (inj _ _ _ _ _ _ (Option.some.inj this)).symm

@[simp] theorem decPtr_none : decPtr vptr none = none := by
  rw [decPtr, dif_neg]; rintro ⟨_, _, _, h⟩; cases h

end

/-- What the ptr module needs of the semantics `S` of a language, for its
interface `L`. -/
class Sem {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
    {LBool : KanonBool.Syntax B} {LCore : CoreMod.Syntax B}
    {LBitvec : BitvecMod.Syntax B LBool LCore} (L : Syntax B LBool LCore LBitvec)
    [KanonBool.Sem LBool] [CoreMod.Sem LCore] [BitvecMod.Sem LBitvec] where
  /-- The pointer values. -/
  vptr : (n : Nat) → BitVec n → BitVec n → S.Val
  vptr_inj : ∀ n m (l o : BitVec n) (l' o' : BitVec m), vptr n l o = vptr m l' o' →
    (⟨n, l, o⟩ : Σ n, BitVec n × BitVec n) = ⟨m, l', o'⟩
  vptr_ne_vbool : ∀ n (l o : BitVec n) b, vptr n l o ≠ KanonBool.Sem.vbool LBool b
  vptr_ne_vbv : ∀ n (l o : BitVec n) m (x : BitVec m), vptr n l o ≠ BitvecMod.Sem.vbv LBitvec m x
  /-- Well-typed pointers evaluate to pointers of their width. -/
  ev_ptr : ∀ ρ t v m, S.WT t → S.ty t = L.TPointer m → S.ev ρ t = some v →
    0 < m ∧ ∃ l o, v = vptr m.toNat l o
  ev_Ptr : ∀ ρ a b t, S.ev ρ (B.node (L.PtrK a b) t) =
    BitvecMod.bvUn (BitvecMod.Sem.vbv LBitvec)
      (fun n l => BitvecMod.bvUn (BitvecMod.Sem.vbv LBitvec)
        (fun m o => if h : m = n then some (vptr n l (h ▸ o)) else none) (S.ev ρ b))
      (S.ev ρ a)
  ev_GetPtrLoc : ∀ ρ a t, S.ev ρ (B.node (L.GetPtrLocK a) t) =
    (decPtr vptr (S.ev ρ a)).map fun p => BitvecMod.Sem.vbv LBitvec p.1 p.2.1
  ev_GetPtrOfs : ∀ ρ a t, S.ev ρ (B.node (L.GetPtrOfsK a) t) =
    (decPtr vptr (S.ev ρ a)).map fun p => BitvecMod.Sem.vbv LBitvec p.1 p.2.2
  size_of_ty_TPointer : ∀ n, LBitvec.bitvec_size_of_ty (L.TPointer n) = n

end PtrMod
