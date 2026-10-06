import Kanon.Interface.Ptr
import Kanon.Lang.Bitvec
import PtrMod.Sem

/-!
# The language, for the ptr module

The ptr module is proved once (`PtrMod`): the language gives its interface
(`ptrSyntax`) and what it needs of its semantics, its pointer values and the
evaluation of its nodes.
-/

namespace Kanon

open Classical Lib

variable (FS : FloatSem)

namespace Lang

theorem vptr_inj : ∀ n m (l o : BitVec n) (l' o' : BitVec m), Val.ptr n l o = Val.ptr m l' o' →
    (⟨n, l, o⟩ : Σ n, BitVec n × BitVec n) = ⟨m, l', o'⟩ := by
  intro n m l o l' o' h; cases h; rfl

/-- The pointer that a value of the language is. -/
theorem decPtr_eq (v : Val) : PtrMod.decPtr Val.ptr (some v) =
    match v with
    | .ptr n l o => some ⟨n, l, o⟩
    | _ => none := by
  cases v with
  | ptr n l o => exact PtrMod.decPtr_some vptr_inj n l o
  | _ => rw [PtrMod.decPtr, dif_neg]; rintro ⟨_, _, _, h⟩; cases h

end Lang

/-- What the ptr module needs of the semantics. -/
noncomputable instance ptrSem : PtrMod.Sem (S := sem FS) (ptrSyntax FS) where
  vptr := Val.ptr
  vptr_inj := Lang.vptr_inj
  vptr_ne_vbool _ _ _ _ e := by cases e
  vptr_ne_vbv _ _ _ _ _ e := by cases e
  ev_ptr ρ t v m w ht e := by
    have := ev_hasSort t w v e
    simp only [ptrSyntax, sem] at ht
    rw [ht] at this
    rcases v with _ | _ | ⟨k, l, o⟩ | _ | _ | _ <;> simp [Val.hasSort] at this
    obtain ⟨rfl, hk⟩ := this
    exact ⟨by omega, l, o, by simp⟩
  ev_Ptr ρ a b t := by
    simp only [bitvecSem_vbv']
    simp only [ptrSyntax, modBase, sem, ev, evOp2, BitvecMod.bvUn]
    rcases ev FS ρ a with _ | va
    · simp [evPtr, BitvecMod.decBV_none]
    rcases ev FS ρ b with _ | vb
    · rcases va <;> simp [evPtr, Lang.decBV_eq, BitvecMod.decBV_none]
    rcases va <;> rcases vb <;> simp [evPtr, Lang.decBV_eq]
  ev_GetPtrLoc ρ a t := by
    simp only [bitvecSem_vbv']
    simp only [ptrSyntax, modBase, sem, ev, evOp1]
    rcases ev FS ρ a with _ | va
    · simp
    · rcases va <;> simp [Lang.decPtr_eq]
  ev_GetPtrOfs ρ a t := by
    simp only [bitvecSem_vbv']
    simp only [ptrSyntax, modBase, sem, ev, evOp1]
    rcases ev FS ρ a with _ | va
    · simp
    · rcases va <;> simp [Lang.decPtr_eq]
  size_of_ty_TPointer _ := rfl

end Kanon
