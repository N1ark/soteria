import KanonCore.Proof
import BitvecMod.Statements
import BitvecMod.Lib.Attr

/-!
# Terms by their structural values

`Sem.den L ρ n t` is the value of a bit-vector term `t` at width `n`, and
`Sem.denB L ρ t` the value of a boolean term, computed by the structure of the
term (`Sem.den_Add`, …, the simp set `bv_den`); on well-typed terms they are
their values (`Sem.den_iff`, `Sem.denB_iff`), so refinements reduce to them
(`Refines.den`, `Refines.denB`).

The lemmas of the module's proofs are in the namespace `BitvecMod.Lib`, over
the variables below.
-/

namespace BitvecMod

open Classical Kanon Kanon.Sem

attribute [bv_den] Sem.den_BitVec Sem.den_Add Sem.den_Sub Sem.den_Mul Sem.den_Div Sem.den_Rem
  Sem.den_Mod Sem.den_BitAnd Sem.den_BitOr Sem.den_BitXor Sem.den_Shl Sem.den_LShr Sem.den_AShr
  Sem.den_BvConcat Sem.den_Neg Sem.den_BvNot Sem.den_BvOfBool Sem.den_BvExtend
  Sem.den_BvExtract Sem.den_Ite Sem.denB_Bool Sem.denB_Not Sem.denB_And Sem.denB_Or
  Sem.denB_Ite Sem.denB_Eq Sem.denB_Lt Sem.denB_Leq Sem.denB_AddOvf Sem.denB_SubOvf
  Sem.denB_MulOvf

set_option linter.unusedSectionVars false

namespace Lib

variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
  {LBool : KanonBool.Syntax B} {LCore : CoreMod.Syntax B} {L : Syntax B LBool LCore}
  [KanonBool.Sem LBool] [CoreMod.Sem LCore] [Sem L]

/-! ## The sorts -/

@[simp] theorem TBitVector_inj_iff {n m : Int} : L.TBitVector n = L.TBitVector m ↔ n = m :=
  ⟨L.TBitVector_inj n m, fun h => h ▸ rfl⟩

@[simp] theorem TLoc_inj_iff {n m : Int} : L.TLoc n = L.TLoc m ↔ n = m :=
  ⟨L.TLoc_inj n m, fun h => h ▸ rfl⟩

@[simp] theorem TBitVector_ne_TBool {n : Int} : L.TBitVector n ≠ LBool.TBool :=
  L.TBitVector_ne_TBool n

@[simp] theorem TBool_ne_TBitVector {n : Int} : LBool.TBool ≠ L.TBitVector n :=
  fun h => L.TBitVector_ne_TBool n h.symm

@[simp] theorem TBitVector_ne_TLoc {n m : Int} : L.TBitVector n ≠ L.TLoc m :=
  L.TBitVector_ne_TLoc n m

@[simp] theorem TLoc_ne_TBitVector {n m : Int} : L.TLoc m ≠ L.TBitVector n :=
  fun h => L.TBitVector_ne_TLoc n m h.symm

/-! ## Values -/

/-- The values of bit-vectors determine their widths and bits. -/
theorem vbv_sigma_inj : ∀ n m (x : BitVec n) (y : BitVec m),
    Sem.vbv L n x = Sem.vbv L m y → (⟨n, x⟩ : Σ n, BitVec n) = ⟨m, y⟩ := by
  intro n m x y h
  by_cases hn : n = m
  · subst hn; rw [Sem.vbv_inj n x y h]
  · exact absurd h (Sem.vbv_ne n m x y hn)

/-- A term of a non-positive width has no value. -/
theorem ev_bv_none {ρ : S.Env} {t : S.Term} {m : Int} (w : S.WT t)
    (hty : S.ty t = L.TBitVector m) (hm : ¬ 0 < m) : S.ev ρ t = none := by
  cases e : S.ev ρ t with
  | none => rfl
  | some v => exact absurd (Sem.ev_bv ρ t v m w hty e).1 hm

/-- The value half of a refinement on bit-vector terms, on their structural
values. -/
theorem den_of {a a' : S.Term} (h : S.Refines a a') (w : S.WT a) {n : Nat}
    (ht : S.ty a = L.TBitVector n) (ρ : S.Env) : OLe (Sem.den L ρ n a) (Sem.den L ρ n a') := by
  intro x e
  obtain ⟨w', s'⟩ := h.syn w
  rw [Sem.den_iff ρ n a x w ht] at e
  rw [Sem.den_iff ρ n a' x w' (s'.trans ht)]
  exact h.ev w ρ _ e

/-- The value half of a refinement on boolean terms, on their structural
values. -/
theorem denB_of {a a' : S.Term} (h : S.Refines a a') (w : S.WT a)
    (ht : S.ty a = LBool.TBool) (ρ : S.Env) : OLe (Sem.denB L ρ a) (Sem.denB L ρ a') := by
  intro x e
  obtain ⟨w', s'⟩ := h.syn w
  rw [Sem.denB_iff ρ a x w ht] at e
  rw [Sem.denB_iff ρ a' x w' (s'.trans ht)]
  exact h.ev w ρ _ e

/-- Refinement of bit-vector terms, by their structural values. -/
theorem Refines.den {s r : S.Term}
    (hty : S.WT s → ∃ n : Int, S.ty s = L.TBitVector n)
    (syn : S.WT s → S.WT r ∧ S.ty r = S.ty s)
    (sem : ∀ n : Nat, S.WT s → S.ty s = L.TBitVector n →
      ∀ ρ x, Sem.den L ρ n s = some x → Sem.den L ρ n r = some x) :
    S.Refines s r := by
  refine Kanon.Sem.Refines.intro syn (fun ρ v w w' e => ?_)
  obtain ⟨m, hm⟩ := hty w
  obtain ⟨hpos, x, rfl⟩ := Sem.ev_bv ρ s v m w hm e
  have hm' : S.ty s = L.TBitVector (m.toNat : Nat) := by rw [hm, Int.toNat_of_nonneg (by omega)]
  rw [← Sem.den_iff ρ _ s x w hm'] at e
  rw [← Sem.den_iff ρ _ r x w' ((syn w).2.trans hm')]
  exact sem _ w hm' ρ x e

/-- Refinement of boolean terms, by their structural values. -/
theorem Refines.denB {s r : S.Term}
    (hty : S.WT s → S.ty s = LBool.TBool)
    (syn : S.WT s → S.WT r ∧ S.ty r = S.ty s)
    (sem : S.WT s → ∀ ρ b, Sem.denB L ρ s = some b → Sem.denB L ρ r = some b) :
    S.Refines s r := by
  refine Kanon.Sem.Refines.intro syn (fun ρ v w w' e => ?_)
  obtain ⟨b, rfl⟩ := KanonBool.Sem.ev_bool ρ s v w (hty w) e
  rw [← Sem.denB_iff (L := L) ρ s b w (hty w)] at e
  rw [← Sem.denB_iff (L := L) ρ r b w' ((syn w).2.trans (hty w))]
  exact sem w ρ b e

/-! ## Monotonicity of the operations in poison -/

theorem ckOp_mono {n c sovf uovf f} {a a' b b' : Option (BitVec n)} (ha : OLe a a')
    (hb : OLe b b') : OLe (ckOp c sovf uovf f a b) (ckOp c sovf uovf f a' b') := by
  intro v e
  rcases a with _ | x <;> rcases b with _ | y <;> simp at e
  rw [ha x rfl, hb y rfl]; simpa using e

theorem binOp_mono {n f} {a a' b b' : Option (BitVec n)} (ha : OLe a a') (hb : OLe b b') :
    OLe (binOp f a b) (binOp f a' b') := by
  intro v e
  rcases a with _ | x <;> rcases b with _ | y <;> simp at e
  rw [ha x rfl, hb y rfl]; simpa using e

theorem negOp_mono {n c} {a a' : Option (BitVec n)} (ha : OLe a a') :
    OLe (negOp c a) (negOp c a') := by
  intro v e
  rcases a with _ | x <;> simp at e
  rw [ha x rfl]; simpa using e

theorem map_mono {α β : Type} {f : α → β} {a a' : Option α} (ha : OLe a a') :
    OLe (a.map f) (a'.map f) := by
  intro v e
  rcases a with _ | x <;> simp at e
  rw [ha x rfl]; simpa using e

theorem binB_mono {α f} {a a' b b' : Option α} (ha : OLe a a') (hb : OLe b b') :
    OLe (binB f a b) (binB f a' b') := by
  intro v e
  rcases a with _ | x <;> rcases b with _ | y <;> simp at e
  rw [ha x rfl, hb y rfl]; simpa using e

end Lib

end BitvecMod
