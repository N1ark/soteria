import PtrMod.Lib.Lift

/-!
# Pointers by evaluation

A well-typed `Ptr l o` evaluates to the pointer of the values of `l` and `o`
(`ev_Ptr_of`), so its location and offset are `l` and `o`
(`Refines.loc_ptr`, `Refines.ofs_ptr`).
-/

namespace PtrMod

open Classical Kanon Kanon.Sem

set_option linter.unusedSectionVars false

namespace Lib

variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
  {LBool : KanonBool.Syntax B} {LCore : CoreMod.Syntax B}
  {LBitvec : BitvecMod.Syntax B LBool LCore} {L : Syntax B LBool LCore LBitvec}
  [KanonBool.Sem LBool] [CoreMod.Sem LCore] [BitvecMod.Sem LBitvec] [Sem L]

theorem vbv_inj' : ∀ n m (x : BitVec n) (y : BitVec m),
    BitvecMod.Sem.vbv LBitvec n x = BitvecMod.Sem.vbv LBitvec m y →
    (⟨n, x⟩ : Σ n, BitVec n) = ⟨m, y⟩ := by
  intro n m x y h
  by_cases hn : n = m
  · subst hn; rw [BitvecMod.Sem.vbv_inj n x y h]
  · exact absurd h (BitvecMod.Sem.vbv_ne n m x y hn)

/-- The value of a well-typed pointer whose location and offset have values. -/
theorem ev_Ptr_of {ρ : S.Env} {l o : S.Term} {t : S.Ty} (w : S.WT (B.node (L.PtrK l o) t))
    {v : S.Val} (e : S.ev ρ (B.node (L.PtrK l o) t) = some v) :
    ∃ n x y, S.ev ρ l = some (BitvecMod.Sem.vbv LBitvec n x) ∧
      S.ev ρ o = some (BitvecMod.Sem.vbv LBitvec n y) ∧ v = Sem.vptr L n x y := by
  obtain ⟨⟨m, -, hl, ho, -⟩, wl, wo⟩ := (L.WT_Ptr _ _ _).1 w
  rw [Sem.ev_Ptr] at e
  cases el : S.ev ρ l with
  | none => rw [el] at e; simp [BitvecMod.bvUn, BitvecMod.decBV_none] at e
  | some vl =>
  cases eo : S.ev ρ o with
  | none =>
    rw [el, eo] at e
    obtain ⟨-, x, rfl⟩ := BitvecMod.Sem.ev_loc ρ l vl m wl hl el
    simp [BitvecMod.bvUn, BitvecMod.decBV_some vbv_inj', BitvecMod.decBV_none] at e
  | some vo =>
    rw [el, eo] at e
    obtain ⟨-, x, rfl⟩ := BitvecMod.Sem.ev_loc ρ l vl m wl hl el
    obtain ⟨-, y, rfl⟩ := BitvecMod.Sem.ev_bv ρ o vo m wo ho eo
    simp only [BitvecMod.bvUn, BitvecMod.decBV_some vbv_inj', dite_true,
      Option.some.injEq] at e
    exact ⟨_, x, y, rfl, rfl, e.symm⟩

theorem decPtr_vptr (n : Nat) (x y : BitVec n) :
    decPtr (Sem.vptr L) (some (Sem.vptr L n x y)) = some ⟨n, x, y⟩ :=
  decPtr_some Sem.vptr_inj n x y

/-- The location of a pointer. -/
theorem Refines.loc_ptr {l o : S.Term} {t t' : S.Ty} :
    S.Refines (B.node (L.GetPtrLocK (B.node (L.PtrK l o) t)) t') l := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;>
    obtain ⟨⟨n, -, hp, ht⟩, wp⟩ := (L.WT_GetPtrLoc _ _).1 w <;>
    obtain ⟨⟨m, -, hl, -, ht4⟩, wl, -⟩ := (L.WT_Ptr _ _ _).1 wp
  · rw [B.ty_node, ht4] at hp
    refine ⟨wl, ?_⟩
    rw [hl, B.ty_node, ht, L.TPointer_inj _ _ hp]
  · rw [Sem.ev_GetPtrLoc] at e
    cases ep : S.ev ρ (B.node (L.PtrK l o) t) with
    | none => rw [ep] at e; simp at e
    | some vp =>
      obtain ⟨k, x, y, el, -, rfl⟩ := ev_Ptr_of wp ep
      rw [ep, decPtr_vptr] at e
      simp only [Option.map_some, Option.some.injEq] at e
      rw [el, e]

/-- The offset of a pointer. -/
theorem Refines.ofs_ptr {l o : S.Term} {t t' : S.Ty} :
    S.Refines (B.node (L.GetPtrOfsK (B.node (L.PtrK l o) t)) t') o := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;>
    obtain ⟨⟨n, -, hp, ht⟩, wp⟩ := (L.WT_GetPtrOfs _ _).1 w <;>
    obtain ⟨⟨m, -, -, ho, ht4⟩, -, wo⟩ := (L.WT_Ptr _ _ _).1 wp
  · rw [B.ty_node, ht4] at hp
    refine ⟨wo, ?_⟩
    rw [ho, B.ty_node, ht, L.TPointer_inj _ _ hp]
  · rw [Sem.ev_GetPtrOfs] at e
    cases ep : S.ev ρ (B.node (L.PtrK l o) t) with
    | none => rw [ep] at e; simp at e
    | some vp =>
      obtain ⟨k, x, y, -, eo, rfl⟩ := ev_Ptr_of wp ep
      rw [ep, decPtr_vptr] at e
      simp only [Option.map_some, Option.some.injEq] at e
      rw [eo, e]

end Lib

end PtrMod
