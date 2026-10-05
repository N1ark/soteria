import PtrMod.Statements
import BitvecMod.Lib.Lift
import BitvecMod.Lib.Cong

/-!
# Refinement by congruence

The congruence lemmas of the nodes of the ptr module, with which `kanon_congr`
proves that the specs are monotone (`Lifts.lean`): the nodes are strict in
their operands (`BitvecMod.Lib.refines_node1`, …).
-/

namespace PtrMod

open Classical Kanon Kanon.Sem BitvecMod.Lib

set_option linter.unusedSectionVars false

attribute [bv_wt] Syntax.WT_Ptr Syntax.WT_GetPtrLoc Syntax.WT_GetPtrOfs

namespace Lib

variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
  {LBool : KanonBool.Syntax B} {LCore : CoreMod.Syntax B}
  {LBitvec : BitvecMod.Syntax B LBool LCore} {L : Syntax B LBool LCore LBitvec}
  [KanonBool.Sem LBool] [CoreMod.Sem LCore] [BitvecMod.Sem LBitvec] [Sem L]
  {a a' b b' : S.Term} {t t' : S.Ty}

theorem bvUn_none {V : Type} {vbv : (n : Nat) → BitVec n → V} {f} :
    BitvecMod.bvUn vbv f none = none := by simp [BitvecMod.bvUn, BitvecMod.decBV_none]

theorem bvUn_none_fun {V : Type} {vbv : (n : Nat) → BitVec n → V} (o : Option V) :
    BitvecMod.bvUn vbv (fun _ _ => none) o = none := by
  simp only [BitvecMod.bvUn]; split <;> rfl

theorem refines_ptr (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.PtrK a b) t) → t' = t) :
    S.Refines (B.node (L.PtrK a b) t) (B.node (L.PtrK a' b') t') :=
  refines_node2 L.WT_Ptr (fun _ _ _ _ _ ha hb q => by simp only [ha, hb]; exact q)
    (F := fun oa ob => BitvecMod.bvUn (BitvecMod.Sem.vbv LBitvec)
      (fun n l => BitvecMod.bvUn (BitvecMod.Sem.vbv LBitvec)
        (fun m o => if h : m = n then some (Sem.vptr L n l (h ▸ o)) else none) ob) oa)
    (fun _ => bvUn_none)
    (fun o => by simp only [bvUn_none]; exact bvUn_none_fun o) Sem.ev_Ptr ha hb ht

theorem refines_getPtrLoc (ha : S.Refines a a')
    (ht : S.WT (B.node (L.GetPtrLocK a) t) → t' = t) :
    S.Refines (B.node (L.GetPtrLocK a) t) (B.node (L.GetPtrLocK a') t') :=
  refines_node1 L.WT_GetPtrLoc (fun _ _ _ h q => by simp only [h]; exact q)
    (F := fun o => (decPtr (Sem.vptr L) o).map fun p => BitvecMod.Sem.vbv LBitvec p.1 p.2.1)
    (by simp only [decPtr_none]; rfl) Sem.ev_GetPtrLoc ha ht

theorem refines_getPtrOfs (ha : S.Refines a a')
    (ht : S.WT (B.node (L.GetPtrOfsK a) t) → t' = t) :
    S.Refines (B.node (L.GetPtrOfsK a) t) (B.node (L.GetPtrOfsK a') t') :=
  refines_node1 L.WT_GetPtrOfs (fun _ _ _ h q => by simp only [h]; exact q)
    (F := fun o => (decPtr (Sem.vptr L) o).map fun p => BitvecMod.Sem.vbv LBitvec p.1 p.2.2)
    (by simp only [decPtr_none]; rfl) Sem.ev_GetPtrOfs ha ht

attribute [kanon_congr_lemma] refines_ptr refines_getPtrLoc refines_getPtrOfs

end Lib

/-- The side goals of the congruence lemmas of the ptr module. -/
macro_rules | `(tactic| kanon_congr_side) => `(tactic|
  (intro w
   simp only [Syntax.WT_Ptr, Syntax.WT_GetPtrLoc, Syntax.WT_GetPtrOfs] at w
   kanon_split
   first
     | exact Kanon.Sem.ty_refines (by assumption) (by assumption)
     | (congr 1; rw [Kanon.Sem.ty_refines (by assumption) (by assumption)])))

end PtrMod
