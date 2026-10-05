import Kanon.Interface
import Kanon.Lib.Bool
import CoreMod.Sem
import ExistsMod.Sem

/-!
# The language, for its modules

The bool, core and exists modules are proved once (`KanonBool`, `CoreMod`,
`ExistsMod`): the language gives their interfaces (`boolSyntax`, …, generated
in `Interface.lean`) and what they need of its semantics, the instances of
their `Sem` classes. The laws that are more than the evaluation of the nodes
are proved in `Lib/Bool.lean`: that well-typed booleans evaluate to booleans,
that the terms that `Bool.sure_neq` tells apart have different values, and
that the binders of an `Exists` that its body does not use do not matter.
-/

namespace Kanon

open Classical KanonBool Lib

variable (FS : FloatSem)

/-- What the bool module needs of the semantics. -/
instance boolSem : KanonBool.Sem (S := sem FS) (boolSyntax FS) where
  vbool := .bool
  ev_Bool _ _ _ := by simp only [boolSyntax, modBase, sem, ev]
  ev_Not _ _ _ := by simp only [boolSyntax, modBase, sem, ev]; rfl
  ev_And _ _ _ _ := by simp only [boolSyntax, modBase, sem, ev]; rfl
  ev_Or _ _ _ _ := by simp only [boolSyntax, modBase, sem, ev]; rfl
  ev_Eq _ _ _ _ := by simp only [boolSyntax, modBase, sem, ev]; rfl
  ev_Ite _ _ _ _ _ := by simp only [boolSyntax, modBase, sem, ev]; rfl
  ev_Distinct _ _ _ := by simp [boolSyntax, modBase, sem, ev, evOpN, evList_eq]
  ev_bool _ t v w ht e := by
    have := ev_hasSort t w v e
    simp only [boolSyntax, sem] at ht
    rw [ht] at this
    rcases v with b | _ | _ | _ | _ | _ <;> simp_all [Val.hasSort]
  sure_neq_sound _ _ _ _ h ht wa wb ea eb :=
    sure_neq_sound h ht (by rw [eval_eq_ev wa]; exact ea) (by rw [eval_eq_ev wb]; exact eb)

/-- The core module needs nothing of the semantics. -/
instance coreSem : CoreMod.Sem (S := sem FS) (coreSyntax FS) := {}

/-- What the exists module needs of the semantics. -/
instance existsSem : ExistsMod.Sem (S := sem FS) (existsSyntax FS) where
  TyWF := Ty.WF
  Extends ρ' ρ bs := ρ'.Extends ρ bs
  extends_nil _ _ := extends_nil
  exists_wf_Exists _ _ _ := by simp [existsSyntax, boolSyntax, modBase, sem, exists_wf]
  ev_Exists _ _ _ _ := by simp only [existsSyntax, boolSyntax, modBase, sem, ev]; rfl
  used_binders_sublist _ _ := List.filter_sublist
  ev_used_binders _ _ _ t t' hn hw := ev_exists_used (T := t) (T' := t') hn hw

end Kanon
