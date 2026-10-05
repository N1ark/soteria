import Kanon.Interface.Bool
import Kanon.Lib.Bool

/-!
# The language, for the bool module

The bool module is proved once (`KanonBool`): the language gives its interface
(`boolSyntax`, generated in `Interface/Bool.lean`) and what it needs of its
semantics, the instance of its `Sem` class. The laws that are more than the
evaluation of the nodes are proved in `Lib/Bool.lean`: that well-typed booleans
evaluate to booleans, and that the terms that `Bool.sure_neq` tells apart have
different values.
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

end Kanon
