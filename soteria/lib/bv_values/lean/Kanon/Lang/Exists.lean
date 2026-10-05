import Kanon.Interface.Exists
import Kanon.Lang.Bool
import Kanon.Lang.Core
import ExistsMod.Sem

/-!
# The language, for the exists module

The exists module is proved once (`ExistsMod`). Besides the evaluation of its
node, it needs that the binders of an `Exists` that its body does not use do
not matter (`Lib/Bool.lean`).
-/

namespace Kanon

open Classical Lib

variable (FS : FloatSem)

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
