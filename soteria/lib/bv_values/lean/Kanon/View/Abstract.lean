import Kanon.View.Types

/-!
# The abstract types of the view

The view (`../rules/view.knl`) is host infrastructure that Lean does not model
(all its functions are `[@no_lean]`): its abstract types are placeholders.
-/

namespace Kanon.View

/-- The SMT operator of the encoding of a term (`View_host.smt_op`), unused. -/
structure SmtOp where
  deriving Inhabited

/-- The SMT operator of the encoding of a sort (`View_host.smt_sort_op`), unused. -/
structure SmtSortOp where
  deriving Inhabited

end Kanon.View
