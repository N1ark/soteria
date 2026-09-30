/-!
# Languages, generically (trial)

A language gives its operators, types and values, the typing of its operators
and their semantics. Terms, their evaluation and refinement are defined once
for every language; modules (`Core/Bool.lean`, ...) give their rules and proofs
for any language that includes them.
-/

namespace Bvr.Core

structure Lang where
  Op : Type
  Ty : Type
  Val : Type
  [decOp : DecidableEq Op]
  [decTy : DecidableEq Ty]
  /-- The typing of an operator: the types of its operands, and of its result. -/
  wt : Op → List Ty → Ty → Prop
  /-- The values of a type. -/
  hasTy : Val → Ty → Prop
  /-- The semantics of an operator, on operands that may be poison (`none`). -/
  den : Op → List (Option Val) → Option Val

attribute [instance] Lang.decOp Lang.decTy

variable {L : Lang}

inductive Term (L : Lang) where
  | var (x : Nat) (ty : L.Ty)
  | app (op : L.Op) (args : List (Term L)) (ty : L.Ty)

def Term.ty : Term L → L.Ty
  | .var _ t | .app _ _ t => t

mutual
def Term.WT : Term L → Prop
  | .var _ _ => True
  | .app op args t => L.wt op (Term.tys args) t ∧ Term.WTs args

def Term.WTs : List (Term L) → Prop
  | [] => True
  | a :: as => a.WT ∧ Term.WTs as

def Term.tys : List (Term L) → List L.Ty
  | [] => []
  | a :: as => a.ty :: Term.tys as
end

abbrev Env (L : Lang) := Nat → Option L.Val

mutual
def ev (ρ : Env L) : Term L → Option L.Val
  | .var x _ => ρ x
  | .app op args _ => L.den op (evs ρ args)

def evs (ρ : Env L) : List (Term L) → List (Option L.Val)
  | [] => []
  | a :: as => ev ρ a :: evs ρ as
end

open Classical in
/-- The value of a term; `none` for poison. -/
noncomputable def eval (ρ : Env L) (t : Term L) : Option L.Val :=
  if t.WT then ev ρ t else none

/-- `r` refines `spec`: it has the same type, and the same value whenever
`spec` is not poison. -/
def Refines (spec r : Term L) : Prop :=
  (spec.WT → r.WT ∧ r.ty = spec.ty) ∧ ∀ ρ v, eval ρ spec = some v → eval ρ r = some v

theorem Refines.refl {t : Term L} : Refines t t := ⟨fun h => ⟨h, rfl⟩, fun _ _ h => h⟩

theorem Refines.trans {a b c : Term L} (h1 : Refines a b) (h2 : Refines b c) :
    Refines a c :=
  ⟨fun w => let ⟨wb, eb⟩ := h1.1 w; let ⟨wc, ec⟩ := h2.1 wb; ⟨wc, ec.trans eb⟩,
   fun ρ v e => h2.2 ρ v (h1.2 ρ v e)⟩

@[simp] theorem eval_of_WT {ρ : Env L} {t : Term L} (w : t.WT) : eval ρ t = ev ρ t := by
  simp [eval, w]

end Bvr.Core
