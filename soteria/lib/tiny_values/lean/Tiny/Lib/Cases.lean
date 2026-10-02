import Tiny.Lemmas

/-!
# Commutativity

The proof of an alternative that only swaps operands of commutative operators
from the unswapped one (`kanon_comm`, Kanon's, with `Refines.comm_congr`).
`Binop.Comm` is generated from the `[@comm]` operators of `lang.knl`, and
`evBinop_comm` proves that each of them commutes.
-/

namespace Tiny.Lib

open Classical Kanon

theorem Binop.WT_comm {op : Binop} (hc : op.Comm) {a b t : Ty} (h : op.WT a b t) :
    op.WT b a t := by
  cases op <;> simp_all [Binop.Comm, Binop.WT]

theorem intOp_comm {f g : Int → Int → Val} (hfg : ∀ x y, f x y = g y x) (a b : Option Val) :
    intOp f a b = intOp g b a := by
  rcases a with _ | ⟨_ | x⟩ <;> rcases b with _ | ⟨_ | y⟩ <;> simp [intOp, hfg]

theorem evBinop_comm {op : Binop} (hc : op.Comm) (a b : Option Val) :
    evBinop op a b = evBinop op b a := by
  cases op <;> simp only [Binop.Comm] at hc
  case And => exact BoolMod.pand_comm a b
  case Or => exact BoolMod.por_comm a b
  case Eq => exact BoolMod.peq_comm a b
  case Plus => exact intOp_comm (fun x y => by rw [Int.add_comm]) a b
  case Times => exact intOp_comm (fun x y => by rw [Int.mul_comm]) a b

/-- Swapping the operands of a commutative operator. -/
theorem Refines.comm {op : Binop} (hc : op.Comm) {a b : Term} {t t' : Ty}
    (ht : (Term.mk (.Binop op a b) t).WT → t' = t) :
    Refines (.mk (.Binop op a b) t) (.mk (.Binop op b a) t') := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v _ _ e => ?_)
  · have ⟨w1, wa, wb⟩ := WT_binop.1 w
    have e := ht w; subst e
    exact ⟨WT_binop.2 ⟨Binop.WT_comm hc w1, wb, wa⟩, rfl⟩
  · show evBinop op (ev ρ b) (ev ρ a) = some v
    rw [evBinop_comm hc]; exact e

/-- Swapping the operands of a commutative operator, and refining them. -/
@[kanon_comm_lemma] theorem Refines.comm_congr {op : Binop} (hc : op.Comm) {a b a' b' : Term}
    {t t' : Ty} (ha : Refines a b') (hb : Refines b a')
    (ht : (Term.mk (.Binop op a b) t).WT → t' = t) :
    Refines (.mk (.Binop op a b) t) (.mk (.Binop op a' b') t') :=
  Sem.Refines.trans (Refines.comm (t' := t) hc (fun _ => rfl))
    (Refines.binop hb ha (fun w => ht (by
      have ⟨w1, wa, wb⟩ := WT_binop.1 w
      exact WT_binop.2 ⟨Binop.WT_comm hc w1, wb, wa⟩)))

/-- The operators of the side goals of `kanon_comm` are commutative. -/
macro_rules | `(tactic| kanon_comm_side) => `(tactic| (simp [Binop.Comm]; done))

end Tiny.Lib
