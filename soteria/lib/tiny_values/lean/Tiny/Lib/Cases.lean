import Tiny.Lemmas

/-!
# Commutativity

The proof of an alternative that only swaps operands of commutative operators
from the unswapped one (`kanon_comm`, declared by Kanon's library).
`Binop.Comm` is generated from the `[@comm]` operators of `lang.knl`, and
`evBinop_comm` proves that each of them commutes.
-/

namespace Tiny.Lib

open Classical

theorem Binop.WT_comm {op : Binop} (hc : op.Comm) {a b t : Ty} (h : op.WT a b t) :
    op.WT b a t := by
  cases op <;> simp_all [Binop.Comm, Binop.WT]

theorem pand_comm (a b : Option Val) : pand a b = pand b a := by
  rcases a with _ | ⟨⟨_ | _⟩ | _⟩ <;> rcases b with _ | ⟨⟨_ | _⟩ | _⟩ <;> rfl

theorem por_comm (a b : Option Val) : por a b = por b a := by
  rcases a with _ | ⟨⟨_ | _⟩ | _⟩ <;> rcases b with _ | ⟨⟨_ | _⟩ | _⟩ <;> rfl

theorem intOp_comm {f g : Int → Int → Val} (hfg : ∀ x y, f x y = g y x) (a b : Option Val) :
    intOp f a b = intOp g b a := by
  rcases a with _ | ⟨_ | x⟩ <;> rcases b with _ | ⟨_ | y⟩ <;> simp [intOp, hfg]

theorem evBinop_comm {op : Binop} (hc : op.Comm) (a b : Option Val) :
    evBinop op a b = evBinop op b a := by
  cases op <;> simp only [Binop.Comm] at hc
  case And => exact pand_comm a b
  case Or => exact por_comm a b
  case Eq => rcases a <;> rcases b <;> simp [evBinop, eqOp, eq_comm]
  case Plus => exact intOp_comm (fun x y => by rw [Int.add_comm]) a b
  case Times => exact intOp_comm (fun x y => by rw [Int.mul_comm]) a b

/-- Swapping the operands of a commutative operator. -/
theorem Refines.comm {op : Binop} (hc : op.Comm) {a b : Term} {t t' : Ty}
    (ht : (Term.mk (.Binop op a b) t).WT → t' = t) :
    Refines (.mk (.Binop op a b) t) (.mk (.Binop op b a) t') := by
  have syn : (Term.mk (.Binop op a b) t).WT → (Term.mk (.Binop op b a) t').WT ∧ t' = t :=
    fun w => by
      have ⟨w1, wa, wb⟩ := WT_binop.1 w
      have e := ht w; subst e
      exact ⟨WT_binop.2 ⟨Binop.WT_comm hc w1, wb, wa⟩, rfl⟩
  refine ⟨syn, fun ρ v e => ?_⟩
  have w := eval_WT e
  rw [eval_binop w] at e; rw [eval_binop (syn w).1, evBinop_comm hc]; exact e

/-- Swapping the operands of a commutative operator, and refining them. -/
theorem Refines.comm_congr {op : Binop} (hc : op.Comm) {a b a' b' : Term} {t t' : Ty}
    (ha : Refines a b') (hb : Refines b a') (ht : (Term.mk (.Binop op a b) t).WT → t' = t) :
    Refines (.mk (.Binop op a b) t) (.mk (.Binop op a' b') t') :=
  Refines.trans (Refines.comm (t' := t) hc (fun _ => rfl))
    (Refines.binop hb ha (fun w => ht (by
      have ⟨w1, wa, wb⟩ := WT_binop.1 w
      exact WT_binop.2 ⟨Binop.WT_comm hc w1, wb, wa⟩)))

/-- Proves `Refines s s'` for terms that only differ by the order of the
operands of commutative operators. -/
syntax "kanon_comm_side" : tactic
macro_rules
  | `(tactic| kanon_comm) => `(tactic| first
      | exact Refines.refl
      | (apply Refines.binop <;> kanon_comm_side)
      | (apply Refines.comm_congr <;> kanon_comm_side)
      | (apply Refines.unop <;> kanon_comm_side)
      | (apply Refines.ite <;> kanon_comm_side))
macro_rules
  | `(tactic| kanon_comm_side) => `(tactic| first
      | (simp [Binop.Comm]; done)
      | kanon_comm
      | (intro _; rfl))

end Tiny.Lib
