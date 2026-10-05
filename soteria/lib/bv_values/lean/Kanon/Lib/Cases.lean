import Kanon.Lemmas

/-!
# Commutativity

The operands of a commutative operator can be swapped (`Refines.comm`): the
commutativity statements of the operators (`Op2.X.comm.Stmt`) are proved from it
in `Proofs/Laws.lean`.
-/

namespace Kanon.Lib

open Classical

/-! ## Commutativity

`Op2.Comm` is generated from the `[@comm]` operators of the rules, and
`evOp2_comm` proves that each of them commutes. -/

theorem Op2.WT_comm {op : Op2} (hc : op.Comm) {a b t : Ty} (h : op.WT a b t) :
    op.WT b a t ∧ (op ≠ .Eq → a = b) := by
  cases op <;> simp_all [Op2.Comm, Op2.WT]

theorem bvBin_comm {f g : ∀ {n : Nat}, BitVec n → BitVec n → Option Val}
    (hfg : ∀ {n} (x y : BitVec n), f x y = g y x) (a b : Option Val) :
    bvBin f a b = bvBin g b a := by
  rcases a with _ | ⟨_ | ⟨n, x⟩ | _ | _ | _ | _⟩ <;>
    rcases b with _ | ⟨_ | ⟨m, y⟩ | _ | _ | _ | _⟩ <;> simp [bvBin]
  by_cases h : m = n
  · subst h; simp [hfg]
  · simp [h, Ne.symm h]

theorem fBin_comm {f g : (p : Fp) → FBits p → FBits p → Option Val}
    (hfg : ∀ p (x y : FBits p), f p x y = g p y x) (a b : Option Val) :
    fBin f a b = fBin g b a := by
  rcases a with _ | ⟨_ | _ | _ | ⟨p, x⟩ | _ | _⟩ <;>
    rcases b with _ | ⟨_ | _ | _ | ⟨q, y⟩ | _ | _⟩ <;> simp [fBin]
  by_cases h : q = p
  · subst h; simp [hfg]
  · simp [h, Ne.symm h]

theorem ovf_comm {n : Nat} (x y : BitVec n) : (x.saddOverflow y = y.saddOverflow x) ∧
    (x.uaddOverflow y = y.uaddOverflow x) ∧ (x.smulOverflow y = y.smulOverflow x) ∧
    (x.umulOverflow y = y.umulOverflow x) := by
  simp [BitVec.saddOverflow, BitVec.uaddOverflow, BitVec.smulOverflow,
    BitVec.umulOverflow, Int.add_comm, Nat.add_comm, Int.mul_comm, Nat.mul_comm]

theorem evOp2_comm {FS : FloatSem} {op : Op2} (hc : op.Comm) (a b : Option Val) :
    evOp2 FS op a b = evOp2 FS op b a := by
  cases op <;> simp only [Op2.Comm] at hc
  case And => exact BoolMod.pand_comm a b
  case Or => exact BoolMod.por_comm a b
  case Eq => exact BoolMod.peq_comm a b
  case FEq =>
    simp only [evOp2]
    exact fBin_comm (fun p x y => by simp only [FBits.eq]; grind) a b
  case Add c =>
    simp only [evOp2, checkedOp]
    exact bvBin_comm (fun x y => by
      simp [(ovf_comm x y).1, (ovf_comm x y).2.1, BitVec.add_comm x]) a b
  case Mul c =>
    simp only [evOp2, checkedOp]
    exact bvBin_comm (fun x y => by
      simp [(ovf_comm x y).2.2.1, (ovf_comm x y).2.2.2, BitVec.mul_comm x]) a b
  case AddOvf s =>
    simp only [evOp2]
    exact bvBin_comm (fun x y => by simp [(ovf_comm x y).1, (ovf_comm x y).2.1]) a b
  case MulOvf s =>
    simp only [evOp2]
    exact bvBin_comm (fun x y => by simp [(ovf_comm x y).2.2.1, (ovf_comm x y).2.2.2]) a b
  case BitAnd =>
    simp only [evOp2]; exact bvBin_comm (fun x y => by simp [BitVec.and_comm]) a b
  case BitOr =>
    simp only [evOp2]; exact bvBin_comm (fun x y => by simp [BitVec.or_comm]) a b
  case BitXor =>
    simp only [evOp2]; exact bvBin_comm (fun x y => by simp [BitVec.xor_comm]) a b

/-- Swapping the operands of a commutative operator (whose type may be given by
either operand). -/
theorem Refines.comm {FS : FloatSem} {op : Op2} (hc : op.Comm) {a b : Term} {t t' : Ty}
    (ht : (Term.mk (.Op2 op a b) t).WT → t' = t) :
    Refines FS (.mk (.Op2 op a b) t) (.mk (.Op2 op b a) t') := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v _ _ e => ?_)
  · have ⟨w1, wa, wb⟩ := WT_op2.1 w
    have e := ht w; subst e
    exact ⟨WT_op2.2 ⟨(Op2.WT_comm hc w1).1, wb, wa⟩, rfl⟩
  · simp only [ev] at e ⊢
    rw [evOp2_comm hc]; exact e

end Kanon.Lib
