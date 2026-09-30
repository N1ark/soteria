import Bvr.Lemmas

/-!
# Glue for `[@cases]` functions

The generated proof of a rule from the proofs of its alternatives (`bvr_arm`),
and the proof of an alternative that only swaps operands of commutative
operators from the unswapped one (`bvr_comm`).
-/

namespace Bvr.Lib

open Classical

theorem orElse_some {α} {a b : Option α} {r : α} (h : (a <|> b) = some r) :
    a = some r ∨ b = some r := by
  cases a <;> simp_all

theorem whenSome_eq_some {α} {c : Bool} {a r : α} (h : whenSome c a = some r) :
    c = true ∧ a = r := by
  cases c <;> simp_all [whenSome]

/-- Closes `Refines FS spec res` from `h : <one alternative> = some res`, with
`p` the proof of that alternative: splits its match (unless its pattern always
matches, so that the conditionals of its body are not split instead), takes its
guard (`whenSome`, also for unguarded alternatives), and applies `p`, whose
conclusion must then match the goal. -/
macro "bvr_arm " h:ident p:term : tactic => `(tactic| first
  | (obtain ⟨hg, heq⟩ := Lib.whenSome_eq_some $h:ident
     subst heq
     apply $p <;> assumption)
  | ((try split at $h:ident)
     all_goals first
       | (simp at $h:ident; done)
       | (obtain ⟨hg, heq⟩ := Lib.whenSome_eq_some $h:ident
          subst heq
          apply $p <;> assumption)))

/-! ## Commutativity

`Binop.Comm` is generated from the `[@comm]` operators of `lang.bvl`, and
`evBinop_comm` proves that each of them commutes. -/

theorem Binop.WT_comm {op : Binop} (hc : op.Comm) {a b t : Ty} (h : op.WT a b t) :
    op.WT b a t ∧ (op ≠ .Eq → a = b) := by
  cases op <;> simp_all [Binop.Comm, Binop.WT]

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

theorem pand_comm (a b : Option Val) : pand a b = pand b a := by
  rcases a with _ | ⟨⟨_ | _⟩ | _ | _ | _ | _ | _⟩ <;>
    rcases b with _ | ⟨⟨_ | _⟩ | _ | _ | _ | _ | _⟩ <;> rfl

theorem por_comm (a b : Option Val) : por a b = por b a := by
  rcases a with _ | ⟨⟨_ | _⟩ | _ | _ | _ | _ | _⟩ <;>
    rcases b with _ | ⟨⟨_ | _⟩ | _ | _ | _ | _ | _⟩ <;> rfl

theorem ovf_comm {n : Nat} (x y : BitVec n) : (x.saddOverflow y = y.saddOverflow x) ∧
    (x.uaddOverflow y = y.uaddOverflow x) ∧ (x.smulOverflow y = y.smulOverflow x) ∧
    (x.umulOverflow y = y.umulOverflow x) := by
  simp [BitVec.saddOverflow, BitVec.uaddOverflow, BitVec.smulOverflow,
    BitVec.umulOverflow, Int.add_comm, Nat.add_comm, Int.mul_comm, Nat.mul_comm]

theorem evBinop_comm {FS : FloatSem} {op : Binop} (hc : op.Comm) (a b : Option Val) :
    evBinop FS op a b = evBinop FS op b a := by
  cases op <;> simp only [Binop.Comm] at hc
  case And => exact pand_comm a b
  case Or => exact por_comm a b
  case Eq => rcases a <;> rcases b <;> simp [evBinop, eq_comm]
  case FEq =>
    simp only [evBinop]
    exact fBin_comm (fun p x y => by simp only [FBits.eq]; grind) a b
  case Add c =>
    simp only [evBinop, checkedOp]
    exact bvBin_comm (fun x y => by
      simp [(ovf_comm x y).1, (ovf_comm x y).2.1, BitVec.add_comm x]) a b
  case Mul c =>
    simp only [evBinop, checkedOp]
    exact bvBin_comm (fun x y => by
      simp [(ovf_comm x y).2.2.1, (ovf_comm x y).2.2.2, BitVec.mul_comm x]) a b
  case AddOvf s =>
    simp only [evBinop]
    exact bvBin_comm (fun x y => by simp [(ovf_comm x y).1, (ovf_comm x y).2.1]) a b
  case MulOvf s =>
    simp only [evBinop]
    exact bvBin_comm (fun x y => by simp [(ovf_comm x y).2.2.1, (ovf_comm x y).2.2.2]) a b
  case BitAnd =>
    simp only [evBinop]; exact bvBin_comm (fun x y => by simp [BitVec.and_comm]) a b
  case BitOr =>
    simp only [evBinop]; exact bvBin_comm (fun x y => by simp [BitVec.or_comm]) a b
  case BitXor =>
    simp only [evBinop]; exact bvBin_comm (fun x y => by simp [BitVec.xor_comm]) a b

/-- Swapping the operands of a commutative operator (whose type may be given by
either operand). -/
theorem Refines.comm {FS : FloatSem} {op : Binop} (hc : op.Comm) {a b : Term} {t t' : Ty}
    (ht : (Term.mk (.Binop op a b) t).WT → t' = t) :
    Refines FS (.mk (.Binop op a b) t) (.mk (.Binop op b a) t') := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · have ⟨w1, wa, wb⟩ := WT_binop.1 w
    have e := ht w; subst e
    exact ⟨WT_binop.2 ⟨(Binop.WT_comm hc w1).1, wb, wa⟩, rfl⟩
  · rw [eval_binop w] at e; rw [eval_binop w', evBinop_comm hc]; exact e

/-- Swapping the operands of a commutative operator, and refining them. -/
theorem Refines.comm_congr {FS : FloatSem} {op : Binop} (hc : op.Comm) {a b a' b' : Term}
    {t t' : Ty} (ha : Refines FS a b') (hb : Refines FS b a')
    (ht : (Term.mk (.Binop op a b) t).WT → t' = t) :
    Refines FS (.mk (.Binop op a b) t) (.mk (.Binop op a' b') t') :=
  Refines.trans (Refines.comm (t' := t) hc (fun _ => rfl))
    (Refines.binop hb ha (fun w => by
      have := ht (by
        have ⟨w1, wa, wb⟩ := WT_binop.1 w
        exact WT_binop.2 ⟨(Binop.WT_comm hc w1).1, wb, wa⟩)
      simp [this]))

/-- The type of a node, given by one of its operands, is that of the other one
when the operator requires them to be equal. -/
theorem ty_of_WT_binop {op : Binop} {a b : Term} {t : Ty} (hc : op.Comm) (hne : op ≠ .Eq)
    (w : (Term.mk (.Binop op a b) t).WT) : b.ty = a.ty :=
  ((Binop.WT_comm hc (WT_binop.1 w).1).2 hne).symm

/-- Proves `Refines FS s s'` for terms that only differ by the order of the
operands of commutative operators. -/
syntax "bvr_comm" : tactic
syntax "bvr_comm_side" : tactic
macro_rules
  | `(tactic| bvr_comm) => `(tactic| first
      | exact Refines.refl
      | (apply Refines.binop <;> bvr_comm_side)
      | (apply Refines.comm_congr <;> bvr_comm_side)
      | (apply Refines.unop <;> bvr_comm_side)
      | (apply Refines.ite <;> bvr_comm_side))
macro_rules
  | `(tactic| bvr_comm_side) => `(tactic| first
      | (simp [Binop.Comm]; done)
      | bvr_comm
      | (intro w; simp; done)
      | (intro w; simpa using ty_of_WT_binop (by simp [Binop.Comm]) (by simp) w)
      -- a type given by the size of either operand
      | (intro w
         have e := ty_of_WT_binop (by simp [Binop.Comm]) (by simp) w
         simp only [Term.ty_mk] at e
         simp [size, ty, e]))

end Bvr.Lib
