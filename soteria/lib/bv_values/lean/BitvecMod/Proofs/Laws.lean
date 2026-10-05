import BitvecMod.Lib.Den

/-! The commutativity of the commutative operators of the bitvec module, by
their structural values. -/

namespace BitvecMod

open Classical Kanon Kanon.Sem

set_option linter.unusedSectionVars false

namespace Lib

variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
  {LBool : KanonBool.Syntax B} {LCore : CoreMod.Syntax B} {L : Syntax B LBool LCore}
  [KanonBool.Sem LBool] [CoreMod.Sem LCore] [Sem L]

/-- Swapping the operands of a commutative binary node on bit-vectors. -/
theorem refines_bin_swap {K : S.Term → S.Term → B.Kind}
    {F : ∀ {n : Nat}, Option (BitVec n) → Option (BitVec n) → Option (BitVec n)}
    (hF : ∀ {n : Nat} (x y : Option (BitVec n)), F x y = F y x)
    (hWT : ∀ a b t, S.WT (B.node (K a b) t) ↔
      ((∃ n : Int, 0 < n ∧ S.ty a = L.TBitVector n) ∧ S.ty b = S.ty a ∧ t = S.ty a) ∧
        S.WT a ∧ S.WT b)
    (hden : ∀ ρ n a b t, Sem.den L ρ n (B.node (K a b) t) = F (Sem.den L ρ n a) (Sem.den L ρ n b))
    (a b : S.Term) (t : S.Ty) : S.Refines (B.node (K a b) t) (B.node (K b a) t) := by
  refine Refines.den (L := L) (fun w => ?_) (fun w => ?_) (fun n w hs ρ x e => ?_) <;>
    rw [hWT] at w <;> obtain ⟨⟨⟨m, hm0, hm⟩, hb, ht⟩, wa, wb⟩ := w
  · exact ⟨m, by rw [B.ty_node, ht, hm]⟩
  · exact ⟨(hWT _ _ _).2 ⟨⟨⟨m, hm0, hb.trans hm⟩, hb.symm, ht.trans hb.symm⟩, wb, wa⟩,
      by rw [B.ty_node, B.ty_node]⟩
  · rw [hden] at e ⊢; rw [hF]; exact e

/-- Swapping the operands of a commutative binary predicate on bit-vectors. -/
theorem refines_pred_swap {K : S.Term → S.Term → B.Kind}
    {f : ∀ {n : Nat}, BitVec n → BitVec n → Bool}
    (hf : ∀ {n : Nat} (x y : BitVec n), f x y = f y x)
    (hWT : ∀ a b t, S.WT (B.node (K a b) t) ↔
      ((∃ n : Int, 0 < n ∧ S.ty a = L.TBitVector n) ∧ S.ty b = S.ty a ∧ t = LBool.TBool) ∧
        S.WT a ∧ S.WT b)
    (hden : ∀ ρ a b t, Sem.denB L ρ (B.node (K a b) t) =
      match L.asTBitVector (S.ty a) with
      | some m =>
        if 0 < m then binB f (Sem.den L ρ m.toNat a) (Sem.den L ρ m.toNat b) else none
      | none => evB LBool ρ (B.node (K a b) t))
    (a b : S.Term) (t : S.Ty) : S.Refines (B.node (K a b) t) (B.node (K b a) t) := by
  refine Refines.denB (L := L) (fun w => ?_) (fun w => ?_) (fun w ρ x e => ?_) <;>
    rw [hWT] at w <;> obtain ⟨⟨⟨m, hm0, hm⟩, hb, ht⟩, wa, wb⟩ := w
  · rw [B.ty_node, ht]
  · exact ⟨(hWT _ _ _).2 ⟨⟨⟨m, hm0, hb.trans hm⟩, hb.symm, ht⟩, wb, wa⟩,
      by rw [B.ty_node, B.ty_node]⟩
  · simp only [hden, hm, hb, L.asTBitVector_sort, hm0, ite_true] at e ⊢
    revert e
    cases Sem.den L ρ m.toNat a <;> cases Sem.den L ρ m.toNat b <;> simp [hf]

theorem ovf_comm {n : Nat} (x y : BitVec n) : (x.saddOverflow y = y.saddOverflow x) ∧
    (x.uaddOverflow y = y.uaddOverflow x) ∧ (x.smulOverflow y = y.smulOverflow x) ∧
    (x.umulOverflow y = y.umulOverflow x) := by
  simp [BitVec.saddOverflow, BitVec.uaddOverflow, BitVec.smulOverflow,
    BitVec.umulOverflow, Int.add_comm, Nat.add_comm, Int.mul_comm, Nat.mul_comm]

end Lib

open Lib

@[kanon_arm] theorem Add.comm.proof : Add.comm.Stmt := by
  intro S _ _ B LBool LCore L _ _ _ c a b t
  refine refines_bin_swap (fun x y => ?_) (L.WT_Add c) (fun ρ n => Sem.den_Add ρ n c) a b t
  cases x <;> cases y <;> simp [(ovf_comm _ _).1, (ovf_comm _ _).2.1, BitVec.add_comm]

@[kanon_arm] theorem Mul.comm.proof : Mul.comm.Stmt := by
  intro S _ _ B LBool LCore L _ _ _ c a b t
  refine refines_bin_swap (fun x y => ?_) (L.WT_Mul c) (fun ρ n => Sem.den_Mul ρ n c) a b t
  cases x <;> cases y <;> simp [(ovf_comm _ _).2.2.1, (ovf_comm _ _).2.2.2, BitVec.mul_comm]

@[kanon_arm] theorem BitAnd.comm.proof : BitAnd.comm.Stmt := by
  intro S _ _ B LBool LCore L _ _ _ a b t
  refine refines_bin_swap (fun x y => ?_) L.WT_BitAnd Sem.den_BitAnd a b t
  cases x <;> cases y <;> simp [BitVec.and_comm]

@[kanon_arm] theorem BitOr.comm.proof : BitOr.comm.Stmt := by
  intro S _ _ B LBool LCore L _ _ _ a b t
  refine refines_bin_swap (fun x y => ?_) L.WT_BitOr Sem.den_BitOr a b t
  cases x <;> cases y <;> simp [BitVec.or_comm]

@[kanon_arm] theorem BitXor.comm.proof : BitXor.comm.Stmt := by
  intro S _ _ B LBool LCore L _ _ _ a b t
  refine refines_bin_swap (fun x y => ?_) L.WT_BitXor Sem.den_BitXor a b t
  cases x <;> cases y <;> simp [BitVec.xor_comm]

@[kanon_arm] theorem AddOvf.comm.proof : AddOvf.comm.Stmt := by
  intro S _ _ B LBool LCore L _ _ _ s a b t
  refine refines_pred_swap
    (f := fun x y => if s then x.saddOverflow y else x.uaddOverflow y) (fun x y => ?_) (L.WT_AddOvf s) (fun ρ => Sem.denB_AddOvf ρ s) a b t
  cases s <;> simp [(ovf_comm _ _).1, (ovf_comm _ _).2.1]

@[kanon_arm] theorem MulOvf.comm.proof : MulOvf.comm.Stmt := by
  intro S _ _ B LBool LCore L _ _ _ s a b t
  refine refines_pred_swap
    (f := fun x y => if s then x.smulOverflow y else x.umulOverflow y) (fun x y => ?_) (L.WT_MulOvf s) (fun ρ => Sem.denB_MulOvf ρ s) a b t
  cases s <;> simp [(ovf_comm _ _).2.2.1, (ovf_comm _ _).2.2.2]

end BitvecMod
