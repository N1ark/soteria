import KanonCore.Proof
import Kanon.Statements

/-!
Basic facts about evaluation, used by the rule proofs, with Kanon's generic
facts on values and refinement (`Kanon.Sem`).
-/

namespace Kanon

open Classical

/-! Kanon's `Sem.eval_WT` and `Sem.eval_eq_ev`, stated on `Term.WT`, `eval` and
`ev`, to unify and rewrite with. -/

theorem eval_WT {FS ρ t v} (h : eval FS ρ t = some v) : t.WT := Sem.eval_WT h

theorem eval_eq_ev {FS ρ t} (h : t.WT) : eval FS ρ t = ev FS ρ t := Sem.eval_eq_ev h

theorem size_of_ty_of_bits {t : Ty} {n : Int} (h : t = .TBitVector n ∨ t = .TLoc n) :
    size_of_ty t = n := by
  rcases h with rfl | rfl <;> rfl

@[simp] theorem size_of_ty_bitVector (n : Int) : size_of_ty (.TBitVector n) = n := rfl
@[simp] theorem ty_eq (v : Term) : ty v = v.ty := rfl
@[simp] theorem kind_eq (v : Term) : kind v = v.kind := rfl
@[simp] theorem size_eq (v : Term) : Bitvec.size v = size_of_ty v.ty := rfl

end Kanon

namespace Kanon

open Classical BoolMod
open Kanon.Sem (OLe)

/-! ## Evaluation of well-typed nodes -/

theorem WT_op1 {op a t} : (Term.mk (.Op1 op a) t).WT ↔ op.WT a.ty t ∧ a.WT := by
  simp [Term.WT]

theorem WT_op2 {op a b t} :
    (Term.mk (.Op2 op a b) t).WT ↔ op.WT a.ty b.ty t ∧ a.WT ∧ b.WT := by
  simp [Term.WT]

theorem WT_op3 {op a b c t} :
    (Term.mk (.Op3 op a b c) t).WT ↔
      op.WT a.ty b.ty c.ty t ∧ a.WT ∧ b.WT ∧ c.WT := by
  simp [Term.WT]

theorem eval_op1 {FS ρ op a t} (h : (Term.mk (.Op1 op a) t).WT) :
    eval FS ρ (.mk (.Op1 op a) t) = evOp1 FS op (eval FS ρ a) := by
  rw [eval_eq_ev h, eval_eq_ev (WT_op1.1 h).2, ev]

theorem eval_op2 {FS ρ op a b t} (h : (Term.mk (.Op2 op a b) t).WT) :
    eval FS ρ (.mk (.Op2 op a b) t) = evOp2 FS op (eval FS ρ a) (eval FS ρ b) := by
  have := WT_op2.1 h
  rw [eval_eq_ev h, eval_eq_ev this.2.1, eval_eq_ev this.2.2, ev]

theorem eval_ite {FS ρ g a b t} (h : (Term.mk (.Op3 .Ite g a b) t).WT) :
    eval FS ρ (.mk (.Op3 .Ite g a b) t) =
      match eval FS ρ g with
      | some (.bool true) => eval FS ρ a
      | some (.bool false) => eval FS ρ b
      | _ => none := by
  have := WT_op3.1 h
  rw [eval_eq_ev h, eval_eq_ev this.2.1, eval_eq_ev this.2.2.1, eval_eq_ev this.2.2.2]
  simp only [ev, evOp3, pite]
  rcases ev FS ρ g with _ | ⟨⟨_ | _⟩ | _ | _ | _ | _ | _⟩ <;> simp

theorem eval_fma {FS ρ a b c t} (h : (Term.mk (.Op3 .Fma a b c) t).WT) :
    eval FS ρ (.mk (.Op3 .Fma a b c) t) =
      evFma FS (eval FS ρ a) (eval FS ρ b) (eval FS ρ c) := by
  have := WT_op3.1 h
  rw [eval_eq_ev h, eval_eq_ev this.2.1, eval_eq_ev this.2.2.1, eval_eq_ev this.2.2.2, ev]
  rfl

/-! ## Monotonicity of the operators in poison -/

@[simp] theorem pnot_bool {b} : pnot Val.bool (some (.bool b)) = some (.bool !b) := by
  cases b <;> simp [pnot]

@[simp] theorem evUnop_none {FS op} : evOp1 FS op none = none := by
  cases op <;> simp [evOp1, pnot]

theorem evUnop_mono {FS op a a'} (h : OLe a a') : OLe (evOp1 FS op a) (evOp1 FS op a') := by
  intro v e
  cases op
  case Not => exact pnot_mono h v e
  all_goals cases a with
    | none => simp at e
    | some x => rw [h x rfl]; exact e


@[simp] theorem bvBin_none_l {f b} : bvBin f none b = none := by cases b <;> rfl
@[simp] theorem bvBin_none_r {f a} : bvBin f a none = none := by
  rcases a with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl
@[simp] theorem fBin_none_l {f b} : fBin f none b = none := by cases b <;> rfl
@[simp] theorem fBin_none_r {f a} : fBin f a none = none := by
  rcases a with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl

theorem evBinop_mono {FS op a a' b b'} (ha : OLe a a') (hb : OLe b b') :
    OLe (evOp2 FS op a b) (evOp2 FS op a' b') := by
  cases op
  case And => exact pand_mono ha hb
  case Or => exact por_mono ha hb
  case Eq => exact peq_mono ha hb
  all_goals
    intro v e
    rcases a with _ | x
    · simp [evOp2, evPtr, fArith, checkedOp] at e
    rcases b with _ | y
    · rcases x with _ | _ | _ | _ | _ | _ <;> simp [evOp2, evPtr, fArith, checkedOp] at e
    rw [ha x rfl, hb y rfl]; exact e

theorem evFma_mono {FS a a' b b' c c'} (ha : OLe a a') (hb : OLe b b') (hc : OLe c c') :
    OLe (evFma FS a b c) (evFma FS a' b' c') := by
  intro v e
  rcases a with _ | x; · simp [evFma] at e
  rcases b with _ | y; · rcases x with _ | _ | _ | _ | _ | _ <;> simp [evFma] at e
  rcases c with _ | z
  · rcases x with _ | _ | _ | _ | _ | _ <;> rcases y with _ | _ | _ | _ | _ | _ <;>
      simp [evFma] at e
  rw [ha x rfl, hb y rfl, hc z rfl]; exact e

/-! ## Congruence: refining the children of a node refines the node -/

theorem Refines.op1 {FS op a a' t t'} (ha : Refines FS a a')
    (ht : (Term.mk (.Op1 op a) t).WT → t' = t) :
    Refines FS (.mk (.Op1 op a) t) (.mk (.Op1 op a') t') := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · have ⟨w1, w2⟩ := WT_op1.1 w
    obtain ⟨w3, s3⟩ : a'.WT ∧ a'.ty = a.ty := ha.syn w2
    refine ⟨WT_op1.2 ⟨?_, w3⟩, ht w⟩
    rw [s3, ht w]; exact w1
  · simp only [ev] at e ⊢
    exact evUnop_mono (ha.ev (WT_op1.1 w).2 ρ) v e

theorem Refines.op2 {FS op a a' b b' t t'} (ha : Refines FS a a') (hb : Refines FS b b')
    (ht : (Term.mk (.Op2 op a b) t).WT → t' = t) :
    Refines FS (.mk (.Op2 op a b) t) (.mk (.Op2 op a' b') t') := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · have ⟨w1, wa, wb⟩ := WT_op2.1 w
    obtain ⟨wa', sa⟩ : a'.WT ∧ a'.ty = a.ty := ha.syn wa
    obtain ⟨wb', sb⟩ : b'.WT ∧ b'.ty = b.ty := hb.syn wb
    refine ⟨WT_op2.2 ⟨?_, wa', wb'⟩, ht w⟩
    rw [sa, sb, ht w]; exact w1
  · have ⟨_, wa, wb⟩ := WT_op2.1 w
    simp only [ev] at e ⊢
    exact evBinop_mono (ha.ev wa ρ) (hb.ev wb ρ) v e

theorem Refines.ite {FS g g' a a' b b' t t'} (hg : Refines FS g g') (ha : Refines FS a a')
    (hb : Refines FS b b') (ht : (Term.mk (.Op3 .Ite g a b) t).WT → t' = t) :
    Refines FS (.mk (.Op3 .Ite g a b) t) (.mk (.Op3 .Ite g' a' b') t') := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · have ⟨w1, wg, wa, wb⟩ := WT_op3.1 w
    obtain ⟨wg', sg⟩ : g'.WT ∧ g'.ty = g.ty := hg.syn wg
    obtain ⟨wa', sa⟩ : a'.WT ∧ a'.ty = a.ty := ha.syn wa
    obtain ⟨wb', sb⟩ : b'.WT ∧ b'.ty = b.ty := hb.syn wb
    refine ⟨WT_op3.2 ⟨?_, wg', wa', wb'⟩, ht w⟩
    rw [sg, sa, sb, ht w]; exact w1
  · have ⟨_, wg, wa, wb⟩ := WT_op3.1 w
    simp only [ev] at e ⊢
    exact pite_mono (hg.ev wg ρ) (ha.ev wa ρ) (hb.ev wb ρ) v e

theorem Refines.fma {FS a a' b b' c c' t t'} (ha : Refines FS a a') (hb : Refines FS b b')
    (hc : Refines FS c c') (ht : (Term.mk (.Op3 .Fma a b c) t).WT → t' = t) :
    Refines FS (.mk (.Op3 .Fma a b c) t) (.mk (.Op3 .Fma a' b' c') t') := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · have ⟨w1, wa, wb, wc⟩ := WT_op3.1 w
    obtain ⟨wa', sa⟩ : a'.WT ∧ a'.ty = a.ty := ha.syn wa
    obtain ⟨wb', sb⟩ : b'.WT ∧ b'.ty = b.ty := hb.syn wb
    obtain ⟨wc', sc⟩ : c'.WT ∧ c'.ty = c.ty := hc.syn wc
    refine ⟨WT_op3.2 ⟨?_, wa', wb', wc'⟩, ht w⟩
    rw [sa, sb, sc, ht w]; exact w1
  · have ⟨_, wa, wb, wc⟩ := WT_op3.1 w
    simp only [ev, evOp3] at e ⊢
    exact evFma_mono (ha.ev wa ρ) (hb.ev wb ρ) (hc.ev wc ρ) v e

attribute [kanon_congr_lemma] Refines.op1 Refines.op2 Refines.ite Refines.fma

macro_rules | `(tactic| kanon_congr_side) => `(tactic| (
  intro w
  simp_all [Term.WT, Op1.WT, Op2.WT, Op3.WT, Term.ty_mk]))

end Kanon

namespace Kanon

end Kanon

namespace Kanon

open Classical

/-! ## Literals -/

theorem WT_bitVec {z t} :
    (Term.mk (.BitVec z) t).WT ↔
      ∃ n : Nat, 0 < n ∧ t = .TBitVector n ∧ 0 ≤ z ∧ z < 2 ^ n := by
  simp [Term.WT]

theorem eval_bitVec {FS ρ z t} (h : (Term.mk (.BitVec z) t).WT) :
    eval FS ρ (.mk (.BitVec z) t) = some (.bv t.width (BitVec.ofInt _ z)) := by
  rw [eval_eq_ev h, ev]

theorem eval_bitVec' {FS ρ z t n} (h : (Term.mk (.BitVec z) t).WT)
    (hn : t = .TBitVector n) :
    eval FS ρ (.mk (.BitVec z) t) = some (.bv n.toNat (BitVec.ofInt _ z)) := by
  rw [eval_bitVec h, Ty.width, size_of_ty_of_bits (.inl hn)]

theorem WT_locLit {z t} :
    (Term.mk (.LocLit z) t).WT ↔
      ∃ n : Nat, 0 < n ∧ t = .TLoc n ∧ 0 ≤ z ∧ z < 2 ^ n := by
  simp [Term.WT]

theorem eval_locLit {FS ρ z t} (h : (Term.mk (.LocLit z) t).WT) :
    eval FS ρ (.mk (.LocLit z) t) = some (.bv t.width (BitVec.ofInt _ z)) := by
  rw [eval_eq_ev h, ev]

theorem eval_locLit' {FS ρ z t n} (h : (Term.mk (.LocLit z) t).WT) (hn : t = .TLoc n) :
    eval FS ρ (.mk (.LocLit z) t) = some (.bv n.toNat (BitVec.ofInt _ z)) := by
  rw [eval_locLit h, Ty.width, size_of_ty_of_bits (.inr hn)]

theorem WT_bool {b t} : (Term.mk (.Bool b) t).WT ↔ t = .TBool := by simp [Term.WT]

theorem eval_bool {FS ρ b t} (h : t = .TBool) :
    eval FS ρ (.mk (.Bool b) t) = some (.bool b) := by
  subst h; rw [eval_eq_ev (WT_bool.2 rfl), ev]

@[simp] theorem v_true_WT : v_true.WT := by simp [v_true, Term.WT]
@[simp] theorem v_false_WT : v_false.WT := by simp [v_false, Term.WT]
@[simp] theorem v_true_ty : v_true.ty = .TBool := rfl
@[simp] theorem v_false_ty : v_false.ty = .TBool := rfl
@[simp] theorem eval_v_true {FS ρ} : eval FS ρ v_true = some (.bool true) := eval_bool rfl
@[simp] theorem eval_v_false {FS ρ} : eval FS ρ v_false = some (.bool false) := eval_bool rfl

theorem emod_two_pow_nonneg (z : Int) (n : Nat) : 0 ≤ z % 2 ^ n :=
  Int.emod_nonneg _ (Int.ne_of_gt (Int.pow_pos (by decide)))

theorem emod_two_pow_lt (z : Int) (n : Nat) : z % 2 ^ n < 2 ^ n :=
  Int.emod_lt_of_pos _ (Int.pow_pos (by decide))

theorem mk_masked_WT {n z : Int} (hn : 0 < n) : (mk_masked n z).WT := by
  refine WT_bitVec.2 ⟨n.toNat, by omega, by simp [Int.toNat_of_nonneg (Int.le_of_lt hn)], ?_, ?_⟩
  · exact emod_two_pow_nonneg _ _
  · exact emod_two_pow_lt _ _

@[simp] theorem mk_masked_ty {n z : Int} : (mk_masked n z).ty = .TBitVector n := rfl

theorem BitVec.ofInt_emod_two_pow {w : Nat} (z : Int) :
    BitVec.ofInt w (z % 2 ^ w) = BitVec.ofInt w z := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]

@[simp] theorem BitVec.ofInt_emod_two_pow' {w : Nat} (z : Int) :
    BitVec.ofInt w (z % ((2 ^ w : Nat) : Int)) = BitVec.ofInt w z := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]

theorem eval_mk_masked {FS ρ} {n z : Int} (hn : 0 < n) :
    eval FS ρ (mk_masked n z) = some (.bv n.toNat (BitVec.ofInt _ z)) := by
  rw [mk_masked, eval_bitVec' (n := n.toNat) (mk_masked_WT hn)
    (by simp [Int.toNat_of_nonneg (Int.le_of_lt hn)])]
  simp only [Int.toNat_natCast, BitVec.ofInt_emod_two_pow]

/-! ## Integers and bit-vectors -/

end Kanon

namespace Kanon

end Kanon
