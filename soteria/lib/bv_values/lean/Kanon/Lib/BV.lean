import Kanon.Lib.Sort
import Kanon.Lib.Cases

/-!
# Bit-vector terms by their values

`evalBV FS ρ n t` is the value of `t` as a `BitVec n`: `none` if `t` is poison,
or not a bit-vector of width `n`. Refinements of bit-vector terms reduce to
their values (`Refines.bv`), and the values of nodes are computed by the
`evalBV_*` equations, which only need the node to be well-typed: they turn a
refinement into an equation on `Option (BitVec n)`.
-/

namespace Kanon.Lib

open Classical

noncomputable def evalBV (FS : FloatSem) (ρ : Env) (n : Nat) (t : Term) : Option (BitVec n) :=
  match eval FS ρ t with
  | some (.bv m x) => if h : m = n then some (h ▸ x) else none
  | _ => none

theorem evalBV_eq_some {FS ρ n t} {x : BitVec n} :
    evalBV FS ρ n t = some x ↔ eval FS ρ t = some (.bv n x) := by
  unfold evalBV
  split
  · rename_i m y h
    rw [h]
    by_cases hm : m = n
    · subst hm; simp
    · simp [hm]
  · rename_i h
    constructor
    · intro e; cases e
    · intro e; exact absurd e (h _ _)

/-- A well-typed bit-vector term of width `n` is poison or has a value of width
`n`. -/
theorem eval_bv {FS ρ t} {n : Nat} (hty : t.ty = .TBitVector n) :
    eval FS ρ t = (evalBV FS ρ n t).map (Val.bv n) := by
  cases h : eval FS ρ t with
  | none => simp [evalBV, h]
  | some v =>
    have hs := eval_hasSort h
    rw [hty] at hs
    rcases v with _ | ⟨m, x⟩ | _ | _ | _ | _ <;> simp [Val.hasSort] at hs
    obtain ⟨hm, -⟩ := hs
    have : m = n := by omega
    subst this
    simp [(evalBV_eq_some).2 h]

/-- A bit-vector term of another width has no value at width `n`. -/
theorem evalBV_ne {FS ρ t} {n m : Nat} (hty : t.ty = .TBitVector m) (h : m ≠ n) :
    evalBV FS ρ n t = none := by
  cases e : evalBV FS ρ n t with
  | none => rfl
  | some x =>
    have := eval_bv (FS := FS) (ρ := ρ) hty
    rw [(evalBV_eq_some).1 e] at this
    cases e' : evalBV FS ρ m t <;> simp [e'] at this
    exact absurd this.1.symm h

/-- Refinement of bit-vector terms, by their values. -/
theorem Refines.bv {FS : FloatSem} {s r : Term}
    (hty : s.WT → ∃ n : Int, s.ty = .TBitVector n)
    (syn : s.WT → r.WT ∧ r.ty = s.ty)
    (sem : ∀ n : Nat, s.WT → s.ty = .TBitVector n →
      ∀ ρ x, evalBV FS ρ n s = some x → evalBV FS ρ n r = some x) :
    Refines FS s r := by
  refine ⟨fun w => by simpa using syn w, fun ρ v e => ?_⟩
  rw [← eval] at e ⊢
  have w := eval_WT e
  obtain ⟨n', hn'⟩ := hty w
  have hs := eval_hasSort e
  rw [hn'] at hs
  rcases v with _ | ⟨n, _⟩ | _ | _ | _ | _ <;> simp [Val.hasSort] at hs
  obtain ⟨rfl, -⟩ := hs
  have hn : s.ty = .TBitVector n := hn'
  have e' := e
  rw [eval_bv hn] at e
  cases h : evalBV FS ρ n s <;> rw [h] at e <;> simp at e
  subst e
  rw [eval_bv (by rw [(syn w).2, hn])]
  simp [sem n w hn ρ _ h]

/-! ## Values of nodes -/

/-- Checked arithmetic: poison when a checked flag overflows. -/
def ckOp {n : Nat} (c : Checked) (sovf uovf : BitVec n → BitVec n → Bool)
    (f : BitVec n → BitVec n → BitVec n) : Option (BitVec n) → Option (BitVec n) → Option (BitVec n)
  | some x, some y => if (c.signed && sovf x y) || (c.unsigned && uovf x y) then none else some (f x y)
  | _, _ => none

/-- Plain binary operations. -/
def binOp {n : Nat} (f : BitVec n → BitVec n → BitVec n) :
    Option (BitVec n) → Option (BitVec n) → Option (BitVec n)
  | some x, some y => some (f x y)
  | _, _ => none

@[simp] theorem ckOp_none_l {n c sovf uovf f} (b : Option (BitVec n)) :
    ckOp c sovf uovf f none b = none := rfl
@[simp] theorem ckOp_none_r {n c sovf uovf f} (a : Option (BitVec n)) :
    ckOp c sovf uovf f a none = none := by cases a <;> rfl
@[simp] theorem ckOp_some {n c sovf uovf f} (x y : BitVec n) :
    ckOp c sovf uovf f (some x) (some y) =
      if (c.signed && sovf x y) || (c.unsigned && uovf x y) then none else some (f x y) := rfl
@[simp] theorem binOp_none_l {n f} (b : Option (BitVec n)) : binOp f none b = none := rfl
@[simp] theorem binOp_none_r {n f} (a : Option (BitVec n)) : binOp f a none = none := by
  cases a <;> rfl
@[simp] theorem binOp_some {n f} (x y : BitVec n) : binOp f (some x) (some y) = some (f x y) :=
  rfl

/-- The operands of an arithmetic node have its type. -/
theorem WT_arith {op : Binop} {a b : Term} {t : Ty}
    (hop : ∀ a b t, op.WT a b t ↔ (∃ n : Int, 0 < n ∧ a = .TBitVector n) ∧ b = a ∧ t = a)
    (w : (Term.mk (.Binop op a b) t).WT) :
    a.WT ∧ b.WT ∧ a.ty = t ∧ b.ty = t ∧ ∃ n : Nat, 0 < n ∧ t = .TBitVector n := by
  have ⟨w1, wa, wb⟩ := WT_binop.1 w
  simp only [Ty.sort_eq, hop] at w1
  obtain ⟨⟨n, hn, ha⟩, hb, rfl⟩ := w1
  refine ⟨wa, wb, rfl, hb, n.toNat, by omega, ?_⟩
  rw [ha]; congr; omega

/-- The value of an arithmetic node. -/
theorem evalBV_binop {FS ρ n} {op : Binop} {a b : Term} {t : Ty}
    (hop : ∀ a b t, op.WT a b t ↔ (∃ n : Int, 0 < n ∧ a = .TBitVector n) ∧ b = a ∧ t = a)
    (F : ∀ {m : Nat}, Option (BitVec m) → Option (BitVec m) → Option (BitVec m))
    (hF : ∀ {m : Nat} (x y : Option (BitVec m)),
      evBinop FS op (x.map (Val.bv m)) (y.map (Val.bv m)) = (F x y).map (Val.bv m))
    (hF0 : ∀ {m : Nat} (y : Option (BitVec m)), F none y = none)
    (w : (Term.mk (.Binop op a b) t).WT) :
    evalBV FS ρ n (.mk (.Binop op a b) t) = F (evalBV FS ρ n a) (evalBV FS ρ n b) := by
  obtain ⟨wa, wb, ha, hb, k, hk, rfl⟩ := WT_arith hop w
  have e : eval FS ρ (.mk (.Binop op a b) (.TBitVector k)) =
      (F (evalBV FS ρ k a) (evalBV FS ρ k b)).map (Val.bv k) := by
    rw [eval_binop w, eval_bv ha, eval_bv hb, hF]
  by_cases hkn : k = n
  · subst hkn
    cases h : F (evalBV FS ρ k a) (evalBV FS ρ k b) <;> rw [h] at e
    · cases e' : evalBV FS ρ k (.mk (.Binop op a b) (.TBitVector k))
      · rfl
      · rw [(evalBV_eq_some).1 e'] at e; cases e
    · exact (evalBV_eq_some).2 (by simpa using e)
  · rw [evalBV_ne (by rfl) hkn, evalBV_ne ha hkn, evalBV_ne hb hkn, hF0]

@[simp] theorem evalBV_add {FS ρ n c a b t} (w : (Term.mk (.Binop (.Add c) a b) t).WT) :
    evalBV FS ρ n (.mk (.Binop (.Add c) a b) t) =
      ckOp c BitVec.saddOverflow BitVec.uaddOverflow (· + ·) (evalBV FS ρ n a) (evalBV FS ρ n b) :=
  evalBV_binop (op := .Add c) (fun _ _ _ => by simp [Binop.WT]) (fun {m} x y => ckOp (n := m) c BitVec.saddOverflow BitVec.uaddOverflow (· + ·) x y)
    (fun x y => by
      cases x <;> cases y <;> simp only [evBinop, checkedOp, bvBin, Option.map, ckOp] <;>
        simp <;> split <;> simp_all)
    (fun _ => rfl) w

@[simp] theorem evalBV_sub {FS ρ n c a b t} (w : (Term.mk (.Binop (.Sub c) a b) t).WT) :
    evalBV FS ρ n (.mk (.Binop (.Sub c) a b) t) =
      ckOp c BitVec.ssubOverflow BitVec.usubOverflow (· - ·) (evalBV FS ρ n a) (evalBV FS ρ n b) :=
  evalBV_binop (op := .Sub c) (fun _ _ _ => by simp [Binop.WT]) (fun {m} x y => ckOp (n := m) c BitVec.ssubOverflow BitVec.usubOverflow (· - ·) x y)
    (fun x y => by
      cases x <;> cases y <;> simp only [evBinop, checkedOp, bvBin, Option.map, ckOp] <;>
        simp <;> split <;> simp_all)
    (fun _ => rfl) w

@[simp] theorem evalBV_mul {FS ρ n c a b t} (w : (Term.mk (.Binop (.Mul c) a b) t).WT) :
    evalBV FS ρ n (.mk (.Binop (.Mul c) a b) t) =
      ckOp c BitVec.smulOverflow BitVec.umulOverflow (· * ·) (evalBV FS ρ n a) (evalBV FS ρ n b) :=
  evalBV_binop (op := .Mul c) (fun _ _ _ => by simp [Binop.WT]) (fun {m} x y => ckOp (n := m) c BitVec.smulOverflow BitVec.umulOverflow (· * ·) x y)
    (fun x y => by
      cases x <;> cases y <;> simp only [evBinop, checkedOp, bvBin, Option.map, ckOp] <;>
        simp <;> split <;> simp_all)
    (fun _ => rfl) w

@[simp] theorem evalBV_div {FS ρ n s a b t} (w : (Term.mk (.Binop (.Div s) a b) t).WT) :
    evalBV FS ρ n (.mk (.Binop (.Div s) a b) t) =
      binOp (fun x y => if s then x.smtSDiv y else x.smtUDiv y)
        (evalBV FS ρ n a) (evalBV FS ρ n b) :=
  evalBV_binop (op := .Div s) (fun _ _ _ => by simp [Binop.WT])
    (fun x y => binOp (fun x y => if s then x.smtSDiv y else x.smtUDiv y) x y)
    (fun x y => by cases x <;> cases y <;> simp [evBinop, bvBin])
    (fun _ => rfl) w

/-- The value of a literal. -/
theorem evalBV_bitVec {FS ρ n z t} (w : (Term.mk (.BitVec z) t).WT) :
    evalBV FS ρ n (.mk (.BitVec z) t) =
      if (size_of_ty t).toNat = n then some (BitVec.ofInt n z) else none := by
  obtain ⟨k, hk, ht, -⟩ := WT_bitVec.1 w
  have e : eval FS ρ (.mk (.BitVec z) t) = some (.bv k (BitVec.ofInt k z)) := by
    rw [eval_eq_ev w]; rcases ht with rfl | rfl <;> simp [ev, Ty.width, size_of_ty]
  rw [size_of_ty_of_bits ht]
  simp only [Int.toNat_natCast]
  by_cases h : k = n
  · subst h; simpa using (evalBV_eq_some).2 e
  · simp only [h, ite_false]
    cases e' : evalBV FS ρ n (.mk (.BitVec z) t)
    · rfl
    · rw [(evalBV_eq_some).1 e'] at e; cases e; exact absurd rfl h

/-! ## Booleans, and the remaining nodes -/

noncomputable def evalB (FS : FloatSem) (ρ : Env) (t : Term) : Option Bool :=
  match eval FS ρ t with
  | some (.bool b) => some b
  | _ => none

theorem evalB_eq_some {FS ρ t b} : evalB FS ρ t = some b ↔ eval FS ρ t = some (.bool b) := by
  unfold evalB
  cases eval FS ρ t with
  | none => simp
  | some v => cases v <;> simp

/-- A well-typed boolean term is poison or a boolean. -/
theorem eval_bool' {FS ρ t} (hty : t.ty = .TBool) :
    eval FS ρ t = (evalB FS ρ t).map Val.bool := by
  cases h : eval FS ρ t with
  | none => simp [evalB, h]
  | some v =>
    have hs := eval_hasSort h
    rw [hty] at hs
    rcases v with _ | _ | _ | _ | _ | _ <;> simp [Val.hasSort] at hs
    simp [(evalB_eq_some).2 h]

/-- Negation, checked against `INT_MIN`. -/
def negOp {n : Nat} (c : Bool) : Option (BitVec n) → Option (BitVec n)
  | some x => if c && x = BitVec.intMin n then none else some (-x)
  | none => none

@[simp] theorem negOp_none {n c} : negOp (n := n) c none = none := rfl
@[simp] theorem negOp_some {n c} (x : BitVec n) :
    negOp c (some x) = if c && x = BitVec.intMin n then none else some (-x) := rfl

theorem evalBV_neg {FS ρ n c a t} (w : (Term.mk (.Unop (.Neg c) a) t).WT) :
    evalBV FS ρ n (.mk (.Unop (.Neg c) a) t) = negOp c (evalBV FS ρ n a) := by
  have ⟨w1, wa⟩ := WT_unop.1 w
  simp only [Unop.WT, Ty.sort_eq] at w1
  obtain ⟨⟨k, hk, ha⟩, rfl⟩ := w1
  obtain ⟨k, rfl⟩ : ∃ k' : Nat, k = k' := ⟨k.toNat, by omega⟩
  have e : eval FS ρ (.mk (.Unop (.Neg c) a) a.ty) =
      (negOp c (evalBV FS ρ k a)).map (Val.bv k) := by
    rw [eval_unop w, eval_bv ha]
    cases evalBV FS ρ k a <;> simp [evUnop]
    split <;> simp_all
  by_cases hkn : k = n
  · subst hkn
    cases h : negOp c (evalBV FS ρ k a) <;> rw [h] at e
    · cases e' : evalBV FS ρ k (.mk (.Unop (.Neg c) a) a.ty)
      · rfl
      · rw [(evalBV_eq_some).1 e'] at e; cases e
    · exact (evalBV_eq_some).2 (by simpa using e)
  · rw [evalBV_ne (by simpa using ha) hkn, evalBV_ne ha hkn]; rfl

theorem evalBV_ite {FS ρ n g a b t} (w : (Term.mk (.Triop .Ite g a b) t).WT) :
    evalBV FS ρ n (.mk (.Triop .Ite g a b) t) =
      match evalB FS ρ g with
      | some true => evalBV FS ρ n a
      | some false => evalBV FS ρ n b
      | none => none := by
  have ⟨w1, wg, wa, wb⟩ := WT_triop.1 w
  simp only [Triop.WT, Ty.sort_eq] at w1
  obtain ⟨hg, hb, rfl⟩ := w1
  unfold evalBV
  rw [eval_ite w, eval_bool' hg]
  cases evalB FS ρ g with
  | none => simp
  | some v => cases v <;> simp

theorem evalBV_bvNot {FS ρ n a t} (w : (Term.mk (.Unop .BvNot a) t).WT) :
    evalBV FS ρ n (.mk (.Unop .BvNot a) t) = (evalBV FS ρ n a).map (~~~·) := by
  have ⟨w1, wa⟩ := WT_unop.1 w
  simp only [Unop.WT, Ty.sort_eq] at w1
  obtain ⟨⟨k, hk, ha⟩, rfl⟩ := w1
  obtain ⟨k, rfl⟩ : ∃ k' : Nat, k = k' := ⟨k.toNat, by omega⟩
  have e : eval FS ρ (.mk (.Unop .BvNot a) a.ty) = ((evalBV FS ρ k a).map (~~~·)).map (Val.bv k) := by
    rw [eval_unop w, eval_bv ha]
    cases evalBV FS ρ k a <;> simp [evUnop]
  by_cases hkn : k = n
  · subst hkn
    cases h : evalBV FS ρ k a <;> rw [h] at e
    · cases e' : evalBV FS ρ k (.mk (.Unop .BvNot a) a.ty)
      · rfl
      · rw [(evalBV_eq_some).1 e'] at e; cases e
    · exact (evalBV_eq_some).2 (by simpa using e)
  · rw [evalBV_ne (by simpa using ha) hkn, evalBV_ne ha hkn]; rfl

theorem evalBV_bvOfBool {FS ρ} {n : Nat} {m b t} (w : (Term.mk (.Unop (.BvOfBool m) b) t).WT)
    (ht : t = .TBitVector (n : Int)) :
    evalBV FS ρ n (.mk (.Unop (.BvOfBool m) b) t) =
      (evalB FS ρ b).map (fun b => if b then 1 else 0) := by
  have ⟨w1, wb⟩ := WT_unop.1 w
  simp only [Unop.WT, Ty.sort_eq] at w1
  obtain ⟨hm, hb, rfl⟩ := w1
  simp at ht; subst ht
  have e : eval FS ρ (.mk (.Unop (.BvOfBool (n : Int)) b) (.TBitVector (n : Int))) =
      ((evalB FS ρ b).map (fun b => if b then (1 : BitVec n) else 0)).map (Val.bv n) := by
    rw [eval_unop w, eval_bool' hb]
    cases evalB FS ρ b <;> simp [evUnop]
  cases h : (evalB FS ρ b).map (fun b => if b then (1 : BitVec n) else 0) <;> rw [h] at e
  · cases e' : evalBV FS ρ n (.mk (.Unop (.BvOfBool (n : Int)) b) (.TBitVector (n : Int)))
    · rfl
    · rw [(evalBV_eq_some).1 e'] at e; cases e
  · exact (evalBV_eq_some).2 (by simpa using e)

theorem evalBV_extend {FS ρ} {n m : Nat} {s k a t}
    (w : (Term.mk (.Unop (.BvExtend s k) a) t).WT) (ht : t = .TBitVector (n : Int))
    (ha : a.ty = .TBitVector (m : Int)) :
    evalBV FS ρ n (.mk (.Unop (.BvExtend s k) a) t) =
      (evalBV FS ρ m a).map (fun x => if s then x.signExtend n else x.setWidth n) := by
  have ⟨w1, wa⟩ := WT_unop.1 w
  simp only [Unop.WT, Ty.sort_eq] at w1
  obtain ⟨m', -, ha', hk, rfl⟩ := w1
  rw [ha] at ha'; simp at ha'; subst ha'
  obtain ⟨k, rfl⟩ : ∃ k' : Nat, k = k' := ⟨k.toNat, by omega⟩
  simp at ht; obtain rfl : n = m + k := by omega
  have e : eval FS ρ (.mk (.Unop (.BvExtend s (k : Int)) a) (.TBitVector ((m : Int) + k))) =
      ((evalBV FS ρ m a).map
        (fun x => if s then x.signExtend (m + k) else x.setWidth (m + k))).map (Val.bv (m + k)) := by
    rw [eval_unop w, eval_bv ha]
    cases evalBV FS ρ m a <;> simp [evUnop]
  cases h : (evalBV FS ρ m a).map
      (fun x => if s then x.signExtend (m + k) else x.setWidth (m + k)) <;> rw [h] at e
  · cases e' : evalBV FS ρ (m + k) (.mk (.Unop (.BvExtend s (k : Int)) a) (.TBitVector ((m : Int) + k)))
    · rfl
    · rw [(evalBV_eq_some).1 e'] at e; cases e
  · exact (evalBV_eq_some).2 (by simpa using e)

end Kanon.Lib
