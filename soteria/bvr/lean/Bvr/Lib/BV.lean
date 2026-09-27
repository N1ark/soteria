import Bvr.Lib.Sort
import Bvr.Lib.Cases

/-!
# Bit-vector terms by their values

`evalBV FS ρ n t` is the value of `t` as a `BitVec n`: `none` if `t` is poison,
or not a bit-vector of width `n`. Refinements of bit-vector terms reduce to
their values (`Refines.bv`), and the values of nodes are computed by the
`evalBV_*` equations, which only need the node to be well-typed: they turn a
refinement into an equation on `Option (BitVec n)`.
-/

namespace Bvr.Lib

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
theorem eval_bv {FS ρ t} {n : Nat} (hty : t.ty = .bitVector n) :
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
theorem evalBV_ne {FS ρ t} {n m : Nat} (hty : t.ty = .bitVector m) (h : m ≠ n) :
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
    (hty : s.WT → ∃ n : Int, s.ty = .bitVector n)
    (syn : s.WT → r.WT ∧ r.ty = s.ty)
    (sem : ∀ n : Nat, s.WT → s.ty = .bitVector n →
      ∀ ρ x, evalBV FS ρ n s = some x → evalBV FS ρ n r = some x) :
    Refines FS s r := by
  refine ⟨fun w => by simpa using syn w, fun ρ v e => ?_⟩
  have w := eval_WT e
  obtain ⟨n', hn'⟩ := hty w
  have hs := eval_hasSort e
  rw [hn'] at hs
  rcases v with _ | ⟨n, _⟩ | _ | _ | _ | _ <;> simp [Val.hasSort] at hs
  obtain ⟨rfl, -⟩ := hs
  have hn : s.ty = .bitVector n := hn'
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
    (hop : ∀ a b t, op.WT a b t ↔ (∃ n : Int, 0 < n ∧ a = .bitVector n) ∧ b = a ∧ t = a)
    (w : (Term.mk (.binop op a b) t).WT) :
    a.WT ∧ b.WT ∧ a.ty = t ∧ b.ty = t ∧ ∃ n : Nat, 0 < n ∧ t = .bitVector n := by
  have ⟨w1, wa, wb⟩ := WT_binop.1 w
  simp only [Ty.sort_eq, hop] at w1
  obtain ⟨⟨n, hn, ha⟩, hb, rfl⟩ := w1
  refine ⟨wa, wb, rfl, hb, n.toNat, by omega, ?_⟩
  rw [ha]; congr; omega

theorem bvBin_map {k : Nat} (F : ∀ {n : Nat}, BitVec n → BitVec n → Option Val)
    (a b : Option (BitVec k)) :
    bvBin F (a.map (Val.bv k)) (b.map (Val.bv k)) =
      (match a, b with | some x, some y => F x y | _, _ => none) := by
  cases a <;> cases b <;> simp [bvBin]

/-- The value of an arithmetic node. -/
theorem evalBV_binop {FS ρ n} {op : Binop} {a b : Term} {t : Ty}
    (hop : ∀ a b t, op.WT a b t ↔ (∃ n : Int, 0 < n ∧ a = .bitVector n) ∧ b = a ∧ t = a)
    (F : ∀ {m : Nat}, Option (BitVec m) → Option (BitVec m) → Option (BitVec m))
    (hF : ∀ {m : Nat} (x y : Option (BitVec m)),
      evBinop FS op (x.map (Val.bv m)) (y.map (Val.bv m)) = (F x y).map (Val.bv m))
    (hF0 : ∀ {m : Nat} (y : Option (BitVec m)), F none y = none)
    (w : (Term.mk (.binop op a b) t).WT) :
    evalBV FS ρ n (.mk (.binop op a b) t) = F (evalBV FS ρ n a) (evalBV FS ρ n b) := by
  obtain ⟨wa, wb, ha, hb, k, hk, rfl⟩ := WT_arith hop w
  have e : eval FS ρ (.mk (.binop op a b) (.bitVector k)) =
      (F (evalBV FS ρ k a) (evalBV FS ρ k b)).map (Val.bv k) := by
    rw [eval_binop w, eval_bv ha, eval_bv hb, hF]
  by_cases hkn : k = n
  · subst hkn
    cases h : F (evalBV FS ρ k a) (evalBV FS ρ k b) <;> rw [h] at e
    · cases e' : evalBV FS ρ k (.mk (.binop op a b) (.bitVector k))
      · rfl
      · rw [(evalBV_eq_some).1 e'] at e; cases e
    · exact (evalBV_eq_some).2 (by simpa using e)
  · rw [evalBV_ne (by rfl) hkn, evalBV_ne ha hkn, evalBV_ne hb hkn, hF0]

@[simp] theorem evalBV_add {FS ρ n c a b t} (w : (Term.mk (.binop (.add c) a b) t).WT) :
    evalBV FS ρ n (.mk (.binop (.add c) a b) t) =
      ckOp c BitVec.saddOverflow BitVec.uaddOverflow (· + ·) (evalBV FS ρ n a) (evalBV FS ρ n b) :=
  evalBV_binop (op := .add c) (fun _ _ _ => by simp [Binop.WT]) (fun {m} x y => ckOp (n := m) c BitVec.saddOverflow BitVec.uaddOverflow (· + ·) x y)
    (fun x y => by
      cases x <;> cases y <;> simp only [evBinop, checkedOp, bvBin, Option.map, ckOp] <;>
        simp <;> split <;> simp_all)
    (fun _ => rfl) w

@[simp] theorem evalBV_sub {FS ρ n c a b t} (w : (Term.mk (.binop (.sub c) a b) t).WT) :
    evalBV FS ρ n (.mk (.binop (.sub c) a b) t) =
      ckOp c BitVec.ssubOverflow BitVec.usubOverflow (· - ·) (evalBV FS ρ n a) (evalBV FS ρ n b) :=
  evalBV_binop (op := .sub c) (fun _ _ _ => by simp [Binop.WT]) (fun {m} x y => ckOp (n := m) c BitVec.ssubOverflow BitVec.usubOverflow (· - ·) x y)
    (fun x y => by
      cases x <;> cases y <;> simp only [evBinop, checkedOp, bvBin, Option.map, ckOp] <;>
        simp <;> split <;> simp_all)
    (fun _ => rfl) w

@[simp] theorem evalBV_mul {FS ρ n c a b t} (w : (Term.mk (.binop (.mul c) a b) t).WT) :
    evalBV FS ρ n (.mk (.binop (.mul c) a b) t) =
      ckOp c BitVec.smulOverflow BitVec.umulOverflow (· * ·) (evalBV FS ρ n a) (evalBV FS ρ n b) :=
  evalBV_binop (op := .mul c) (fun _ _ _ => by simp [Binop.WT]) (fun {m} x y => ckOp (n := m) c BitVec.smulOverflow BitVec.umulOverflow (· * ·) x y)
    (fun x y => by
      cases x <;> cases y <;> simp only [evBinop, checkedOp, bvBin, Option.map, ckOp] <;>
        simp <;> split <;> simp_all)
    (fun _ => rfl) w

@[simp] theorem evalBV_div {FS ρ n s a b t} (w : (Term.mk (.binop (.div s) a b) t).WT) :
    evalBV FS ρ n (.mk (.binop (.div s) a b) t) =
      binOp (fun x y => if s then x.smtSDiv y else x.smtUDiv y)
        (evalBV FS ρ n a) (evalBV FS ρ n b) :=
  evalBV_binop (op := .div s) (fun _ _ _ => by simp [Binop.WT])
    (fun x y => binOp (fun x y => if s then x.smtSDiv y else x.smtUDiv y) x y)
    (fun x y => by cases x <;> cases y <;> simp [evBinop, bvBin])
    (fun _ => rfl) w

/-- The value of a literal. -/
theorem evalBV_bitVec {FS ρ n z t} (w : (Term.mk (.bitVec z) t).WT) :
    evalBV FS ρ n (.mk (.bitVec z) t) =
      if (size_of_ty t).toNat = n then some (BitVec.ofInt n z) else none := by
  obtain ⟨k, hk, ht, -⟩ := WT_bitVec.1 w
  have e : eval FS ρ (.mk (.bitVec z) t) = some (.bv k (BitVec.ofInt k z)) := by
    rw [eval_eq_ev w]; rcases ht with rfl | rfl <;> simp [ev, Ty.width, size_of_ty]
  rw [size_of_ty_of_bits ht]
  simp only [Int.toNat_natCast]
  by_cases h : k = n
  · subst h; simpa using (evalBV_eq_some).2 e
  · simp only [h, ite_false]
    cases e' : evalBV FS ρ n (.mk (.bitVec z) t)
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
theorem eval_bool' {FS ρ t} (hty : t.ty = .bool) :
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

theorem evalBV_neg {FS ρ n c a t} (w : (Term.mk (.unop (.neg c) a) t).WT) :
    evalBV FS ρ n (.mk (.unop (.neg c) a) t) = negOp c (evalBV FS ρ n a) := by
  have ⟨w1, wa⟩ := WT_unop.1 w
  simp only [Unop.WT, Ty.sort_eq] at w1
  obtain ⟨k, hk, ha, rfl⟩ := w1
  obtain ⟨k, rfl⟩ : ∃ k' : Nat, k = k' := ⟨k.toNat, by omega⟩
  have e : eval FS ρ (.mk (.unop (.neg c) a) a.ty) =
      (negOp c (evalBV FS ρ k a)).map (Val.bv k) := by
    rw [eval_unop w, eval_bv ha]
    cases evalBV FS ρ k a <;> simp [evUnop]
    split <;> simp_all
  by_cases hkn : k = n
  · subst hkn
    cases h : negOp c (evalBV FS ρ k a) <;> rw [h] at e
    · cases e' : evalBV FS ρ k (.mk (.unop (.neg c) a) a.ty)
      · rfl
      · rw [(evalBV_eq_some).1 e'] at e; cases e
    · exact (evalBV_eq_some).2 (by simpa using e)
  · rw [evalBV_ne (by simpa using ha) hkn, evalBV_ne ha hkn]; rfl

theorem evalBV_ite {FS ρ n g a b t} (w : (Term.mk (.triop .ite g a b) t).WT) :
    evalBV FS ρ n (.mk (.triop .ite g a b) t) =
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

theorem evalBV_bvNot {FS ρ n a t} (w : (Term.mk (.unop .bvNot a) t).WT) :
    evalBV FS ρ n (.mk (.unop .bvNot a) t) = (evalBV FS ρ n a).map (~~~·) := by
  have ⟨w1, wa⟩ := WT_unop.1 w
  simp only [Unop.WT, Ty.sort_eq] at w1
  obtain ⟨k, hk, ha, rfl⟩ := w1
  obtain ⟨k, rfl⟩ : ∃ k' : Nat, k = k' := ⟨k.toNat, by omega⟩
  have e : eval FS ρ (.mk (.unop .bvNot a) a.ty) = ((evalBV FS ρ k a).map (~~~·)).map (Val.bv k) := by
    rw [eval_unop w, eval_bv ha]
    cases evalBV FS ρ k a <;> simp [evUnop]
  by_cases hkn : k = n
  · subst hkn
    cases h : evalBV FS ρ k a <;> rw [h] at e
    · cases e' : evalBV FS ρ k (.mk (.unop .bvNot a) a.ty)
      · rfl
      · rw [(evalBV_eq_some).1 e'] at e; cases e
    · exact (evalBV_eq_some).2 (by simpa using e)
  · rw [evalBV_ne (by simpa using ha) hkn, evalBV_ne ha hkn]; rfl

theorem evalBV_bvOfBool {FS ρ} {n : Nat} {m b t} (w : (Term.mk (.unop (.bvOfBool m) b) t).WT)
    (ht : t = .bitVector (n : Int)) :
    evalBV FS ρ n (.mk (.unop (.bvOfBool m) b) t) =
      (evalB FS ρ b).map (fun b => if b then 1 else 0) := by
  have ⟨w1, wb⟩ := WT_unop.1 w
  simp only [Unop.WT, Ty.sort_eq] at w1
  obtain ⟨hm, hb, rfl⟩ := w1
  simp at ht; subst ht
  have e : eval FS ρ (.mk (.unop (.bvOfBool (n : Int)) b) (.bitVector (n : Int))) =
      ((evalB FS ρ b).map (fun b => if b then (1 : BitVec n) else 0)).map (Val.bv n) := by
    rw [eval_unop w, eval_bool' hb]
    cases evalB FS ρ b <;> simp [evUnop]
  cases h : (evalB FS ρ b).map (fun b => if b then (1 : BitVec n) else 0) <;> rw [h] at e
  · cases e' : evalBV FS ρ n (.mk (.unop (.bvOfBool (n : Int)) b) (.bitVector (n : Int)))
    · rfl
    · rw [(evalBV_eq_some).1 e'] at e; cases e
  · exact (evalBV_eq_some).2 (by simpa using e)

theorem evalBV_extend {FS ρ} {n m : Nat} {s k a t}
    (w : (Term.mk (.unop (.bvExtend s k) a) t).WT) (ht : t = .bitVector (n : Int))
    (ha : a.ty = .bitVector (m : Int)) :
    evalBV FS ρ n (.mk (.unop (.bvExtend s k) a) t) =
      (evalBV FS ρ m a).map (fun x => if s then x.signExtend n else x.setWidth n) := by
  have ⟨w1, wa⟩ := WT_unop.1 w
  simp only [Unop.WT, Ty.sort_eq] at w1
  obtain ⟨m', -, ha', hk, rfl⟩ := w1
  rw [ha] at ha'; simp at ha'; subst ha'
  obtain ⟨k, rfl⟩ : ∃ k' : Nat, k = k' := ⟨k.toNat, by omega⟩
  simp at ht; obtain rfl : n = m + k := by omega
  have e : eval FS ρ (.mk (.unop (.bvExtend s (k : Int)) a) (.bitVector ((m : Int) + k))) =
      ((evalBV FS ρ m a).map
        (fun x => if s then x.signExtend (m + k) else x.setWidth (m + k))).map (Val.bv (m + k)) := by
    rw [eval_unop w, eval_bv ha]
    cases evalBV FS ρ m a <;> simp [evUnop]
  cases h : (evalBV FS ρ m a).map
      (fun x => if s then x.signExtend (m + k) else x.setWidth (m + k)) <;> rw [h] at e
  · cases e' : evalBV FS ρ (m + k) (.mk (.unop (.bvExtend s (k : Int)) a) (.bitVector ((m : Int) + k)))
    · rfl
    · rw [(evalBV_eq_some).1 e'] at e; cases e
  · exact (evalBV_eq_some).2 (by simpa using e)

/-! ## Values by the structure of terms -/

/-- The value of a term of width `n`, computed on the arithmetic nodes, the
literals and the conditionals of the term, and `evalBV` elsewhere. On
well-typed terms of width `n`, it is `evalBV` (`evalBV_den`). -/
noncomputable def den (FS : FloatSem) (ρ : Env) (n : Nat) : Term → Option (BitVec n)
  | .mk (.bitVec z) _ => some (BitVec.ofInt n z)
  | .mk (.binop op a b) t =>
      match op with
      | .add c =>
          ckOp c BitVec.saddOverflow BitVec.uaddOverflow (· + ·) (den FS ρ n a) (den FS ρ n b)
      | .sub c =>
          ckOp c BitVec.ssubOverflow BitVec.usubOverflow (· - ·) (den FS ρ n a) (den FS ρ n b)
      | .mul c =>
          ckOp c BitVec.smulOverflow BitVec.umulOverflow (· * ·) (den FS ρ n a) (den FS ρ n b)
      | .div s =>
          binOp (fun x y => if s then x.smtSDiv y else x.smtUDiv y) (den FS ρ n a) (den FS ρ n b)
      | op => evalBV FS ρ n (.mk (.binop op a b) t)
  | .mk (.unop op a) t =>
      match op with
      | .neg c => negOp c (den FS ρ n a)
      | .bvNot => (den FS ρ n a).map (~~~·)
      | .bvOfBool _ => (evalB FS ρ a).map (fun b => if b then 1 else 0)
      | .bvExtend s _ =>
          match a.ty with
          | .bitVector m => (den FS ρ m.toNat a).map (fun x => if s then x.signExtend n else x.setWidth n)
          | _ => none
      | op => evalBV FS ρ n (.mk (.unop op a) t)
  | .mk (.triop op g a b) t =>
      match op with
      | .ite =>
          match evalB FS ρ g with
          | some true => den FS ρ n a
          | some false => den FS ρ n b
          | none => none
      | op => evalBV FS ρ n (.mk (.triop op g a b) t)
  | t => evalBV FS ρ n t

theorem evalBV_den {FS ρ} {n : Nat} : ∀ (t : Term), t.WT → t.ty = .bitVector n →
    evalBV FS ρ n t = den FS ρ n t
  | .mk (.bitVec z) t, w, ht => by
      simp at ht; subst ht; rw [evalBV_bitVec w]; simp [den]
  | .mk (.binop op a b) t, w, ht => by
      have arith := fun (h : ∀ a b t, op.WT a b t ↔
          (∃ n : Int, 0 < n ∧ a = .bitVector n) ∧ b = a ∧ t = a) =>
        WT_arith h w
      cases op <;> simp only [den]
      all_goals first
        | rfl
        | (obtain ⟨wa, wb, ha, hb, -⟩ := arith (fun _ _ _ => by simp [Binop.WT])
           simp at ht; subst ht
           first
             | rw [evalBV_add w, evalBV_den a wa ha, evalBV_den b wb hb]
             | rw [evalBV_sub w, evalBV_den a wa ha, evalBV_den b wb hb]
             | rw [evalBV_mul w, evalBV_den a wa ha, evalBV_den b wb hb]
             | rw [evalBV_div w, evalBV_den a wa ha, evalBV_den b wb hb])
  | .mk (.unop op a) t, w, ht => by
      cases op <;> simp only [den]
      all_goals first
        | rfl
        | (have ⟨w1, wa⟩ := WT_unop.1 w
           simp only [Unop.WT, Ty.sort_eq] at w1
           obtain ⟨-, -, -, rfl⟩ := w1
           simp at ht
           first
             | rw [evalBV_neg w, evalBV_den a wa ht]
             | rw [evalBV_bvNot w, evalBV_den a wa ht])
        | exact evalBV_bvOfBool w ht
        | (have ⟨w1, wa⟩ := WT_unop.1 w
           simp only [Unop.WT, Ty.sort_eq] at w1
           obtain ⟨m, hm, ha, -, rfl⟩ := w1
           have ha' : a.ty = .bitVector ((m.toNat : Nat) : Int) := by rw [ha]; congr 1; omega
           simp only [ha]
           rw [evalBV_extend w (by simpa using ht) ha', evalBV_den a wa ha'])
  | .mk (.triop op g a b) t, w, ht => by
      cases op <;> simp only [den]
      all_goals first
        | rfl
        | (have ⟨w1, wg, wa, wb⟩ := WT_triop.1 w
           simp only [Triop.WT, Ty.sort_eq] at w1
           obtain ⟨-, hb, rfl⟩ := w1
           simp at ht
           rw [evalBV_ite w, evalBV_den a wa ht, evalBV_den b wb (by rw [hb, ht])])
  | .mk (.var _) _, _, _ | .mk (.bool _) _, _, _ | .mk (.float _) _, _, _
  | .mk (.ptr _ _) _, _, _ | .mk (.seq _) _, _, _ | .mk (.nop _ _) _, _, _
  | .mk (.exists_ _ _) _, _, _ | .mk (.extension _) _, _, _ => by simp [den]

/-- Refinement of bit-vector terms, by their structural values. -/
theorem Refines.den {FS : FloatSem} {s r : Term}
    (hty : s.WT → ∃ n : Int, s.ty = .bitVector n)
    (syn : s.WT → r.WT ∧ r.ty = s.ty)
    (sem : ∀ n : Nat, s.WT → s.ty = .bitVector n →
      ∀ ρ x, den FS ρ n s = some x → den FS ρ n r = some x) :
    Refines FS s r :=
  Refines.bv hty syn (fun n w ht ρ x h => by
    rw [evalBV_den s w ht] at h
    rw [evalBV_den r (syn w).1 (by rw [(syn w).2, ht])]
    exact sem n w ht ρ x h)

end Bvr.Lib
