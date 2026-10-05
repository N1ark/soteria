import Kanon.Lib.BV

/-!
# Terms by their structural values

`den FS ρ n t` is the value of a bit-vector term `t` at width `n`, and
`denB FS ρ t` the value of a boolean term, computed by the structure of the
term on the nodes whose value is a function of their operands', and by
`evalBV` / `evalB` elsewhere. On well-typed terms they are `evalBV` and `evalB`
(`evalBV_den`, `evalB_denB`), so refinements reduce to them (`Refines.den`,
`Refines.denB`).
-/

namespace Kanon.Lib

open Classical

theorem evalBV_of_eval {FS ρ n t} {o : Option (BitVec n)}
    (h : eval FS ρ t = o.map (Val.bv n)) : evalBV FS ρ n t = o := by
  cases o with
  | none => simp at h; simp [evalBV, h]
  | some x => exact (evalBV_eq_some).2 (by simpa using h)

theorem evalB_of_eval {FS ρ t} {o : Option Bool} (h : eval FS ρ t = o.map Val.bool) :
    evalB FS ρ t = o := by
  cases o with
  | none => simp at h; simp [evalB, h]
  | some x => exact (evalB_eq_some).2 (by simpa using h)

/-- `eval_bv`, at an integer width. -/
theorem eval_bv_int {FS ρ t} {m : Int} (hty : t.ty = .TBitVector m) :
    eval FS ρ t = (evalBV FS ρ m.toNat t).map (Val.bv m.toNat) := by
  by_cases hm : 0 ≤ m
  · exact eval_bv (by rw [hty]; congr 1; omega)
  · cases h : eval FS ρ t with
    | none => cases e : evalBV FS ρ m.toNat t <;> simp_all [evalBV]
    | some v =>
      have hs := eval_hasSort h
      rw [hty] at hs
      rcases v with _ | ⟨k, _⟩ | _ | _ | _ | _ <;> simp [Val.hasSort] at hs
      omega

/-- A term of a non-positive width has no value. -/
theorem evalBV_nonpos {FS ρ t} {m : Int} (hty : t.ty = .TBitVector m) (hm : ¬ 0 < m) (k : Nat) :
    evalBV FS ρ k t = none := by
  cases h : eval FS ρ t with
  | none => simp [evalBV, h]
  | some v =>
    have hs := eval_hasSort h
    rw [hty] at hs
    rcases v with _ | ⟨k, _⟩ | _ | _ | _ | _ <;> simp [Val.hasSort] at hs
    omega

/-! ## Bit-vector nodes -/

section
variable {FS : FloatSem} {ρ : Env} {n : Nat} {a b : Term} {t : Ty}

@[simp] theorem evalBV_bitAnd (w : (Term.mk (.Op2 .BitAnd a b) t).WT) :
    evalBV FS ρ n (.mk (.Op2 .BitAnd a b) t) =
      binOp (· &&& ·) (evalBV FS ρ n a) (evalBV FS ρ n b) := by
  refine evalBV_binop (op := .BitAnd) (fun _ _ _ => by simp [Op2.WT])
    (fun x y => binOp (· &&& ·) x y) ?_ (fun _ => rfl) w
  intro m x y; cases x <;> cases y <;> simp [evOp2, bvBin]
@[simp] theorem evalBV_bitOr (w : (Term.mk (.Op2 .BitOr a b) t).WT) :
    evalBV FS ρ n (.mk (.Op2 .BitOr a b) t) =
      binOp (· ||| ·) (evalBV FS ρ n a) (evalBV FS ρ n b) := by
  refine evalBV_binop (op := .BitOr) (fun _ _ _ => by simp [Op2.WT])
    (fun x y => binOp (· ||| ·) x y) ?_ (fun _ => rfl) w
  intro m x y; cases x <;> cases y <;> simp [evOp2, bvBin]
@[simp] theorem evalBV_bitXor (w : (Term.mk (.Op2 .BitXor a b) t).WT) :
    evalBV FS ρ n (.mk (.Op2 .BitXor a b) t) =
      binOp (· ^^^ ·) (evalBV FS ρ n a) (evalBV FS ρ n b) := by
  refine evalBV_binop (op := .BitXor) (fun _ _ _ => by simp [Op2.WT])
    (fun x y => binOp (· ^^^ ·) x y) ?_ (fun _ => rfl) w
  intro m x y; cases x <;> cases y <;> simp [evOp2, bvBin]
@[simp] theorem evalBV_shl (w : (Term.mk (.Op2 .Shl a b) t).WT) :
    evalBV FS ρ n (.mk (.Op2 .Shl a b) t) =
      binOp (· <<< ·) (evalBV FS ρ n a) (evalBV FS ρ n b) := by
  refine evalBV_binop (op := .Shl) (fun _ _ _ => by simp [Op2.WT])
    (fun x y => binOp (· <<< ·) x y) ?_ (fun _ => rfl) w
  intro m x y; cases x <;> cases y <;> simp [evOp2, bvBin]
@[simp] theorem evalBV_lShr (w : (Term.mk (.Op2 .LShr a b) t).WT) :
    evalBV FS ρ n (.mk (.Op2 .LShr a b) t) =
      binOp (· >>> ·) (evalBV FS ρ n a) (evalBV FS ρ n b) := by
  refine evalBV_binop (op := .LShr) (fun _ _ _ => by simp [Op2.WT])
    (fun x y => binOp (· >>> ·) x y) ?_ (fun _ => rfl) w
  intro m x y; cases x <;> cases y <;> simp [evOp2, bvBin]
@[simp] theorem evalBV_aShr (w : (Term.mk (.Op2 .AShr a b) t).WT) :
    evalBV FS ρ n (.mk (.Op2 .AShr a b) t) =
      binOp (·.sshiftRight' ·) (evalBV FS ρ n a) (evalBV FS ρ n b) := by
  refine evalBV_binop (op := .AShr) (fun _ _ _ => by simp [Op2.WT])
    (fun x y => binOp (·.sshiftRight' ·) x y) ?_ (fun _ => rfl) w
  intro m x y; cases x <;> cases y <;> simp [evOp2, bvBin]
@[simp] theorem evalBV_rem {s} (w : (Term.mk (.Op2 (.Rem s) a b) t).WT) :
    evalBV FS ρ n (.mk (.Op2 (.Rem s) a b) t) =
      binOp (fun x y => if s then x.srem y else x.umod y) (evalBV FS ρ n a) (evalBV FS ρ n b) := by
  refine evalBV_binop (op := (.Rem s)) (fun _ _ _ => by simp [Op2.WT])
    (fun x y => binOp (fun x y => if s then x.srem y else x.umod y) x y) ?_ (fun _ => rfl) w
  intro m x y; cases x <;> cases y <;> simp [evOp2, bvBin]
@[simp] theorem evalBV_mod (w : (Term.mk (.Op2 .Mod a b) t).WT) :
    evalBV FS ρ n (.mk (.Op2 .Mod a b) t) =
      binOp (·.smod ·) (evalBV FS ρ n a) (evalBV FS ρ n b) := by
  refine evalBV_binop (op := .Mod) (fun _ _ _ => by simp [Op2.WT])
    (fun x y => binOp (·.smod ·) x y) ?_ (fun _ => rfl) w
  intro m x y; cases x <;> cases y <;> simp [evOp2, bvBin]

end

theorem evalBV_extract {FS ρ} {n m : Nat} {i j a t}
    (w : (Term.mk (.Op1 (.BvExtract i j) a) t).WT) (ht : t = .TBitVector (n : Int))
    (ha : a.ty = .TBitVector (m : Int)) :
    evalBV FS ρ n (.mk (.Op1 (.BvExtract i j) a) t) =
      (evalBV FS ρ m a).map (fun x => x.extractLsb' i.toNat n) := by
  have ⟨w1, wa⟩ := WT_op1.1 w
  simp only [Op1.WT] at w1
  obtain ⟨m', ha', hi, hij, hj, rfl⟩ := w1
  rw [ha] at ha'; simp at ha'; subst ha'
  simp at ht
  apply evalBV_of_eval
  rw [eval_op1 w, eval_bv ha]
  have e : (j - i + 1).toNat = n := by omega
  cases evalBV FS ρ m a <;> simp [evOp1]
  rw [e]; simp

theorem evalBV_concat {FS ρ} {n m1 m2 : Nat} {a b t}
    (w : (Term.mk (.Op2 .BvConcat a b) t).WT) (ht : t = .TBitVector (n : Int))
    (ha : a.ty = .TBitVector (m1 : Int)) (hb : b.ty = .TBitVector (m2 : Int)) :
    evalBV FS ρ n (.mk (.Op2 .BvConcat a b) t) =
      (match evalBV FS ρ m1 a, evalBV FS ρ m2 b with
       | some x, some y => some ((x ++ y).setWidth n)
       | _, _ => none) := by
  have ⟨w1, wa, wb⟩ := WT_op2.1 w
  simp only [Op2.WT] at w1
  obtain ⟨k1, k2, -, -, ha', hb', rfl⟩ := w1
  rw [ha] at ha'; rw [hb] at hb'; simp at ha' hb'; subst ha' hb'
  simp at ht; obtain rfl : n = m1 + m2 := by omega
  apply evalBV_of_eval
  rw [eval_op2 w, eval_bv ha, eval_bv hb]
  cases evalBV FS ρ m1 a <;> cases evalBV FS ρ m2 b <;> simp [evOp2]

/-! ## Boolean nodes -/

/-- Parallel conjunction and disjunction: `false` (resp. `true`) wins over
poison. -/
def andB : Option Bool → Option Bool → Option Bool
  | some false, _ => some false
  | _, some false => some false
  | some true, some true => some true
  | _, _ => none

def orB : Option Bool → Option Bool → Option Bool
  | some true, _ => some true
  | _, some true => some true
  | some false, some false => some false
  | _, _ => none

/-- A binary predicate on values. -/
def binB {α : Type} (f : α → α → Bool) : Option α → Option α → Option Bool
  | some x, some y => some (f x y)
  | _, _ => none

@[simp] theorem binB_some {α f} (x y : α) : binB f (some x) (some y) = some (f x y) := rfl
@[simp] theorem binB_none_l {α f} (y : Option α) : binB f none y = none := rfl
@[simp] theorem binB_none_r {α f} (x : Option α) : binB f x none = none := by cases x <;> rfl

@[simp] theorem andB_some {x y : Bool} : andB (some x) (some y) = some (x && y) := by
  cases x <;> cases y <;> rfl
@[simp] theorem orB_some {x y : Bool} : orB (some x) (some y) = some (x || y) := by
  cases x <;> cases y <;> rfl

@[simp] theorem andB_false_l (b : Option Bool) : andB (some false) b = some false := rfl
@[simp] theorem andB_false_r (a : Option Bool) : andB a (some false) = some false := by
  rcases a with _ | _ | _ <;> rfl
@[simp] theorem andB_true_l (b : Option Bool) : andB (some true) b = b := by
  rcases b with _ | _ | _ <;> rfl
@[simp] theorem andB_true_r (a : Option Bool) : andB a (some true) = a := by
  rcases a with _ | _ | _ <;> rfl
@[simp] theorem andB_none_none : andB none none = none := rfl
@[simp] theorem orB_true_l (b : Option Bool) : orB (some true) b = some true := rfl
@[simp] theorem orB_true_r (a : Option Bool) : orB a (some true) = some true := by
  rcases a with _ | _ | _ <;> rfl
@[simp] theorem orB_false_l (b : Option Bool) : orB (some false) b = b := by
  rcases b with _ | _ | _ <;> rfl
@[simp] theorem orB_false_r (a : Option Bool) : orB a (some false) = a := by
  rcases a with _ | _ | _ <;> rfl
@[simp] theorem orB_none_none : orB none none = none := rfl

section
variable {FS : FloatSem} {ρ : Env} {a b g : Term} {t : Ty}

@[simp] theorem evalB_bool {c : Bool} (w : (Term.mk (.Bool c) t).WT) :
    evalB FS ρ (.mk (.Bool c) t) = some c :=
  evalB_of_eval (by rw [eval_bool (WT_bool.1 w)]; rfl)

theorem evalB_not (w : (Term.mk (.Op1 .Not a) t).WT) :
    evalB FS ρ (.mk (.Op1 .Not a) t) = (evalB FS ρ a).map (!·) := by
  have ⟨w1, wa⟩ := WT_op1.1 w
  simp only [Op1.WT] at w1
  apply evalB_of_eval
  rw [eval_op1 w, eval_bool' w1.1]
  rcases evalB FS ρ a with _ | _ | _ <;> simp [evOp1, KanonBool.pnot]

theorem evalB_and (w : (Term.mk (.Op2 .And a b) t).WT) :
    evalB FS ρ (.mk (.Op2 .And a b) t) = andB (evalB FS ρ a) (evalB FS ρ b) := by
  have ⟨w1, wa, wb⟩ := WT_op2.1 w
  simp only [Op2.WT] at w1
  apply evalB_of_eval
  rw [eval_op2 w, eval_bool' w1.1, eval_bool' w1.2.1]
  rcases evalB FS ρ a with _ | _ | _ <;> rcases evalB FS ρ b with _ | _ | _ <;>
    simp [evOp2, KanonBool.pand, andB]

theorem evalB_or (w : (Term.mk (.Op2 .Or a b) t).WT) :
    evalB FS ρ (.mk (.Op2 .Or a b) t) = orB (evalB FS ρ a) (evalB FS ρ b) := by
  have ⟨w1, wa, wb⟩ := WT_op2.1 w
  simp only [Op2.WT] at w1
  apply evalB_of_eval
  rw [eval_op2 w, eval_bool' w1.1, eval_bool' w1.2.1]
  rcases evalB FS ρ a with _ | _ | _ <;> rcases evalB FS ρ b with _ | _ | _ <;>
    simp [evOp2, KanonBool.por, orB]

theorem evalB_ite (w : (Term.mk (.Op3 .Ite g a b) t).WT) (ht : t = .TBool) :
    evalB FS ρ (.mk (.Op3 .Ite g a b) t) =
      match evalB FS ρ g with
      | some true => evalB FS ρ a
      | some false => evalB FS ρ b
      | none => none := by
  have ⟨w1, wg, wa, wb⟩ := WT_op3.1 w
  simp only [Op3.WT] at w1
  obtain ⟨hg, hb, rfl⟩ := w1
  unfold evalB
  rw [eval_ite w, eval_bool' hg]
  cases evalB FS ρ g with
  | none => simp
  | some v => cases v <;> simp

theorem evalB_eq_bool (w : (Term.mk (.Op2 .Eq a b) t).WT) (ha : a.ty = .TBool) :
    evalB FS ρ (.mk (.Op2 .Eq a b) t) = binB (fun x y => decide (x = y)) (evalB FS ρ a) (evalB FS ρ b) := by
  have ⟨w1, wa, wb⟩ := WT_op2.1 w
  simp only [Op2.WT] at w1
  apply evalB_of_eval
  rw [eval_op2 w, eval_bool' ha, eval_bool' (by rw [w1.1, ha])]
  cases evalB FS ρ a <;> cases evalB FS ρ b <;> simp [evOp2, KanonBool.peq]

theorem evalB_eq_bv {m : Int} (w : (Term.mk (.Op2 .Eq a b) t).WT) (ha : a.ty = .TBitVector m) :
    evalB FS ρ (.mk (.Op2 .Eq a b) t) =
      binB (fun x y => decide (x = y)) (evalBV FS ρ m.toNat a) (evalBV FS ρ m.toNat b) := by
  have ⟨w1, wa, wb⟩ := WT_op2.1 w
  simp only [Op2.WT] at w1
  apply evalB_of_eval
  rw [eval_op2 w, eval_bv_int ha, eval_bv_int (by rw [w1.1, ha])]
  cases evalBV FS ρ m.toNat a <;> cases evalBV FS ρ m.toNat b <;> simp [evOp2, KanonBool.peq]

/-- The predicates on bit-vectors. -/
def bvPred : Op2 → Option (∀ {n : Nat}, BitVec n → BitVec n → Bool)
  | .Lt s => some fun x y => if s then x.slt y else x.ult y
  | .Leq s => some fun x y => if s then x.sle y else x.ule y
  | .AddOvf s => some fun x y => if s then x.saddOverflow y else x.uaddOverflow y
  | .SubOvf s => some fun x y => if s then x.ssubOverflow y else x.usubOverflow y
  | .MulOvf s => some fun x y => if s then x.smulOverflow y else x.umulOverflow y
  | _ => none

theorem evalB_pred {op f} (hop : bvPred op = some f) {m : Int}
    (w : (Term.mk (.Op2 op a b) t).WT) (ha : a.ty = .TBitVector m) :
    evalB FS ρ (.mk (.Op2 op a b) t) =
      binB f (evalBV FS ρ m.toNat a) (evalBV FS ρ m.toNat b) := by
  have ⟨w1, wa, wb⟩ := WT_op2.1 w
  have hb : b.ty = a.ty := by
    cases op <;> simp [bvPred] at hop <;> simp only [Op2.WT] at w1 <;> exact w1.2.1
  apply evalB_of_eval
  rw [eval_op2 w, eval_bv_int ha, eval_bv_int (by rw [hb, ha])]
  cases op <;> simp [bvPred] at hop <;> subst hop <;>
    cases evalBV FS ρ m.toNat a <;> cases evalBV FS ρ m.toNat b <;> simp [evOp2, bvBin]

end

/-! ## Values by the structure of terms -/

mutual
/-- The value of a bit-vector term at width `n`. -/
noncomputable def den (FS : FloatSem) (ρ : Env) (n : Nat) : Term → Option (BitVec n)
  | .mk (.BitVec z) _ => some (BitVec.ofInt n z)
  | .mk (.Op2 op a b) t =>
      match op with
      | .Add c =>
          ckOp c BitVec.saddOverflow BitVec.uaddOverflow (· + ·) (den FS ρ n a) (den FS ρ n b)
      | .Sub c =>
          ckOp c BitVec.ssubOverflow BitVec.usubOverflow (· - ·) (den FS ρ n a) (den FS ρ n b)
      | .Mul c =>
          ckOp c BitVec.smulOverflow BitVec.umulOverflow (· * ·) (den FS ρ n a) (den FS ρ n b)
      | .Div s =>
          binOp (fun x y => if s then x.smtSDiv y else x.smtUDiv y) (den FS ρ n a) (den FS ρ n b)
      | .Rem s =>
          binOp (fun x y => if s then x.srem y else x.umod y) (den FS ρ n a) (den FS ρ n b)
      | .Mod => binOp (·.smod ·) (den FS ρ n a) (den FS ρ n b)
      | .BitAnd => binOp (· &&& ·) (den FS ρ n a) (den FS ρ n b)
      | .BitOr => binOp (· ||| ·) (den FS ρ n a) (den FS ρ n b)
      | .BitXor => binOp (· ^^^ ·) (den FS ρ n a) (den FS ρ n b)
      | .Shl => binOp (· <<< ·) (den FS ρ n a) (den FS ρ n b)
      | .LShr => binOp (· >>> ·) (den FS ρ n a) (den FS ρ n b)
      | .AShr => binOp (·.sshiftRight' ·) (den FS ρ n a) (den FS ρ n b)
      | .BvConcat =>
          match a.ty, b.ty with
          | .TBitVector m1, .TBitVector m2 =>
              match den FS ρ m1.toNat a, den FS ρ m2.toNat b with
              | some x, some y => some ((x ++ y).setWidth n)
              | _, _ => none
          | _, _ => none
      | op => evalBV FS ρ n (.mk (.Op2 op a b) t)
  | .mk (.Op1 op a) t =>
      match op with
      | .Neg c => negOp c (den FS ρ n a)
      | .BvNot => (den FS ρ n a).map (~~~·)
      | .BvOfBool _ => (denB FS ρ a).map (fun b => if b then 1 else 0)
      | .BvExtend s _ =>
          match a.ty with
          | .TBitVector m =>
              (den FS ρ m.toNat a).map (fun x => if s then x.signExtend n else x.setWidth n)
          | _ => none
      | .BvExtract i _ =>
          match a.ty with
          | .TBitVector m => (den FS ρ m.toNat a).map (fun x => x.extractLsb' i.toNat n)
          | _ => none
      | op => evalBV FS ρ n (.mk (.Op1 op a) t)
  | .mk (.Op3 op g a b) t =>
      match op with
      | .Ite =>
          match denB FS ρ g with
          | some true => den FS ρ n a
          | some false => den FS ρ n b
          | none => none
      | op => evalBV FS ρ n (.mk (.Op3 op g a b) t)
  | t => evalBV FS ρ n t

/-- The value of a boolean term. -/
noncomputable def denB (FS : FloatSem) (ρ : Env) : Term → Option Bool
  | .mk (.Bool b) _ => some b
  | .mk (.Op1 op a) t =>
      match op with
      | .Not => (denB FS ρ a).map (!·)
      | op => evalB FS ρ (.mk (.Op1 op a) t)
  | .mk (.Op2 op a b) t =>
      match op with
      | .And => andB (denB FS ρ a) (denB FS ρ b)
      | .Or => orB (denB FS ρ a) (denB FS ρ b)
      | .Eq =>
          match a.ty with
          | .TBitVector m =>
              if 0 < m then binB (fun x y => decide (x = y)) (den FS ρ m.toNat a) (den FS ρ m.toNat b)
              else none
          | .TBool => binB (fun x y => decide (x = y)) (denB FS ρ a) (denB FS ρ b)
          | _ => evalB FS ρ (.mk (.Op2 .Eq a b) t)
      | .Lt s =>
          match a.ty with
          | .TBitVector m =>
              if 0 < m then binB (fun x y => if s then x.slt y else x.ult y) (den FS ρ m.toNat a) (den FS ρ m.toNat b)
              else none
          | _ => evalB FS ρ (.mk (.Op2 (.Lt s) a b) t)
      | .Leq s =>
          match a.ty with
          | .TBitVector m =>
              if 0 < m then binB (fun x y => if s then x.sle y else x.ule y) (den FS ρ m.toNat a) (den FS ρ m.toNat b)
              else none
          | _ => evalB FS ρ (.mk (.Op2 (.Leq s) a b) t)
      | .AddOvf s =>
          match a.ty with
          | .TBitVector m =>
              if 0 < m then
                binB (fun x y => if s then x.saddOverflow y else x.uaddOverflow y)
                  (den FS ρ m.toNat a) (den FS ρ m.toNat b)
              else none
          | _ => evalB FS ρ (.mk (.Op2 (.AddOvf s) a b) t)
      | .SubOvf s =>
          match a.ty with
          | .TBitVector m =>
              if 0 < m then
                binB (fun x y => if s then x.ssubOverflow y else x.usubOverflow y)
                  (den FS ρ m.toNat a) (den FS ρ m.toNat b)
              else none
          | _ => evalB FS ρ (.mk (.Op2 (.SubOvf s) a b) t)
      | .MulOvf s =>
          match a.ty with
          | .TBitVector m =>
              if 0 < m then
                binB (fun x y => if s then x.smulOverflow y else x.umulOverflow y)
                  (den FS ρ m.toNat a) (den FS ρ m.toNat b)
              else none
          | _ => evalB FS ρ (.mk (.Op2 (.MulOvf s) a b) t)
      | op => evalB FS ρ (.mk (.Op2 op a b) t)
  | .mk (.Op3 op g a b) t =>
      match op with
      | .Ite =>
          match denB FS ρ g with
          | some true => denB FS ρ a
          | some false => denB FS ρ b
          | none => none
      | op => evalB FS ρ (.mk (.Op3 op g a b) t)
  | t => evalB FS ρ t
end

theorem WT_bv_of_arith {op : Op2} {a b : Term} {t : Ty} {n : Nat}
    (hop : ∀ a b t, op.WT a b t ↔ (∃ n : Int, 0 < n ∧ a = .TBitVector n) ∧ b = a ∧ t = a)
    (w : (Term.mk (.Op2 op a b) t).WT) (ht : t = .TBitVector (n : Int)) :
    a.WT ∧ b.WT ∧ a.ty = .TBitVector (n : Int) ∧ b.ty = .TBitVector (n : Int) := by
  obtain ⟨wa, wb, ha, hb, -⟩ := WT_arith hop w
  exact ⟨wa, wb, ha.trans ht, hb.trans ht⟩

/-- The operands of a predicate on bit-vectors. -/
theorem WT_pred {op : Op2} {a b : Term} {t : Ty}
    (hop : ∀ a b t, op.WT a b t ↔ (∃ n : Int, 0 < n ∧ a = .TBitVector n) ∧ b = a ∧ t = .TBool)
    (w : (Term.mk (.Op2 op a b) t).WT) :
    a.WT ∧ b.WT ∧ b.ty = a.ty ∧ ∃ m : Int, 0 < m ∧ a.ty = .TBitVector m := by
  have ⟨w1, wa, wb⟩ := WT_op2.1 w
  simp only [hop] at w1
  obtain ⟨⟨m, hm, ha⟩, hb, -⟩ := w1
  exact ⟨wa, wb, hb, m, hm, ha⟩

mutual
theorem evalBV_den {FS ρ} : ∀ {n : Nat} (t : Term), t.WT → t.ty = .TBitVector n →
    evalBV FS ρ n t = den FS ρ n t
  | n, .mk (.BitVec z) t, w, ht => by
      simp at ht; subst ht; rw [evalBV_bitVec w]; simp [den]
  | n, .mk (.Op2 op a b) t, w, ht => by
      have arith := fun (h : ∀ a b t, op.WT a b t ↔
          (∃ n : Int, 0 < n ∧ a = .TBitVector n) ∧ b = a ∧ t = a) =>
        WT_bv_of_arith h w (by simpa using ht)
      cases op <;> simp only [den]
      all_goals first
        | rfl
        | (obtain ⟨wa, wb, ha, hb⟩ := arith (fun _ _ _ => by simp [Op2.WT])
           first
             | rw [evalBV_add w, evalBV_den a wa ha, evalBV_den b wb hb]
             | rw [evalBV_sub w, evalBV_den a wa ha, evalBV_den b wb hb]
             | rw [evalBV_mul w, evalBV_den a wa ha, evalBV_den b wb hb]
             | rw [evalBV_div w, evalBV_den a wa ha, evalBV_den b wb hb]
             | rw [evalBV_rem w, evalBV_den a wa ha, evalBV_den b wb hb]
             | rw [evalBV_mod w, evalBV_den a wa ha, evalBV_den b wb hb]
             | rw [evalBV_bitAnd w, evalBV_den a wa ha, evalBV_den b wb hb]
             | rw [evalBV_bitOr w, evalBV_den a wa ha, evalBV_den b wb hb]
             | rw [evalBV_bitXor w, evalBV_den a wa ha, evalBV_den b wb hb]
             | rw [evalBV_shl w, evalBV_den a wa ha, evalBV_den b wb hb]
             | rw [evalBV_lShr w, evalBV_den a wa ha, evalBV_den b wb hb]
             | rw [evalBV_aShr w, evalBV_den a wa ha, evalBV_den b wb hb])
        | (have ⟨w1, wa, wb⟩ := WT_op2.1 w
           simp only [Op2.WT] at w1
           obtain ⟨m1, m2, h1, h2, ha, hb, rfl⟩ := w1
           have ha' : a.ty = .TBitVector ((m1.toNat : Nat) : Int) := by rw [ha, Int.toNat_of_nonneg (by omega)]
           have hb' : b.ty = .TBitVector ((m2.toNat : Nat) : Int) := by rw [hb, Int.toNat_of_nonneg (by omega)]
           simp only [ha, hb]
           rw [evalBV_concat w (by simpa using ht) ha' hb', evalBV_den a wa ha', evalBV_den b wb hb']
           cases den FS ρ m1.toNat a <;> cases den FS ρ m2.toNat b <;> simp)
  | n, .mk (.Op1 op a) t, w, ht => by
      cases op <;> simp only [den]
      all_goals first
        | rfl
        | (have ⟨w1, wa⟩ := WT_op1.1 w
           simp only [Op1.WT] at w1
           obtain ⟨-, -, -, rfl⟩ := w1
           simp at ht
           first
             | rw [evalBV_neg w, evalBV_den a wa ht]
             | rw [evalBV_bvNot w, evalBV_den a wa ht])
        | (have ⟨w1, wa⟩ := WT_op1.1 w
           simp only [Op1.WT] at w1
           rw [evalBV_bvOfBool w (by simpa using ht), evalB_denB a wa w1.2.1])
        | (have ⟨w1, wa⟩ := WT_op1.1 w
           simp only [Op1.WT] at w1
           obtain ⟨m, hm, ha, -, rfl⟩ := w1
           have ha' : a.ty = .TBitVector ((m.toNat : Nat) : Int) := by rw [ha, Int.toNat_of_nonneg (by omega)]
           simp only [ha]
           rw [evalBV_extend w (by simpa using ht) ha', evalBV_den a wa ha'])
        | (have ⟨w1, wa⟩ := WT_op1.1 w
           simp only [Op1.WT] at w1
           obtain ⟨m, ha, hi, hij, hj, rfl⟩ := w1
           have ha' : a.ty = .TBitVector ((m.toNat : Nat) : Int) := by rw [ha]; congr 1; omega
           simp only [ha]
           rw [evalBV_extract w (by simpa using ht) ha', evalBV_den a wa ha'])
  | n, .mk (.Op3 op g a b) t, w, ht => by
      cases op <;> simp only [den]
      all_goals first
        | rfl
        | (have ⟨w1, wg, wa, wb⟩ := WT_op3.1 w
           simp only [Op3.WT] at w1
           obtain ⟨hg, hb, rfl⟩ := w1
           simp at ht
           rw [evalBV_ite w, evalB_denB g wg hg, evalBV_den a wa ht, evalBV_den b wb (by rw [hb, ht])]; rfl)
  | _, .mk (.Var _) _, _, _ | _, .mk (.Bool _) _, _, _ | _, .mk (.Float _) _, _, _
  | _, .mk (.LocLit _) _, _, _ | _, .mk (.Seq _) _, _, _ | _, .mk (.OpN _ _) _, _, _
  | _, .mk (.Exists _ _) _, _, _ => by simp [den]

theorem evalB_denB {FS ρ} : ∀ (t : Term), t.WT → t.ty = .TBool → evalB FS ρ t = denB FS ρ t
  | .mk (.Bool c) t, w, ht => by simp [denB, evalB_bool w]
  | .mk (.Op1 op a) t, w, ht => by
      cases op <;> simp only [denB]
      all_goals first
        | rfl
        | (have ⟨w1, wa⟩ := WT_op1.1 w
           simp only [Op1.WT] at w1
           rw [evalB_not w, evalB_denB a wa w1.1])
  | .mk (.Op2 op a b) t, w, ht => by
      have pred := fun (h : ∀ a b t, op.WT a b t ↔
          (∃ n : Int, 0 < n ∧ a = .TBitVector n) ∧ b = a ∧ t = .TBool) => WT_pred h w
      cases op <;> simp only [denB]
      all_goals first
        | rfl
        | (have ⟨w1, wa, wb⟩ := WT_op2.1 w
           simp only [Op2.WT] at w1
           first
             | rw [evalB_and w, evalB_denB a wa w1.1, evalB_denB b wb w1.2.1]
             | rw [evalB_or w, evalB_denB a wa w1.1, evalB_denB b wb w1.2.1])
        | (obtain ⟨wa, wb, hb, m, hm, ha⟩ := pred (fun _ _ _ => by simp [Op2.WT])
           have ha' : a.ty = .TBitVector ((m.toNat : Nat) : Int) := by rw [ha, Int.toNat_of_nonneg (by omega)]
           have hb' : b.ty = .TBitVector ((m.toNat : Nat) : Int) := by rw [hb, ha']
           simp only [ha, hm, ite_true]
           rw [evalB_pred rfl w ha, evalBV_den a wa ha', evalBV_den b wb hb'])
        | (have ⟨w1, wa, wb⟩ := WT_op2.1 w
           simp only [Op2.WT] at w1
           obtain ⟨hab, -⟩ := w1
           cases hty : a.ty with
           | TBitVector m =>
             simp only
             by_cases hm : 0 < m
             · have ha' : a.ty = .TBitVector ((m.toNat : Nat) : Int) := by
                 rw [hty, Int.toNat_of_nonneg (by omega)]
               have hb' : b.ty = .TBitVector ((m.toNat : Nat) : Int) := by rw [hab, ha']
               simp only [hm, ite_true]
               rw [evalB_eq_bv w hty, evalBV_den a wa ha', evalBV_den b wb hb']
             · simp only [hm, ite_false]
               rw [evalB_eq_bv w hty, evalBV_nonpos hty hm]; rfl
           | TBool =>
             simp only
             rw [evalB_eq_bool w hty, evalB_denB a wa hty, evalB_denB b wb (by rw [hab, hty])]
           | _ => rfl)
  | .mk (.Op3 op g a b) t, w, ht => by
      cases op <;> simp only [denB]
      all_goals first
        | rfl
        | (have ⟨w1, wg, wa, wb⟩ := WT_op3.1 w
           simp only [Op3.WT] at w1
           obtain ⟨hg, hb, rfl⟩ := w1
           simp at ht
           rw [evalB_ite w ht, evalB_denB g wg hg, evalB_denB a wa ht,
             evalB_denB b wb (by rw [hb, ht])])
  | .mk (.Var _) _, _, _ | .mk (.BitVec _) _, _, _ | .mk (.Float _) _, _, _
  | .mk (.LocLit _) _, _, _ | .mk (.Seq _) _, _, _ | .mk (.OpN _ _) _, _, _
  | .mk (.Exists _ _) _, _, _ => by simp [denB]
end

/-- Refinement of bit-vector terms, by their structural values. -/
theorem Refines.den {FS : FloatSem} {s r : Term}
    (hty : s.WT → ∃ n : Int, s.ty = .TBitVector n)
    (syn : s.WT → r.WT ∧ r.ty = s.ty)
    (sem : ∀ n : Nat, s.WT → s.ty = .TBitVector n →
      ∀ ρ x, den FS ρ n s = some x → den FS ρ n r = some x) :
    Refines FS s r :=
  Refines.bv hty syn (fun n w ht ρ x h => by
    rw [evalBV_den s w ht] at h
    rw [evalBV_den r (syn w).1 (by rw [(syn w).2, ht])]
    exact sem n w ht ρ x h)

/-- Refinement of boolean terms, by their structural values. -/
theorem Refines.denB {FS : FloatSem} {s r : Term}
    (hty : s.WT → s.ty = .TBool)
    (syn : s.WT → r.WT ∧ r.ty = s.ty)
    (sem : s.WT → ∀ ρ b, denB FS ρ s = some b → denB FS ρ r = some b) :
    Refines FS s r := by
  refine ⟨fun w => by simpa using syn w, fun ρ v e => ?_⟩
  rw [← eval] at e ⊢
  have w := eval_WT e
  have hs := hty w
  have hr : r.ty = .TBool := by rw [(syn w).2, hs]
  rw [eval_bool' hs] at e
  cases h : evalB FS ρ s <;> rw [h] at e <;> simp at e
  subst e
  rw [evalB_denB s w hs] at h
  rw [eval_bool' hr, evalB_denB r (syn w).1 hr, sem w ρ _ h]
  rfl

end Kanon.Lib
