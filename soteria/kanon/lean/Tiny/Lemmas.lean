import Tiny.Statements

/-! Basic facts about typing and evaluation, used by the rule proofs. -/

namespace Tiny

open Classical

variable {ρ : Env}

@[simp] theorem ty_eq (v : Term) : ty v = v.ty := rfl
@[simp] theorem kind_eq (v : Term) : kind v = v.kind := rfl

theorem eval_WT {t v} (h : eval ρ t = some v) : t.WT := by
  unfold eval at h; split at h <;> simp_all

theorem eval_eq_ev {t} (h : t.WT) : eval ρ t = ev ρ t := by
  simp [eval, h]

/-! ## Typing -/

theorem WT_unop {op a t} : (Term.mk (.Unop op a) t).WT ↔ op.WT a.ty t ∧ a.WT := by
  simp [Term.WT]

theorem WT_binop {op a b t} :
    (Term.mk (.Binop op a b) t).WT ↔ op.WT a.ty b.ty t ∧ a.WT ∧ b.WT := by
  simp [Term.WT]

theorem WT_ite {g a b t} :
    (Term.mk (.Ite g a b) t).WT ↔
      g.ty = .TBool ∧ a.ty = t ∧ b.ty = t ∧ g.WT ∧ a.WT ∧ b.WT := by
  simp [Term.WT]

theorem WTList_iff {e : Ty} : ∀ {l : List Term}, Term.WTList e l ↔ ∀ t ∈ l, t.ty = e ∧ t.WT
  | [] => by simp [Term.WTList]
  | t :: ts => by simp [Term.WTList, WTList_iff (l := ts), and_assoc]

@[simp] theorem WT_bool {b t} : (Term.mk (.Bool b) t).WT ↔ t = .TBool := by simp [Term.WT]
@[simp] theorem WT_int {z t} : (Term.mk (.Int z) t).WT ↔ t = .TInt := by simp [Term.WT]
@[simp] theorem WT_var {x t} : (Term.mk (.Var x) t).WT := by simp [Term.WT]

@[simp] theorem v_true_WT : v_true.WT := by simp [v_true]
@[simp] theorem v_false_WT : v_false.WT := by simp [v_false]
@[simp] theorem int_z_WT {z} : (int_z z).WT := by simp [int_z]
@[simp] theorem v_true_ty : v_true.ty = .TBool := rfl
@[simp] theorem v_false_ty : v_false.ty = .TBool := rfl
@[simp] theorem int_z_ty {z} : (int_z z).ty = .TInt := rfl

theorem pand_eq_some {a b : Option Val} {v : Val} :
    pand a b = some v ↔
      (a = some (.bool false) ∧ v = .bool false) ∨ (b = some (.bool false) ∧ v = .bool false) ∨
        (a = some (.bool true) ∧ b = some (.bool true) ∧ v = .bool true) := by
  unfold pand; split <;> grind

theorem por_eq_some {a b : Option Val} {v : Val} :
    por a b = some v ↔
      (a = some (.bool true) ∧ v = .bool true) ∨ (b = some (.bool true) ∧ v = .bool true) ∨
        (a = some (.bool false) ∧ b = some (.bool false) ∧ v = .bool false) := by
  unfold por; split <;> grind

theorem intOp_eq_some {f x y v} :
    intOp f x y = some v ↔ ∃ a b, x = some (.int a) ∧ y = some (.int b) ∧ f a b = v := by
  unfold intOp; split <;> simp_all

theorem divOp_eq_some {f x y v} :
    divOp f x y = some v ↔
      ∃ a b, x = some (.int a) ∧ y = some (.int b) ∧ b ≠ 0 ∧ .int (f a b) = v := by
  unfold divOp; split
  · split <;> simp_all
  · simp_all

/-- The type of the result of an operator. -/
def Binop.resTy : Binop → Ty
  | .Plus | .Minus | .Times | .Div | .Rem | .Mod => .TInt
  | _ => .TBool

theorem evBinop_ty {op x y v} (h : evBinop op x y = some v) : v.ty = op.resTy := by
  cases op <;> simp only [evBinop] at h
  case And => rw [pand_eq_some] at h; rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> rfl
  case Or => rw [por_eq_some] at h; rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> rfl
  case Eq => unfold eqOp at h; split at h <;> simp at h; subst h; rfl
  all_goals first
    | (obtain ⟨_, _, -, -, rfl⟩ := intOp_eq_some.1 h; rfl)
    | (obtain ⟨_, _, -, -, -, rfl⟩ := divOp_eq_some.1 h; rfl)

/-- Evaluation respects types. -/
theorem ev_ty : ∀ {t : Term} {v : Val}, t.WT → ev ρ t = some v → v.ty = t.ty
  | .mk (.Var x) T, v, _, e => by
      simp only [ev] at e
      split at e
      · split at e <;> simp_all
      · simp at e
  | .mk (.Bool b) T, v, w, e => by
      simp only [ev, Option.some.injEq] at e; subst e; simp_all [Val.ty]
  | .mk (.Int z) T, v, w, e => by
      simp only [ev, Option.some.injEq] at e; subst e; simp_all [Val.ty]
  | .mk (.Unop op a) T, v, w, e => by
      simp only [Term.WT] at w
      cases op
      simp only [Unop.WT] at w
      simp only [ev] at e
      rcases h : ev ρ a with _ | ⟨_ | _⟩ <;> simp [h, evUnop] at e
      subst e; simp_all [Val.ty]
  | .mk (.Binop op a b) T, v, w, e => by
      simp only [Term.WT] at w
      obtain ⟨w, -, -⟩ := w
      simp only [ev] at e
      rw [evBinop_ty e]
      cases op <;> simp_all [Binop.WT, Binop.resTy]
  | .mk (.Nop .Distinct l) T, v, w, e => by
      simp only [Term.WT] at w
      simp only [ev] at e
      cases h : evList ρ l <;> simp [h] at e
      subst e; simp_all [Val.ty]
  | .mk (.Ite g a b) T, v, w, e => by
      rw [WT_ite] at w
      obtain ⟨-, ha, hb, -, wa, wb⟩ := w
      simp only [ev] at e
      split at e
      · rw [ev_ty wa e, ha]; rfl
      · rw [ev_ty wb e, hb]; rfl
      · simp at e

theorem ev_int {t : Term} (w : t.WT) (ht : t.ty = .TInt) :
    ev ρ t = none ∨ ∃ z, ev ρ t = some (.int z) := by
  rcases h : ev ρ t with _ | ⟨b | z⟩
  · exact .inl rfl
  · have := ev_ty w h; rw [ht] at this; simp [Val.ty] at this
  · exact .inr ⟨z, rfl⟩

theorem ev_bool {t : Term} (w : t.WT) (ht : t.ty = .TBool) :
    ev ρ t = none ∨ ev ρ t = some (.bool true) ∨ ev ρ t = some (.bool false) := by
  rcases h : ev ρ t with _ | ⟨b | z⟩
  · exact .inl rfl
  · cases b <;> simp
  · have := ev_ty w h; rw [ht] at this; simp [Val.ty] at this

theorem val_cases (a : Option Val) :
    a = none ∨ (∃ b, a = some (.bool b)) ∨ ∃ z, a = some (.int z) := by
  rcases a with _ | ⟨b | z⟩ <;> simp

theorem ev_opt (t : Term) : ev ρ t = none ∨ ∃ x, ev ρ t = some x := by
  cases ev ρ t <;> simp

/-! ## Conditionals, lifted out of the operators -/

section
variable {c : Prop} [Decidable c] {a b x : Option Val}

@[simp] theorem intOp_ite_l {f} :
    intOp f (if c then a else b) x = if c then intOp f a x else intOp f b x := by split <;> rfl
@[simp] theorem intOp_ite_r {f} :
    intOp f x (if c then a else b) = if c then intOp f x a else intOp f x b := by split <;> rfl
@[simp] theorem divOp_ite_l {f} :
    divOp f (if c then a else b) x = if c then divOp f a x else divOp f b x := by split <;> rfl
@[simp] theorem divOp_ite_r {f} :
    divOp f x (if c then a else b) = if c then divOp f x a else divOp f x b := by split <;> rfl
@[simp] theorem eqOp_ite_l : eqOp (if c then a else b) x = if c then eqOp a x else eqOp b x := by
  split <;> rfl
@[simp] theorem eqOp_ite_r : eqOp x (if c then a else b) = if c then eqOp x a else eqOp x b := by
  split <;> rfl
@[simp] theorem pand_ite_l : pand (if c then a else b) x = if c then pand a x else pand b x := by
  split <;> rfl
@[simp] theorem pand_ite_r : pand x (if c then a else b) = if c then pand x a else pand x b := by
  split <;> rfl
@[simp] theorem por_ite_l : por (if c then a else b) x = if c then por a x else por b x := by
  split <;> rfl
@[simp] theorem por_ite_r : por x (if c then a else b) = if c then por x a else por x b := by
  split <;> rfl
@[simp] theorem evUnop_ite {op} : evUnop op (if c then a else b) = if c then evUnop op a else evUnop op b := by
  split <;> rfl
end

/-! ## The operators on values, by cases -/

section
variable {f : Int → Int → Val} {g : Int → Int → Int} {x y : Int} {b : Bool} {a c : Option Val}
@[simp] theorem intOp_some : intOp f (some (.int x)) (some (.int y)) = some (f x y) := rfl
@[simp] theorem intOp_none_l : intOp f none c = none := rfl
@[simp] theorem intOp_none_r : intOp f a none = none := by rcases a with _ | ⟨_ | _⟩ <;> rfl
@[simp] theorem intOp_bool_l : intOp f (some (.bool b)) c = none := rfl
@[simp] theorem intOp_bool_r : intOp f a (some (.bool b)) = none := by
  rcases a with _ | ⟨_ | _⟩ <;> rfl
@[simp] theorem divOp_some :
    divOp g (some (.int x)) (some (.int y)) = if y = 0 then none else some (.int (g x y)) := rfl
@[simp] theorem divOp_none_l : divOp g none c = none := rfl
@[simp] theorem divOp_none_r : divOp g a none = none := by rcases a with _ | ⟨_ | _⟩ <;> rfl
@[simp] theorem divOp_bool_l : divOp g (some (.bool b)) c = none := rfl
@[simp] theorem divOp_bool_r : divOp g a (some (.bool b)) = none := by
  rcases a with _ | ⟨_ | _⟩ <;> rfl
@[simp] theorem eqOp_some {u w : Val} : eqOp (some u) (some w) = some (.bool (decide (u = w))) := rfl
@[simp] theorem eqOp_none_l : eqOp none c = none := rfl
@[simp] theorem eqOp_none_r : eqOp a none = none := by rcases a <;> rfl
@[simp] theorem evUnop_bool : evUnop .Not (some (.bool b)) = some (.bool !b) := rfl
@[simp] theorem evUnop_none {op} : evUnop op none = none := by cases op; rfl
@[simp] theorem evUnop_int {op} : evUnop op (some (.int x)) = none := by cases op; rfl
end

/-- `abs`, as `omega` understands it. -/
theorem abs_eq_max (z : Int) : abs z = max z (-z) := by
  simp only [abs, decide_eq_true_eq]; split <;> omega

/-! ## Evaluation of well-typed nodes -/

theorem eval_unop {op a t} (h : (Term.mk (.Unop op a) t).WT) :
    eval ρ (.mk (.Unop op a) t) = evUnop op (eval ρ a) := by
  rw [eval_eq_ev h, eval_eq_ev (WT_unop.1 h).2, ev]

theorem eval_binop {op a b t} (h : (Term.mk (.Binop op a b) t).WT) :
    eval ρ (.mk (.Binop op a b) t) = evBinop op (eval ρ a) (eval ρ b) := by
  have := WT_binop.1 h
  rw [eval_eq_ev h, eval_eq_ev this.2.1, eval_eq_ev this.2.2, ev]

theorem eval_ite {g a b t} (h : (Term.mk (.Ite g a b) t).WT) :
    eval ρ (.mk (.Ite g a b) t) =
      match eval ρ g with
      | some (.bool true) => eval ρ a
      | some (.bool false) => eval ρ b
      | _ => none := by
  have := WT_ite.1 h
  rw [eval_eq_ev h, eval_eq_ev this.2.2.2.1, eval_eq_ev this.2.2.2.2.1,
    eval_eq_ev this.2.2.2.2.2]
  rw [ev]; rfl

/-! ## Refinement -/

/-- `a` is poison or equal to `b`. -/
def OLe (a b : Option Val) : Prop := ∀ v, a = some v → b = some v

theorem Refines.syn {a b : Term} (h : Refines a b) (w : a.WT) : b.WT ∧ b.ty = a.ty := h.1 w

theorem Refines.sem {a b : Term} (h : Refines a b) (ρ : Env) : OLe (eval ρ a) (eval ρ b) :=
  h.2 ρ

theorem ty_refines {a a' : Term} (ha : Refines a a') (w : a.WT) : a'.ty = a.ty :=
  (ha.syn w).2

/-- To prove a refinement, one may use the typing half in the value half. -/
theorem Refines.intro {a b : Term} (syn : a.WT → b.WT ∧ b.ty = a.ty)
    (sem : ∀ ρ v, a.WT → b.WT → ev ρ a = some v → ev ρ b = some v) : Refines a b := by
  refine ⟨syn, fun ρ v e => ?_⟩
  have w := eval_WT e
  have w' := (syn w).1
  rw [eval_eq_ev w] at e; rw [eval_eq_ev w']
  exact sem ρ v w w' e

theorem Refines.of_WT {s r : Term} (h : s.WT → Refines s r) : Refines s r := by
  by_cases w : s.WT
  · exact h w
  · exact ⟨fun h => absurd h w, fun ρ v e => absurd (eval_WT e) w⟩

/-- `Refines.trans`, with the lifting first so that it determines the middle
term. -/
theorem Refines.of_lift {s m r : Term} (hl : Refines m r) (hm : Refines s m) : Refines s r :=
  Refines.trans hm hl

/-! ## Monotonicity of the operators in poison -/

theorem pand_mono {a a' b b'} (ha : OLe a a') (hb : OLe b b') : OLe (pand a b) (pand a' b') := by
  intro v e
  rw [pand_eq_some] at *
  rcases e with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h1, h2, rfl⟩
  · exact Or.inl ⟨ha _ h, rfl⟩
  · exact Or.inr (Or.inl ⟨hb _ h, rfl⟩)
  · exact Or.inr (Or.inr ⟨ha _ h1, hb _ h2, rfl⟩)

theorem por_mono {a a' b b'} (ha : OLe a a') (hb : OLe b b') : OLe (por a b) (por a' b') := by
  intro v e
  rw [por_eq_some] at *
  rcases e with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h1, h2, rfl⟩
  · exact Or.inl ⟨ha _ h, rfl⟩
  · exact Or.inr (Or.inl ⟨hb _ h, rfl⟩)
  · exact Or.inr (Or.inr ⟨ha _ h1, hb _ h2, rfl⟩)

theorem evUnop_mono {op a a'} (h : OLe a a') : OLe (evUnop op a) (evUnop op a') := by
  intro v e
  cases a with
  | none => cases op; simp [evUnop] at e
  | some x => rw [h x rfl]; exact e

theorem evBinop_mono {op a a' b b'} (ha : OLe a a') (hb : OLe b b') :
    OLe (evBinop op a b) (evBinop op a' b') := by
  cases op
  case And => exact pand_mono ha hb
  case Or => exact por_mono ha hb
  all_goals
    intro v e
    rcases a with _ | x
    · simp [evBinop, intOp, divOp, eqOp] at e
    rcases b with _ | y
    · rcases x with _ | _ <;> simp [evBinop, intOp, divOp, eqOp] at e
    rw [ha x rfl, hb y rfl]; exact e

/-! ## Congruence: refining the children of a node refines the node -/

theorem Refines.unop {op a a' t t'} (ha : Refines a a')
    (ht : (Term.mk (.Unop op a) t).WT → t' = t) :
    Refines (.mk (.Unop op a) t) (.mk (.Unop op a') t') := by
  refine ⟨fun w => ?_, fun ρ v e => ?_⟩
  · have ⟨w1, w2⟩ := WT_unop.1 w
    have ⟨w3, s3⟩ := ha.syn w2
    refine ⟨WT_unop.2 ⟨?_, w3⟩, ht w⟩
    rw [s3, ht w]; exact w1
  · have w := eval_WT e
    have ⟨w1, w2⟩ := WT_unop.1 w
    have ⟨w3, s3⟩ := ha.syn w2
    have w' : (Term.mk (.Unop op a') t').WT := WT_unop.2 ⟨by rw [s3, ht w]; exact w1, w3⟩
    rw [eval_unop w] at e; rw [eval_unop w']
    exact evUnop_mono (ha.sem ρ) v e

theorem Refines.binop {op a a' b b' t t'} (ha : Refines a a') (hb : Refines b b')
    (ht : (Term.mk (.Binop op a b) t).WT → t' = t) :
    Refines (.mk (.Binop op a b) t) (.mk (.Binop op a' b') t') := by
  have syn : (Term.mk (.Binop op a b) t).WT →
      (Term.mk (.Binop op a' b') t').WT ∧ t' = t := fun w => by
    have ⟨w1, wa, wb⟩ := WT_binop.1 w
    have ⟨wa', sa⟩ := ha.syn wa
    have ⟨wb', sb⟩ := hb.syn wb
    refine ⟨WT_binop.2 ⟨?_, wa', wb'⟩, ht w⟩
    rw [sa, sb, ht w]; exact w1
  refine ⟨syn, fun ρ v e => ?_⟩
  have w := eval_WT e
  rw [eval_binop w] at e; rw [eval_binop (syn w).1]
  exact evBinop_mono (ha.sem ρ) (hb.sem ρ) v e

theorem Refines.ite {g g' a a' b b' t t'} (hg : Refines g g') (ha : Refines a a')
    (hb : Refines b b') (ht : (Term.mk (.Ite g a b) t).WT → t' = t) :
    Refines (.mk (.Ite g a b) t) (.mk (.Ite g' a' b') t') := by
  have syn : (Term.mk (.Ite g a b) t).WT → (Term.mk (.Ite g' a' b') t').WT ∧ t' = t := fun w => by
    have ⟨h1, h2, h3, wg, wa, wb⟩ := WT_ite.1 w
    have ⟨wg', sg⟩ := hg.syn wg
    have ⟨wa', sa⟩ := ha.syn wa
    have ⟨wb', sb⟩ := hb.syn wb
    refine ⟨WT_ite.2 ⟨by rw [sg, h1], by rw [sa, h2, ht w], by rw [sb, h3, ht w], wg', wa', wb'⟩,
      ht w⟩
  refine ⟨syn, fun ρ v e => ?_⟩
  have w := eval_WT e
  rw [eval_ite w] at e; rw [eval_ite (syn w).1]
  have := hg.sem ρ
  split at e
  · rename_i h; rw [this _ h]; exact ha.sem ρ v e
  · rename_i h; rw [this _ h]; exact hb.sem ρ v e
  · simp at e

/-- The type of a node given by its first operand, when it is refined. -/
theorem Refines.ty_binop_left {op a a' b t} (h : Refines a a') :
    (Term.mk (.Binop op a b) t).WT → ty a' = ty a :=
  fun w => (h.syn (WT_binop.1 w).2.1).2

/-- The type of a conditional, given by its branch, when it is refined. -/
theorem Refines.ty_ite {g a a' b t} (h : Refines a a') :
    (Term.mk (.Ite g a b) t).WT → ty a' = ty a :=
  fun w => (h.syn (WT_ite.1 w).2.2.2.2.1).2

end Tiny
