import KanonCore.Proof
import Tiny.Statements

/-!
Basic facts about typing and evaluation, used by the rule proofs, which Kanon's
rule tactics (`KanonCore.Proof`) are given by their attributes.
-/

namespace Tiny

open Classical Kanon BoolMod
open Kanon.Sem (OLe)

variable {ρ : Env}

@[simp] theorem ty_eq (v : Term) : ty v = v.ty := rfl
@[simp] theorem kind_eq (v : Term) : kind v = v.kind := rfl

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
  case Eq => obtain ⟨_, _, -, -, rfl⟩ := peq_eq_some.1 h; rfl
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
      simp only [ev, evUnop] at e
      rcases pnot_eq_some.1 e with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp_all [Val.ty]
  | .mk (.Binop op a b) T, v, w, e => by
      simp only [Term.WT] at w
      obtain ⟨w, -, -⟩ := w
      simp only [ev] at e
      rw [evBinop_ty e]
      cases op <;> simp_all [Binop.WT, Binop.resTy]
  | .mk (.Nop .Distinct l) T, v, w, e => by
      simp only [Term.WT] at w
      simp only [ev] at e
      cases h : evList ρ l <;> simp [h, pdistinct] at e
      subst e; simp_all [Val.ty]
  | .mk (.Ite g a b) T, v, w, e => by
      rw [WT_ite] at w
      obtain ⟨-, ha, hb, -, wa, wb⟩ := w
      simp only [ev] at e
      rcases pite_eq_some.1 e with ⟨-, e⟩ | ⟨-, -, e⟩
      · rw [ev_ty wa e, ha]; rfl
      · rw [ev_ty wb e, hb]; rfl

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

/-- The values of the variables of the language. -/
theorem env_cases (ρ : Env) (i : Int) :
    ρ i = none ∨ (∃ b, ρ i = some (.bool b)) ∨ ∃ z, ρ i = some (.int z) :=
  val_cases (ρ i)

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
@[simp] theorem evUnop_bool : evUnop .Not (some (.bool b)) = some (.bool !b) := by
  cases b <;> simp [evUnop, pnot]
@[simp] theorem evUnop_none {op} : evUnop op none = none := by cases op; simp [evUnop, pnot]
@[simp] theorem evUnop_int {op} : evUnop op (some (.int x)) = none := by
  cases op; simp [evUnop, pnot]
end

/-- `abs`, as `omega` understands it. -/
theorem abs_eq_max (z : Int) : abs z = max z (-z) := by
  simp only [abs, decide_eq_true_eq]; split <;> omega

/-! ## Monotonicity of the operators in poison -/

theorem evUnop_mono {op a a'} (h : OLe a a') : OLe (evUnop op a) (evUnop op a') := by
  cases op; exact pnot_mono h

theorem evBinop_mono {op a a' b b'} (ha : OLe a a') (hb : OLe b b') :
    OLe (evBinop op a b) (evBinop op a' b') := by
  cases op
  case And => exact pand_mono ha hb
  case Or => exact por_mono ha hb
  case Eq => exact peq_mono ha hb
  all_goals
    intro v e
    rcases a with _ | x
    · simp [evBinop, intOp, divOp] at e
    rcases b with _ | y
    · rcases x with _ | _ <;> simp [evBinop, intOp, divOp] at e
    rw [ha x rfl, hb y rfl]; exact e

/-! ## Congruence: refining the children of a node refines the node -/

theorem Refines.unop {op a a' t t'} (ha : Refines a a')
    (ht : (Term.mk (.Unop op a) t).WT → t' = t) :
    Refines (.mk (.Unop op a) t) (.mk (.Unop op a') t') := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · have ⟨w1, w2⟩ := WT_unop.1 w
    obtain ⟨w3, s3⟩ : a'.WT ∧ a'.ty = a.ty := ha.syn w2
    refine ⟨WT_unop.2 ⟨?_, w3⟩, ht w⟩
    rw [s3, ht w]; exact w1
  · exact evUnop_mono (op := op) (ha.ev (WT_unop.1 w).2 ρ) v e

theorem Refines.binop {op a a' b b' t t'} (ha : Refines a a')
    (hb : Refines b b') (ht : (Term.mk (.Binop op a b) t).WT → t' = t) :
    Refines (.mk (.Binop op a b) t) (.mk (.Binop op a' b') t') := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · have ⟨w1, wa, wb⟩ := WT_binop.1 w
    obtain ⟨wa', sa⟩ : a'.WT ∧ a'.ty = a.ty := ha.syn wa
    obtain ⟨wb', sb⟩ : b'.WT ∧ b'.ty = b.ty := hb.syn wb
    refine ⟨WT_binop.2 ⟨?_, wa', wb'⟩, ht w⟩
    rw [sa, sb, ht w]; exact w1
  · have ⟨_, wa, wb⟩ := WT_binop.1 w
    exact evBinop_mono (ha.ev wa ρ) (hb.ev wb ρ) v e

theorem Refines.ite {g g' a a' b b' t t'} (hg : Refines g g')
    (ha : Refines a a') (hb : Refines b b') (ht : (Term.mk (.Ite g a b) t).WT → t' = t) :
    Refines (.mk (.Ite g a b) t) (.mk (.Ite g' a' b') t') := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · have ⟨h1, h2, h3, wg, wa, wb⟩ := WT_ite.1 w
    obtain ⟨wg', sg⟩ : g'.WT ∧ g'.ty = g.ty := hg.syn wg
    obtain ⟨wa', sa⟩ : a'.WT ∧ a'.ty = a.ty := ha.syn wa
    obtain ⟨wb', sb⟩ : b'.WT ∧ b'.ty = b.ty := hb.syn wb
    refine ⟨WT_ite.2 ⟨by rw [sg, h1], by rw [sa, h2, ht w], by rw [sb, h3, ht w], wg', wa', wb'⟩,
      ht w⟩
  · have ⟨_, _, _, wg, wa, wb⟩ := WT_ite.1 w
    simp only [ev] at e ⊢
    exact pite_mono (hg.ev wg ρ) (ha.ev wa ρ) (hb.ev wb ρ) v e

/-- The type of a node given by its first operand, when it is refined. -/
theorem Refines.ty_binop_left {op a a' b t} (h : Refines a a') :
    (Term.mk (.Binop op a b) t).WT → ty a' = ty a :=
  fun w => (h.syn (WT_binop.1 w).2.1).2

/-- The type of a conditional, given by its branch, when it is refined. -/
theorem Refines.ty_ite {g a a' b t} (h : Refines a a') :
    (Term.mk (.Ite g a b) t).WT → ty a' = ty a :=
  fun w => (h.syn (WT_ite.1 w).2.2.2.2.1).2

/-! ## The lemmas of Kanon's rule tactics (`KanonCore.Proof`) -/

attribute [kanon_guards] equal var_equal divisible ty_eq
attribute [kanon_body] ty_eq mk_commut_binop of_bool
attribute [kanon_lits] v_true v_false int_z zero one tdiv trem ediv erem divisible abs_eq_max
  Term.ty_mk ty_eq
attribute [kanon_wt] WT_binop WT_unop WT_ite WT_bool WT_int WT_var Binop.WT Unop.WT Term.ty_mk
  ty_eq
attribute [kanon_atom_cases] ev_int ev_bool env_cases ev_opt
attribute [kanon_ev] ev evBinop
attribute [kanon_val] intOp_some intOp_none_l intOp_none_r intOp_bool_l intOp_bool_r divOp_some
  divOp_none_l divOp_none_r divOp_bool_l divOp_bool_r evUnop_bool evUnop_none evUnop_int
  intOp_ite_l intOp_ite_r divOp_ite_l divOp_ite_r evUnop_ite Val.ty Val.bool.injEq Val.int.injEq
attribute [kanon_congr_lemma] Refines.unop Refines.binop Refines.ite

end Tiny
