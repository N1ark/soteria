import Bvr.Core.Lang

/-!
# The Bool module (trial)

The operators of booleans, and the laws that a language including them must
satisfy (`HasBool`). The rules of this module are proved once, for every such
language.
-/

namespace Bvr.Core

inductive BoolOp where
  | tt | ff | not | and | or
  deriving DecidableEq

/-- Non-strict conjunction: false as soon as one operand is. -/
def pand : Option Bool → Option Bool → Option Bool
  | some false, _ | _, some false => some false
  | some true, some true => some true
  | _, _ => none

class HasBool (L : Lang) where
  op : BoolOp → L.Op
  view : L.Op → Option BoolOp
  view_op : ∀ o, view (op o) = some o
  op_of_view : ∀ {o b}, view o = some b → o = op b
  tBool : L.Ty
  ofBool : Bool → L.Val
  toBool : L.Val → Option Bool
  toBool_ofBool : ∀ b, toBool (ofBool b) = some b
  ofBool_of_toBool : ∀ {v b}, toBool v = some b → ofBool b = v
  wt_lit : ∀ {b as t}, (b = .tt ∨ b = .ff) → L.wt (op b) as t → as = [] ∧ t = tBool
  wt_not : ∀ {as t}, L.wt (op .not) as t ↔ as = [tBool] ∧ t = tBool
  wt_and : ∀ {as t}, L.wt (op .and) as t ↔ as = [tBool, tBool] ∧ t = tBool
  wt_tt : L.wt (op .tt) [] tBool
  wt_ff : L.wt (op .ff) [] tBool
  den_tt : L.den (op .tt) [] = some (ofBool true)
  den_ff : L.den (op .ff) [] = some (ofBool false)
  den_not : ∀ v, L.den (op .not) [v] = (v.bind toBool).map (fun b => ofBool (!b))
  den_and : ∀ v w, L.den (op .and) [v, w] = (pand (v.bind toBool) (w.bind toBool)).map ofBool

variable {L : Lang} [HasBool L]

open HasBool

@[simp] theorem pand_false_left (b) : pand (some false) b = some false := by cases b <;> rfl
@[simp] theorem pand_false_right (a) : pand a (some false) = some false := by
  rcases a with _ | _ | _ <;> rfl
@[simp] theorem pand_true_left (b) : pand (some true) b = b := by rcases b with _ | _ | _ <;> rfl
@[simp] theorem pand_true_right (a) : pand a (some true) = a := by rcases a with _ | _ | _ <;> rfl
@[simp] theorem pand_self (a) : pand a a = a := by rcases a with _ | _ | _ <;> rfl

def mkBool (b : Bool) : Term L := .app (op (if b then .tt else .ff)) [] tBool
def mkAnd (a b : Term L) : Term L := .app (op .and) [a, b] tBool

/-- The Bool operator at the head of a term, and its operands. -/
def bview : Term L → Option (BoolOp × List (Term L))
  | .app o args _ => (view o).map (·, args)
  | _ => none

theorem bview_some {t : Term L} {b args} (h : bview t = some (b, args)) :
    ∃ ty, t = .app (op b) args ty := by
  cases t with
  | var => simp [bview] at h
  | app o as ty =>
    simp only [bview, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨b', hv, rfl, rfl⟩ := h
    exact ⟨ty, by rw [op_of_view hv]⟩

/-! ## The rules of `b_and`, whose spec is `mkAnd v1 v2` -/

open Classical in
noncomputable def b_and.r_same (v1 v2 : Term L) : Option (Term L) :=
  if v1 = v2 then some v1 else none

def b_and.r_false (v1 v2 : Term L) : Option (Term L) :=
  match bview v1, bview v2 with
  | some (.ff, []), _ | _, some (.ff, []) => some (mkBool false)
  | _, _ => none

def b_and.r_true (v1 v2 : Term L) : Option (Term L) :=
  match bview v1, bview v2 with
  | some (.tt, []), _ => some v2
  | _, some (.tt, []) => some v1
  | _, _ => none

/-! ## Their proofs -/

theorem and_WT {v1 v2 : Term L} :
    (mkAnd v1 v2).WT ↔ v1.ty = tBool ∧ v2.ty = tBool ∧ v1.WT ∧ v2.WT := by
  simp [mkAnd, Term.WT, Term.WTs, Term.tys, wt_and, and_assoc]

theorem and_eval {v1 v2 : Term L} {ρ : Env L} (w : (mkAnd v1 v2).WT) :
    eval ρ (mkAnd v1 v2) = (pand ((ev ρ v1).bind toBool) ((ev ρ v2).bind toBool)).map ofBool := by
  rw [eval_of_WT w]; simp [mkAnd, ev, evs, den_and]

theorem lit_ev {t : Term L} {b : BoolOp} {ρ : Env L} (h : bview t = some (b, [])) (w : t.WT) :
    (b = .tt ∨ b = .ff) → t.ty = tBool ∧ ev ρ t = some (ofBool (b = .tt)) := by
  intro hb
  obtain ⟨ty, rfl⟩ := bview_some h
  simp only [Term.WT, Term.tys] at w
  have := wt_lit hb w.1
  rcases hb with rfl | rfl <;> simp [Term.ty, this.2, ev, evs, den_tt, den_ff]

theorem mkBool_WT (b : Bool) : (mkBool b : Term L).WT ∧ (mkBool b : Term L).ty = tBool := by
  cases b <;> simp [mkBool, Term.WT, Term.WTs, Term.tys, Term.ty, wt_tt, wt_ff]

theorem mkBool_ev (b : Bool) {ρ : Env L} : ev ρ (mkBool b : Term L) = some (ofBool b) := by
  cases b <;> simp [mkBool, ev, evs, den_tt, den_ff]

/-- A term whose value is a boolean has that boolean's value. -/
theorem ofBool_ev {t : Term L} {ρ : Env L} {b} (h : (ev ρ t).bind toBool = some b) :
    ev ρ t = some (ofBool b) := by
  cases e : ev ρ t with
  | none => simp [e] at h
  | some x => simp [e] at h; rw [ofBool_of_toBool h]

/-- The value of a term, from the boolean it stands for. -/
theorem ev_of_map {t : Term L} {ρ : Env L} {v}
    (e : ((ev ρ t).bind toBool).map ofBool = some v) : ev ρ t = some v := by
  cases hx : (ev ρ t).bind toBool with
  | none => simp [hx] at e
  | some b => rw [ofBool_ev hx]; simpa [hx] using e

theorem b_and.r_same.sound {v1 v2 r : Term L} (h : r_same v1 v2 = some r) :
    Refines (mkAnd v1 v2) r := by
  simp only [r_same] at h; split at h <;> simp at h
  subst h; rename_i h; subst h
  refine ⟨fun w => ?_, fun ρ v e => ?_⟩
  · obtain ⟨h1, -, w1, -⟩ := and_WT.1 w; exact ⟨w1, h1⟩
  · by_cases w : (mkAnd v1 v1).WT
    · obtain ⟨-, -, w1, -⟩ := and_WT.1 w
      rw [and_eval w, pand_self] at e
      rw [eval_of_WT w1]; exact ev_of_map e
    · simp [eval, w] at e

theorem b_and.r_false.sound {v1 v2 r : Term L} (h : r_false v1 v2 = some r) :
    Refines (mkAnd v1 v2) r := by
  have hr : r = mkBool false := by
    simp only [r_false] at h; split at h <;> simp at h <;> exact h.symm
  subst hr
  refine ⟨fun _ => mkBool_WT false, fun ρ v e => ?_⟩
  by_cases w : (mkAnd v1 v2).WT
  · obtain ⟨-, -, w1, w2⟩ := and_WT.1 w
    rw [and_eval w] at e
    rw [eval_of_WT (mkBool_WT false).1, mkBool_ev]
    simp only [r_false] at h; split at h <;> simp at h
    · have := (lit_ev ‹bview v1 = some (.ff, [])› w1 (.inr rfl) (ρ := ρ)).2
      simpa [this, toBool_ofBool] using e
    · have := (lit_ev ‹bview v2 = some (.ff, [])› w2 (.inr rfl) (ρ := ρ)).2
      simpa [this, toBool_ofBool] using e
  · simp [eval, w] at e

theorem b_and.r_true.sound {v1 v2 r : Term L} (h : r_true v1 v2 = some r) :
    Refines (mkAnd v1 v2) r := by
  refine ⟨fun w => ?_, fun ρ v e => ?_⟩
  · obtain ⟨h1, h2, w1, w2⟩ := and_WT.1 w
    simp only [r_true] at h; split at h <;> simp at h <;> subst h
    · exact ⟨w2, h2⟩
    · exact ⟨w1, h1⟩
  · by_cases w : (mkAnd v1 v2).WT
    · obtain ⟨-, -, w1, w2⟩ := and_WT.1 w
      rw [and_eval w] at e
      simp only [r_true] at h; split at h <;> simp at h <;> subst h
      · have := (lit_ev ‹bview v1 = some (.tt, [])› w1 (.inl rfl) (ρ := ρ)).2
        simp only [this, Option.bind_some, toBool_ofBool, decide_true, pand_true_left,
          pand_true_right] at e
        rw [eval_of_WT w2]; exact ev_of_map e
      · have := (lit_ev ‹bview v2 = some (.tt, [])› w2 (.inl rfl) (ρ := ρ)).2
        simp only [this, Option.bind_some, toBool_ofBool, decide_true, pand_true_left,
          pand_true_right] at e
        rw [eval_of_WT w1]; exact ev_of_map e
    · simp [eval, w] at e

end Bvr.Core
