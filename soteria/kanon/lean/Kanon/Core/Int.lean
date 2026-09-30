import KanonCore.Lang

/-!
# The Int module (trial)

Mathematical integers, for any language that includes them (`HasInt`).
-/

namespace Kanon.Core

inductive IntOp where
  | lit (z : Int) | add
  deriving DecidableEq

class HasInt (L : Lang) where
  op : IntOp → L.Op
  view : L.Op → Option IntOp
  view_op : ∀ o, view (op o) = some o
  op_of_view : ∀ {o i}, view o = some i → o = op i
  tInt : L.Ty
  ofInt : Int → L.Val
  toInt : L.Val → Option Int
  toInt_ofInt : ∀ z, toInt (ofInt z) = some z
  ofInt_of_toInt : ∀ {v z}, toInt v = some z → ofInt z = v
  wt_lit : ∀ {z as t}, L.wt (op (.lit z)) as t ↔ as = [] ∧ t = tInt
  wt_add : ∀ {as t}, L.wt (op .add) as t ↔ as = [tInt, tInt] ∧ t = tInt
  den_lit : ∀ z, L.den (op (.lit z)) [] = some (ofInt z)
  den_add : ∀ v w, L.den (op .add) [v, w] =
    (do let a ← v.bind toInt; let b ← w.bind toInt; pure (a + b)).map ofInt

variable {L : Lang} [HasInt L]

open HasInt

def mkAdd (a b : Term L) : Term L := .app (op .add) [a, b] tInt

def iview : Term L → Option (IntOp × List (Term L))
  | .app o args _ => (view o).map (·, args)
  | _ => none

theorem iview_some {t : Term L} {i args} (h : iview t = some (i, args)) :
    ∃ ty, t = .app (op i) args ty := by
  cases t with
  | var => simp [iview] at h
  | app o as ty =>
    simp only [iview, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨i', hv, rfl, rfl⟩ := h
    exact ⟨ty, by rw [op_of_view hv]⟩

/-- `0 + x` is `x`. -/
def add.r_zero (v1 v2 : Term L) : Option (Term L) :=
  match iview v1 with
  | some (.lit 0, []) => some v2
  | _ => none

theorem add.r_zero.sound {v1 v2 r : Term L} (h : r_zero v1 v2 = some r) :
    Refines (mkAdd v1 v2) r := by
  simp only [r_zero] at h; split at h <;> simp at h; subst h
  obtain ⟨ty, rfl⟩ := iview_some ‹iview v1 = some (.lit 0, [])›
  refine ⟨fun w => ?_, fun ρ v e => ?_⟩
  · simp [mkAdd, Term.WT, Term.WTs, Term.tys, wt_add] at w
    exact ⟨w.2.2, w.1.2⟩
  · by_cases w : (mkAdd (.app (op (.lit 0)) [] ty) v2).WT
    · have w' := w
      simp [mkAdd, Term.WT, Term.WTs, Term.tys, wt_add] at w'
      rw [eval_of_WT w] at e; rw [eval_of_WT w'.2.2]
      simp only [mkAdd, ev, evs, den_add, den_lit, Option.bind_some, toInt_ofInt] at e
      cases hx : (ev ρ v2).bind toInt with
      | none => simp [hx] at e
      | some z =>
        cases ex : ev ρ v2 with
        | none => simp [ex] at hx
        | some x =>
          simp [ex] at hx; simp [ex, hx] at e; rw [← e, ofInt_of_toInt hx]
    · simp [eval, w] at e

end Kanon.Core
