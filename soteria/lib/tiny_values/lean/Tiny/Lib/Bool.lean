import KanonCore.BoolMod
import Tiny.Lemmas

/-!
# The language, for the bool module

Kanon's library proves the rules of the bool module once (`Kanon.BoolMod`), for
any language that gives the terms of its nodes, its booleans and its primitives,
with their laws: here `boolLang`. The only law that is more than the typing and
evaluation of the nodes is that of `sure_neq`, which the integer module extends
with the integer literals.
-/

namespace Tiny.Lib

open Classical Kanon BoolMod

variable {ρ : Env}

/-! ## `sure_neq` -/

theorem getD_firstSome_orElse {α} {o : Option α} {l : List (Option α)} {d : α} :
    (firstSome (o :: l)).getD d = match o with | some x => x | none => (firstSome l).getD d := by
  cases o <;> simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

theorem sure_neq_cases {a b : Term} (h : sure_neq a b = true) :
    a.ty ≠ b.ty ∨
    (∃ x y Ta Tb, a = .mk (.Bool x) Ta ∧ b = .mk (.Bool y) Tb ∧ x ≠ y) ∨
    (∃ x y Ta Tb, a = .mk (.Int x) Ta ∧ b = .mk (.Int y) Tb ∧ x ≠ y) := by
  unfold sure_neq at h
  simp only [getD_firstSome_orElse, Bool.or_eq_true, Bool.not_eq_true', ty_eq] at h
  rcases h with h | h
  · left; exact of_decide_eq_false h
  right
  rcases a with ⟨ka, Ta⟩; rcases b with ⟨kb, Tb⟩
  cases ka <;> cases kb <;> simp [firstSome] at h ⊢ <;> exact h

theorem sure_neq_sound {a b : Term} {u : Val} (h : sure_neq a b = true) (ht : a.ty = b.ty)
    (ea : ev ρ a = some u) (eb : ev ρ b = some u) : False := by
  rcases sure_neq_cases h with h | ⟨x, y, Ta, Tb, rfl, rfl, hne⟩ | ⟨x, y, Ta, Tb, rfl, rfl, hne⟩
  · exact h ht
  · simp only [ev, Option.some.injEq] at ea eb; rw [← eb] at ea; simp at ea; exact hne ea
  · simp only [ev, Option.some.injEq] at ea eb; rw [← eb] at ea; simp at ea; exact hne ea

theorem evList_eq : ∀ l, evList ρ l = l.mapM (ev ρ)
  | [] => rfl
  | t :: ts => by
    rw [evList, List.mapM_cons, evList_eq ts]
    cases ev ρ t <;> cases ts.mapM (ev ρ) <;> rfl

end Tiny.Lib

namespace Tiny

open Classical Kanon BoolMod Lib

/-- The language, for the bool module. -/
noncomputable def boolLang : BoolMod.Lang sem where
  Kind := Kind
  mk := Term.mk
  tbool := .TBool
  litK := .Bool
  notK a := .Unop .Not a
  andK a b := .Binop .And a b
  orK a b := .Binop .Or a b
  eqK a b := .Binop .Eq a b
  iteK := .Ite
  distinctK l := .Nop .Distinct l
  vbool := .bool
  equal := equal
  sure_neq := sure_neq
  ty_mk _ _ := rfl
  WT_lit _ _ := by simp
  WT_not _ _ := by simp [Term.WT, Unop.WT, and_assoc]
  WT_and _ _ _ := by simp [Term.WT, Binop.WT, and_assoc]
  WT_or _ _ _ := by simp [Term.WT, Binop.WT, and_assoc]
  WT_eq _ _ _ := by simp [Term.WT, Binop.WT, and_assoc]
  WT_ite _ _ _ _ := by simp [Term.WT]
  WT_distinct _ _ := by simp [Term.WT, WTList_iff]
  ev_lit _ _ _ := rfl
  ev_not _ _ _ := by simp [ev, evUnop]
  ev_and _ _ _ _ := by simp [ev, evBinop]
  ev_or _ _ _ _ := by simp [ev, evBinop]
  ev_eq _ _ _ _ := by simp [ev, evBinop]
  ev_ite _ _ _ _ _ := by simp [ev]
  ev_distinct _ _ _ := by simp [ev, evList_eq]
  ev_bool _ _ v w ht e := by
    have := ev_ty w e
    rcases v with b | z
    · exact ⟨b, rfl⟩
    · simp_all [Val.ty]
  vbool_inj _ _ h := Val.bool.inj h
  equal_eq _ _ h := by simpa [equal] using h
  sure_neq_sound _ _ _ _ h ht _ _ ea eb := sure_neq_sound h ht ea eb

end Tiny
