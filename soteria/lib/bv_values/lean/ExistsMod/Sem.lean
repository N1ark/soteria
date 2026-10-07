import ExistsMod.Node
import CoreMod.Sem
import KanonBool.Sem

/-!
# The meaning of the nodes of the exists module

`Exists bs body` is true when some environment that gives the binders `bs`
values of their sorts (`Values.Extends`) makes `body` true: its meaning
evaluates its body in other environments than its own. It is poison unless the
body is a boolean in all of them, and unless the sorts of the binders have
values (SMT sorts always do: dropping a binder of a sort without values would
change the quantifier). Its invariant `exists_wf`, part of its typing, is that
its binders are distinct and its body a boolean.
-/

noncomputable section

namespace ExistsMod

open Classical Kanon
open Kanon.Sem (OLe FLe)

/-- What the exists module needs of a language: the environments that give the
binders values of their sorts, and agree with `ρ` elsewhere. -/
class Values (D : Kanon.Dom) where
  Extends : D.Env → D.Env → List (Int × D.Ty) → Prop
  extends_nil : ∀ ρ' ρ, Extends ρ' ρ [] ↔ ρ' = ρ

/-- The invariant of `Exists`: its binders are distinct, its body a boolean. -/
@[kanon_wt] def exists_wf {T Ty : Type} (sBool : KanonBool.Srt → Ty) (sCore : CoreMod.Srt Ty → Ty)
    (ty : T → Ty) : Node Ty T → Ty → Prop
  | .Exists bs body, _ => (bs.map Prod.fst).Nodup ∧ ty body = sBool .TBool

section
variable {D : Kanon.Dom} [KanonBool.Values D] [CoreMod.Values D] [Values D]

/-- `Exists bs body`, given the values of `body` in every environment. -/
def existsV (ρ : D.Env) (bs : List (Int × D.Ty)) (body : D.Env → Option D.Val) :
    Option D.Val :=
  if (∀ b ∈ bs, ∃ v, CoreMod.Values.Of v b.2) ∧
      ∀ ρ', Values.Extends ρ' ρ bs → ∃ b, body ρ' = some (KanonBool.Values.vbool.inj b) then
    some (KanonBool.Values.vbool.inj
      (decide (∃ ρ', Values.Extends ρ' ρ bs ∧
        body ρ' = some (KanonBool.Values.vbool.inj true))))
  else none

/-- Two quantifiers have the same value when their environments correspond, with
the same values of their bodies, and the sorts of their binders have values
alike. -/
theorem existsV_congr {ρ ρ' : D.Env} {bs bs' : List (Int × D.Ty)} {a a' : D.Env → Option D.Val}
    (hs : (∀ b ∈ bs, ∃ v, CoreMod.Values.Of v b.2) ↔ (∀ b ∈ bs', ∃ v, CoreMod.Values.Of v b.2))
    (h1 : ∀ ρ1, Values.Extends ρ1 ρ bs → ∃ ρ2, Values.Extends ρ2 ρ' bs' ∧ a ρ1 = a' ρ2)
    (h2 : ∀ ρ2, Values.Extends ρ2 ρ' bs' → ∃ ρ1, Values.Extends ρ1 ρ bs ∧ a ρ1 = a' ρ2) :
    existsV ρ bs a = existsV ρ' bs' a' := by
  have hc : (∀ ρ1, Values.Extends ρ1 ρ bs → ∃ b, a ρ1 = some (KanonBool.Values.vbool.inj b)) ↔
      (∀ ρ2, Values.Extends ρ2 ρ' bs' → ∃ b, a' ρ2 = some (KanonBool.Values.vbool.inj b)) := by
    constructor
    · intro h ρ2 e2; obtain ⟨ρ1, e1, eq⟩ := h2 ρ2 e2; rw [← eq]; exact h ρ1 e1
    · intro h ρ1 e1; obtain ⟨ρ2, e2, eq⟩ := h1 ρ1 e1; rw [eq]; exact h ρ2 e2
  have he : (∃ ρ1, Values.Extends ρ1 ρ bs ∧ a ρ1 = some (KanonBool.Values.vbool.inj true)) ↔
      (∃ ρ2, Values.Extends ρ2 ρ' bs' ∧ a' ρ2 = some (KanonBool.Values.vbool.inj true)) := by
    constructor
    · rintro ⟨ρ1, e1, h⟩; obtain ⟨ρ2, e2, eq⟩ := h1 ρ1 e1; exact ⟨ρ2, e2, eq ▸ h⟩
    · rintro ⟨ρ2, e2, h⟩; obtain ⟨ρ1, e1, eq⟩ := h2 ρ2 e2; exact ⟨ρ1, e1, eq ▸ h⟩
  unfold existsV
  simp only [hs, hc, he]

theorem existsV_mono {ρ : D.Env} {bs : List (Int × D.Ty)} {a a' : D.Env → Option D.Val}
    (h : FLe a a') : OLe (existsV ρ bs a) (existsV ρ bs a') := by
  intro v e
  unfold existsV at e ⊢
  split at e
  · rename_i hb
    have hb' : ∀ ρ', Values.Extends ρ' ρ bs →
        ∃ b, a' ρ' = some (KanonBool.Values.vbool.inj b) := fun ρ' he => by
      obtain ⟨b, hb⟩ := hb.2 ρ' he; exact ⟨b, h ρ' _ hb⟩
    rw [if_pos ⟨hb.1, hb'⟩]
    cases e
    congr 3
    apply propext
    constructor
    · rintro ⟨ρ', he, h'⟩
      refine ⟨ρ', he, ?_⟩
      obtain ⟨b, hb⟩ := hb.2 ρ' he
      rw [h ρ' _ hb] at h'; rw [hb, h']
    · rintro ⟨ρ', he, h'⟩; exact ⟨ρ', he, h ρ' _ h'⟩
  · cases e

/-- A quantifier without binders, when it is not poison, is the value of its
body. -/
theorem existsV_nil {ρ : D.Env} {a : D.Env → Option D.Val} {v : D.Val}
    (h : existsV ρ [] a = some v) :
    ∃ b, a ρ = some (KanonBool.Values.vbool.inj b) ∧ v = KanonBool.Values.vbool.inj b := by
  unfold existsV at h
  split at h
  · rename_i hb
    obtain ⟨b, hb⟩ := hb.2 ρ ((Values.extends_nil ρ ρ).2 rfl)
    cases h
    refine ⟨b, hb, ?_⟩
    cases b <;> simp [Values.extends_nil, hb]
  · cases h
end

/-- The evaluation of a node in the environment `ρ`, given the values of its
children in every environment. -/
def Node.eval {D : Kanon.Dom} [KanonBool.Values D] [CoreMod.Values D] [Values D] (ρ : D.Env)
    (t : D.Ty) : Node D.Ty (D.Env → Option D.Val) → Option D.Val
  | .Exists bs body => existsV ρ bs body

theorem Node.eval_mono {D : Kanon.Dom} [KanonBool.Values D] [CoreMod.Values D] [Values D]
    (ρ : D.Env) (t : D.Ty) {n n' : Node D.Ty (D.Env → Option D.Val)} (h : n.Rel FLe n') :
    OLe (n.eval ρ t) (n'.eval ρ t) := by
  cases n; cases n'; simp only [Node.Rel] at h
  obtain ⟨rfl, h⟩ := h
  exact existsV_mono h

end ExistsMod
