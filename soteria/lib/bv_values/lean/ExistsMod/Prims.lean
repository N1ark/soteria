import ExistsMod.Lang

/-!
# What the rules of the exists module need of a language

The primitive `used_binders` reads the terms of a language (the variables that
occur free in them), so each language gives it, with what the rules need of it:
it keeps some of the binders, and dropping the others does not change the value
of a quantifier that is not poison. They are the class `Laws` (`[@@@lean_laws]` in `exists.knl`),
which the proofs of the module assume and each language proves.
-/

namespace ExistsMod

open Kanon

/-- A well-typed `Exists`: a boolean, with distinct binders, and a well-typed
boolean body. -/
theorem WT_exists {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [Lang S]
    {bs : List (Int × S.Ty)} {body : S.Term} {t : S.Ty} (w : S.WT (mk (.Exists bs body) t)) :
    t = KanonBool.sort .TBool ∧ (bs.map Prod.fst).Nodup ∧
      S.ty body = KanonBool.sort .TBool ∧ S.WT body := by
  rw [WT_mk] at w
  simp only [Node.wt, exists_wf, Node.All] at w
  exact ⟨w.1.1, w.1.2.1, w.1.2.2, w.2⟩

/-- What the exists module needs a language to give and prove. -/
class Laws (S : Kanon.Sem) [KanonBool.Lang S] [CoreMod.Lang S] [Lang S] where
  /-- The binders among `bs` that occur free in `body`. -/
  used_binders : List (Int × S.Ty) → S.Term → List (Int × S.Ty)
  used_sublist : ∀ bs body, (used_binders bs body).Sublist bs
  /-- The binders that `used_binders` drops do not change an `Exists` that is
  not poison. -/
  ev_used : ∀ ρ bs body t v, S.WT (mk (.Exists bs body) t) →
    S.ev ρ (mk (.Exists bs body) t) = some v →
      S.ev ρ (mk (.Exists (used_binders bs body) body) t) = some v

variable {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [Lang S] [Laws S]

/-- The primitive `used_binders`, the language's. -/
def used_binders (bs : List (Int × S.Ty)) (body : S.Term) : List (Int × S.Ty) :=
  Laws.used_binders bs body

end ExistsMod
