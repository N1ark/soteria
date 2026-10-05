import KanonBool.Sem
import CoreMod.Sem
import ExistsMod.Syntax

/-!
# What the exists module needs of the semantics of a language

`Exists (bs, body)` is true when some values of the binders `bs`, of their
sorts, make `body` true: its evaluation quantifies over the environments that
extend the current one with the binders (`Extends`), and is poison unless
`body` is a boolean in all of them. Its invariant `exists_wf` (part of the
typing of its terms) is that the binders are distinct, their sorts have values
(`TyWF`), and the body is a boolean. The only law that is about the terms of
the language is that the binders that do not occur in the body do not matter
(`ev_used_binders`), for the primitive `used_binders`.
-/

namespace ExistsMod

open Classical Kanon

/-- What the exists module needs of the semantics `S` of a language, for its
interface `L`. -/
class Sem {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
    {LBool : KanonBool.Syntax B} {LCore : CoreMod.Syntax B} (L : Syntax B LBool LCore)
    [KanonBool.Sem LBool] [CoreMod.Sem LCore] where
  /-- The sorts that have values. -/
  TyWF : S.Ty → Prop
  /-- The environments `ρ'` that differ from `ρ` only on the variables bound by
  `bs`, to which they give values of their sorts. -/
  Extends : S.Env → S.Env → List (Int × S.Ty) → Prop
  extends_nil : ∀ ρ' ρ, Extends ρ' ρ [] ↔ ρ' = ρ
  exists_wf_Exists : ∀ bs body t, L.exists_wf (B.node (L.ExistsK bs body) t) ↔
    (bs.map Prod.fst).Nodup ∧ (∀ b ∈ bs, TyWF b.2) ∧ S.ty body = LBool.TBool
  ev_Exists : ∀ ρ bs body t, S.ev ρ (B.node (L.ExistsK bs body) t) =
    if ∀ ρ', Extends ρ' ρ bs → ∃ b, S.ev ρ' body = some (KanonBool.Sem.vbool LBool b) then
      some (KanonBool.Sem.vbool LBool
        (decide (∃ ρ', Extends ρ' ρ bs ∧
          S.ev ρ' body = some (KanonBool.Sem.vbool LBool true))))
    else none
  /-- `used_binders` keeps some of the binders, in order. -/
  used_binders_sublist : ∀ bs body, (L.exists_used_binders bs body).Sublist bs
  /-- The binders that `used_binders` drops do not matter. -/
  ev_used_binders : ∀ ρ bs body t t', (bs.map Prod.fst).Nodup → (∀ b ∈ bs, TyWF b.2) →
    S.ev ρ (B.node (L.ExistsK bs body) t) =
      S.ev ρ (B.node (L.ExistsK (L.exists_used_binders bs body) body) t')

end ExistsMod
