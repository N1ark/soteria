import KanonCore.Proof
import KanonCore.Generic

/-!
# Congruence of the nodes that are strict in their operands

A node whose typing is a condition on the sorts of its operands (and its own),
with its operands well-typed, and whose value is a function of the values of
its operands that is poison when one of them is (`F none = none`), is monotone
in its operands: refining them refines it (`refines_node1`, …). The modules
that use the bitvec module prove the congruence of their nodes with them.
-/

namespace BitvecMod.Lib

open Kanon Kanon.Sem

variable {S : Kanon.Sem}

theorem strict1 {F : Option S.Val → Option S.Val} (h0 : F none = none) {a a' : Option S.Val}
    (ha : OLe a a') : OLe (F a) (F a') := by
  intro v e
  rcases a with _ | x
  · rw [h0] at e; cases e
  · rw [ha x rfl]; exact e

theorem strict2 {F : Option S.Val → Option S.Val → Option S.Val}
    (h0 : ∀ b, F none b = none) (h1 : ∀ a, F a none = none) {a a' b b' : Option S.Val}
    (ha : OLe a a') (hb : OLe b b') : OLe (F a b) (F a' b') := by
  intro v e
  rcases a with _ | x
  · rw [h0] at e; cases e
  rcases b with _ | y
  · rw [h1] at e; cases e
  rw [ha x rfl, hb y rfl]; exact e

theorem strict3 {F : Option S.Val → Option S.Val → Option S.Val → Option S.Val}
    (h0 : ∀ b c, F none b c = none) (h1 : ∀ a c, F a none c = none)
    (h2 : ∀ a b, F a b none = none) {a a' b b' c c' : Option S.Val}
    (ha : OLe a a') (hb : OLe b b') (hc : OLe c c') : OLe (F a b c) (F a' b' c') := by
  intro v e
  rcases a with _ | x
  · rw [h0] at e; cases e
  rcases b with _ | y
  · rw [h1] at e; cases e
  rcases c with _ | z
  · rw [h2] at e; cases e
  rw [ha x rfl, hb y rfl, hc z rfl]; exact e

variable {B : Kanon.Base S}

theorem refines_node1 {K : S.Term → B.Kind} {Q : S.Term → S.Ty → Prop}
    (hWT : ∀ a t, S.WT (B.node (K a) t) ↔ Q a t ∧ S.WT a)
    (hQ : ∀ a a' t, S.ty a' = S.ty a → Q a t → Q a' t)
    {F : Option S.Val → Option S.Val} (h0 : F none = none)
    (hev : ∀ ρ a t, S.ev ρ (B.node (K a) t) = F (S.ev ρ a))
    {a a' : S.Term} {t t' : S.Ty} (ha : S.Refines a a')
    (ht : S.WT (B.node (K a) t) → t' = t) :
    S.Refines (B.node (K a) t) (B.node (K a') t') := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · have e' := ht w; subst e'
    rw [hWT] at w
    obtain ⟨wa', sa⟩ := ha.syn w.2
    exact ⟨(hWT _ _).2 ⟨hQ _ _ _ sa w.1, wa'⟩, by rw [B.ty_node, B.ty_node]⟩
  · rw [hWT] at w
    rw [hev] at e ⊢
    exact strict1 h0 (ha.ev w.2 ρ) v e

theorem refines_node2 {K : S.Term → S.Term → B.Kind} {Q : S.Term → S.Term → S.Ty → Prop}
    (hWT : ∀ a b t, S.WT (B.node (K a b) t) ↔ Q a b t ∧ S.WT a ∧ S.WT b)
    (hQ : ∀ a a' b b' t, S.ty a' = S.ty a → S.ty b' = S.ty b → Q a b t → Q a' b' t)
    {F : Option S.Val → Option S.Val → Option S.Val} (h0 : ∀ b, F none b = none)
    (h1 : ∀ a, F a none = none)
    (hev : ∀ ρ a b t, S.ev ρ (B.node (K a b) t) = F (S.ev ρ a) (S.ev ρ b))
    {a a' b b' : S.Term} {t t' : S.Ty} (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (K a b) t) → t' = t) :
    S.Refines (B.node (K a b) t) (B.node (K a' b') t') := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · have e' := ht w; subst e'
    rw [hWT] at w
    obtain ⟨wa', sa⟩ := ha.syn w.2.1
    obtain ⟨wb', sb⟩ := hb.syn w.2.2
    exact ⟨(hWT _ _ _).2 ⟨hQ _ _ _ _ _ sa sb w.1, wa', wb'⟩, by rw [B.ty_node, B.ty_node]⟩
  · rw [hWT] at w
    rw [hev] at e ⊢
    exact strict2 h0 h1 (ha.ev w.2.1 ρ) (hb.ev w.2.2 ρ) v e

theorem refines_node3 {K : S.Term → S.Term → S.Term → B.Kind}
    {Q : S.Term → S.Term → S.Term → S.Ty → Prop}
    (hWT : ∀ a b c t, S.WT (B.node (K a b c) t) ↔ Q a b c t ∧ S.WT a ∧ S.WT b ∧ S.WT c)
    (hQ : ∀ a a' b b' c c' t, S.ty a' = S.ty a → S.ty b' = S.ty b → S.ty c' = S.ty c →
      Q a b c t → Q a' b' c' t)
    {F : Option S.Val → Option S.Val → Option S.Val → Option S.Val}
    (h0 : ∀ b c, F none b c = none) (h1 : ∀ a c, F a none c = none)
    (h2 : ∀ a b, F a b none = none)
    (hev : ∀ ρ a b c t, S.ev ρ (B.node (K a b c) t) = F (S.ev ρ a) (S.ev ρ b) (S.ev ρ c))
    {a a' b b' c c' : S.Term} {t t' : S.Ty} (ha : S.Refines a a') (hb : S.Refines b b')
    (hc : S.Refines c c') (ht : S.WT (B.node (K a b c) t) → t' = t) :
    S.Refines (B.node (K a b c) t) (B.node (K a' b' c') t') := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · have e' := ht w; subst e'
    rw [hWT] at w
    obtain ⟨wa', sa⟩ := ha.syn w.2.1
    obtain ⟨wb', sb⟩ := hb.syn w.2.2.1
    obtain ⟨wc', sc⟩ := hc.syn w.2.2.2
    exact ⟨(hWT _ _ _ _).2 ⟨hQ _ _ _ _ _ _ _ sa sb sc w.1, wa', wb', wc'⟩,
      by rw [B.ty_node, B.ty_node]⟩
  · rw [hWT] at w
    rw [hev] at e ⊢
    exact strict3 h0 h1 h2 (ha.ev w.2.1 ρ) (hb.ev w.2.2.1 ρ) (hc.ev w.2.2.2 ρ) v e

end BitvecMod.Lib
