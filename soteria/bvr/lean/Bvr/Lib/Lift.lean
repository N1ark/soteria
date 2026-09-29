import Bvr.Lib.Meta

/-!
# Lifting the calls to rule functions to their specs

The body of a rule calls rule functions through `O`, which only refine their
specs. `bvr_lift` proves `Refines FS S body`, where `S` is `body` with every
call `O.f args` replaced by `f.spec args` (it is found by unification), so
that the rest of a proof is about raw terms only.
-/

namespace Bvr.Lib

open Classical

variable {FS : FloatSem} {O : Ops}

theorem ty_refines {a a' : Term} (ha : Refines FS a a') (w : a.WT) : a'.ty = a.ty := by
  simpa using (ha.syn w).2

/-! ## Congruence, with the well-typedness of the node in context -/

theorem Refines.of_WT {s r : Term} (h : s.WT → Refines FS s r) : Refines FS s r := by
  by_cases w : s.WT
  · exact h w
  · exact ⟨fun h => absurd h w, fun ρ v e => absurd (eval_WT e) w⟩

theorem Refines.exists_ {bs body body' t} (h : Refines FS body body') :
    Refines FS (.mk (.exists_ bs body) t) (.mk (.exists_ bs body') t) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · simp only [Term.WT] at w ⊢
    obtain ⟨ht, hn, hwf, hb, wb⟩ := w
    have ⟨wb', sb⟩ := h.1 wb
    refine ⟨⟨ht, hn, hwf, ?_, wb'⟩, rfl⟩
    rw [Ty.sort_eq, Ty.sort_eq] at sb; rw [sb, hb]
  · have wb := (by simp only [Term.WT] at w; exact w.2.2.2.2 : body.WT)
    have wb' := (by simp only [Term.WT] at w'; exact w'.2.2.2.2 : body'.WT)
    have hev : ∀ ρ', (∃ b, ev FS ρ' body = some (.bool b)) → ev FS ρ' body' = ev FS ρ' body := by
      intro ρ' ⟨b, hb⟩
      have := h.2 ρ' _ (by rw [eval_eq_ev wb]; exact hb)
      rw [eval_eq_ev wb'] at this; rw [this, hb]
    rw [eval_eq_ev w] at e; rw [eval_eq_ev w']
    simp only [ev] at e ⊢
    split at e
    · rename_i hall
      have hall' : ∀ ρ', ρ'.Extends ρ bs → ∃ b, ev FS ρ' body' = some (.bool b) := fun ρ' hx => by
        rw [hev ρ' (hall ρ' hx)]; exact hall ρ' hx
      rw [if_pos hall']
      rw [← e]; congr 3
      apply propext; constructor
      · rintro ⟨ρ', hx, hb⟩; exact ⟨ρ', hx, by rw [← hev ρ' (hall ρ' hx)]; exact hb⟩
      · rintro ⟨ρ', hx, hb⟩; exact ⟨ρ', hx, by rw [hev ρ' (hall ρ' hx)]; exact hb⟩
    · simp at e

open Lean Meta Elab Tactic in
/-- Adds `x'.ty = x.ty` for every `Refines FS x x'` of the context whose `x` is
known to be well-typed. -/
def tyRefines (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  let lctx ← getLCtx
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars d.type)
    unless ty.isAppOfArity ``Bvr.Refines 3 do continue
    let x := ty.getArg! 1
    let wt ← mkAppM ``Bvr.Term.WT #[x]
    let some hw := lctx.findDecl? fun d' =>
      if d'.isImplementationDetail then none else some d' |>.filter fun d' => d'.type == wt
      | continue
    let pf ← mkAppM ``ty_refines #[d.toExpr, hw.toExpr]
    let (_, g') ← (← g.assert `hty (← inferType pf) pf).intro1P
    g := g'
  return g

open Lean Meta Elab Tactic in
elab "bvr_ty_refines" : tactic => liftMetaTactic fun g => return [← tyRefines g]

/-- Proves `Refines FS s s'`, where `s'` is `s` with some of its subterms
replaced by terms that refine them (hypotheses of the context). -/
syntax "bvr_congr" : tactic
macro_rules
  | `(tactic| bvr_congr) => `(tactic| first
      | exact Refines.refl
      | assumption
      | (apply Refines.of_WT
         intro w
         (try simp only [WT_unop, WT_binop, WT_triop] at w)
         (try bvr_split)
         bvr_ty_refines
         (try simp only [ty, size, Term.ty_mk, *] at ⊢)
         all_goals first
           | exact Refines.refl
           | ((first
               | apply Refines.unop
               | apply Refines.binop
               | apply Refines.ite
               | apply Refines.fma
               | apply Refines.exists_) <;>
              first
                | (intro; rfl)
                | bvr_congr)))

/-- `Refines.trans`, with the lifting first so that it determines the middle
term. -/
theorem Refines.of_lift {s m r : Term} (hl : Refines FS m r) (hm : Refines FS s m) :
    Refines FS s r :=
  Refines.trans hm hl

end Bvr.Lib
