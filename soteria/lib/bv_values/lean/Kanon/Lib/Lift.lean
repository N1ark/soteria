import Kanon.Lib.Meta

/-!
# Congruence

`kanon_congr` (Kanon's) proves `Refines FS s s'`, where `s'` is `s` with some
of its subterms replaced by terms that refine them (hypotheses of the context),
with the congruence lemmas of the nodes (`kanon_congr_lemma`): the generated
`Lifts.lean` proves with it that the specs are monotone in their term
arguments. The types of the nodes are given by their operands, whose types the
refinements preserve once they are well-typed (`kanon_ty_refines`).
-/

namespace Kanon.Lib

open Classical

variable {FS : FloatSem}

@[kanon_congr_lemma] theorem Refines.exists_ {bs body body' t} (h : Refines FS body body') :
    Refines FS (.mk (.Exists bs body) t) (.mk (.Exists bs body') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · dsimp only at w ⊢
    simp only [Term.WT] at w ⊢
    obtain ⟨ht, hn, hwf, hb, wb⟩ := w
    obtain ⟨wb', sb⟩ : body'.WT ∧ body'.ty = body.ty := h.syn wb
    refine ⟨⟨ht, hn, hwf, ?_, wb'⟩, rfl⟩
    rw [sb, hb]
  · have wb := (by dsimp only at w; simp only [Term.WT] at w; exact w.2.2.2.2 : body.WT)
    have hev : ∀ ρ', (∃ b, ev FS ρ' body = some (.bool b)) → ev FS ρ' body' = ev FS ρ' body :=
      fun ρ' ⟨_, hb⟩ => (h.ev wb ρ' _ hb).trans hb.symm
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
    unless ty.isAppOfArity ``Kanon.Sem.Refines 3 do continue
    let x := ty.getArg! 1
    let wt ← mkAppM ``Kanon.Term.WT #[x]
    let some hw := lctx.findDecl? fun d' =>
      if d'.isImplementationDetail then none else some d' |>.filter fun d' => d'.type == wt
      | continue
    let pf ← mkAppM ``Kanon.Sem.ty_refines #[d.toExpr, hw.toExpr]
    let tyOf (e : Expr) := mkApp (mkConst ``Kanon.Term.ty) e
    let (_, g') ← (← g.assert `hty (← mkEq (tyOf (ty.getArg! 2)) (tyOf x)) pf).intro1P
    g := g'
  return g

open Lean Meta Elab Tactic in
elab "kanon_ty_refines" : tactic => liftMetaTactic fun g => return [← tyRefines g]

/-- `kanon_congr` first rewrites the types of the refined terms, which their
refinements preserve once they are well-typed. -/
macro_rules
  | `(tactic| kanon_congr_pre) => `(tactic| (
      apply Sem.Refines.of_WT
      intro w
      dsimp only at w
      (try simp only [WT_unop, WT_binop, WT_triop] at w)
      (try kanon_split)
      kanon_ty_refines
      (try simp only [ty, size, Term.ty_mk, *] at ⊢)))

end Kanon.Lib
