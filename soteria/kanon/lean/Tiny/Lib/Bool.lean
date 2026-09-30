import Tiny.Lib.Tactic

/-!
# Lemmas for the rules of the bool module

`sure_neq` (surely different values), and `distinct`.
-/

namespace Tiny.Lib

open Classical Kanon

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

theorem eqOp_true {a b : Option Val} (h : eqOp a b = some (.bool true)) :
    ∃ u, a = some u ∧ b = some u := by
  unfold eqOp at h
  split at h
  · simp only [Option.some.injEq, Val.bool.injEq, decide_eq_true_eq] at h
    subst h; exact ⟨_, rfl, rfl⟩
  · simp at h

theorem pand_eqOp_true {a b c d : Option Val} (h : pand (eqOp a b) (eqOp c d) = some (.bool true)) :
    ∃ u w, a = some u ∧ b = some u ∧ c = some w ∧ d = some w := by
  rw [pand_eq_some] at h
  rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨h1, h2, -⟩
  · cases h
  · cases h
  · obtain ⟨u, rfl, rfl⟩ := eqOp_true h1
    obtain ⟨w, rfl, rfl⟩ := eqOp_true h2
    exact ⟨u, w, rfl, rfl, rfl, rfl⟩

/-- `a == x && a == y` (with the equalities in either order) refines `false`,
for `x` and `y` surely different. -/
theorem Refines.and_eq_neq {p1 q1 p2 q2 x y a T1 T2 T}
    (o1 : (p1 = a ∧ q1 = x) ∨ (p1 = x ∧ q1 = a)) (o2 : (p2 = a ∧ q2 = y) ∨ (p2 = y ∧ q2 = a))
    (hn : sure_neq x y = true) :
    Refines (.mk (.Binop .And (.mk (.Binop .Eq p1 q1) T1) (.mk (.Binop .Eq p2 q2) T2)) T)
      v_false := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · have := (WT_binop.1 w).1; simp [Binop.WT] at this; simp [this]
  obtain ⟨-, w1, w2⟩ := WT_binop.1 w
  obtain ⟨h1, -, -⟩ := WT_binop.1 w1
  obtain ⟨h2, -, -⟩ := WT_binop.1 w2
  simp only [Binop.WT] at h1 h2
  simp only [ev, evBinop] at e
  simp only [v_false, ev]
  have hv := evBinop_ty (op := .And) e
  rcases v with ⟨_ | _⟩ | _ <;> simp [Val.ty, Binop.resTy] at hv ⊢
  have hx : x.ty = a.ty := by
    rcases o1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> first | exact h1.1 | exact h1.1.symm
  have hy : y.ty = a.ty := by
    rcases o2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> first | exact h2.1 | exact h2.1.symm
  obtain ⟨u, u', e1, e2, e3, e4⟩ := pand_eqOp_true e
  have ea1 : ev ρ a = some u ∧ ev ρ x = some u := by
    rcases o1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> first | exact ⟨e1, e2⟩ | exact ⟨e2, e1⟩
  have ea2 : ev ρ a = some u' ∧ ev ρ y = some u' := by
    rcases o2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> first | exact ⟨e3, e4⟩ | exact ⟨e4, e3⟩
  have : u = u' := by rw [ea1.1] at ea2; simpa using ea2.1
  subst this
  exact sure_neq_sound hn (hx.trans hy.symm) ea1.2 ea2.2

/-- Proves `a == x && a == y` (with the equalities in either order) refines
`false`, for `x` and `y` surely different. -/
macro "kanon_and_eq_neq" : tactic => `(tactic| (
  intro O hO
  intros
  kanon_guards
  (try kanon_split)
  (try subst_vars)
  simp only [kanon_spec] at *
  first
    | exact Refines.and_eq_neq (.inl ⟨rfl, rfl⟩) (.inl ⟨rfl, rfl⟩) ‹_›
    | exact Refines.and_eq_neq (.inl ⟨rfl, rfl⟩) (.inr ⟨rfl, rfl⟩) ‹_›
    | exact Refines.and_eq_neq (.inr ⟨rfl, rfl⟩) (.inl ⟨rfl, rfl⟩) ‹_›
    | exact Refines.and_eq_neq (.inr ⟨rfl, rfl⟩) (.inr ⟨rfl, rfl⟩) ‹_›))

/-! ## `distinct` -/

theorem equal_iff {a b : Term} : equal a b = true ↔ a = b := by simp [equal]

/-- The value of a term that evaluates (a default otherwise). -/
noncomputable def evD (ρ : Env) (t : Term) : Val := (ev ρ t).getD (.bool false)

theorem evList_eq_some : ∀ {l : List Term} {vs : List Val},
    evList ρ l = some vs ↔ (∀ t ∈ l, ∃ v, ev ρ t = some v) ∧ vs = l.map (evD ρ)
  | [], vs => by simp [evList]
  | t :: ts, vs => by
    simp only [evList]
    constructor
    · intro h
      split at h
      · rename_i v vs' hv hvs
        cases h
        obtain ⟨h1, h2⟩ := evList_eq_some.1 hvs
        refine ⟨?_, ?_⟩
        · intro t' ht'
          rcases List.mem_cons.1 ht' with rfl | ht'
          · exact ⟨v, hv⟩
          · exact h1 t' ht'
        · simp [h2, evD, hv]
      · cases h
    · rintro ⟨h1, rfl⟩
      obtain ⟨v, hv⟩ := h1 t (by simp)
      have := evList_eq_some (l := ts) (vs := ts.map (evD ρ)) |>.2
        ⟨fun t' ht' => h1 t' (by simp [ht']), rfl⟩
      rw [hv, this]; simp [evD, hv]

theorem distinct_check_one_true {a : Term} : ∀ {rest : List Term},
    distinct_check_one a rest = some true → ∀ b ∈ rest, sure_neq a b = true
  | [], _ => by simp
  | b :: rest, h => by
    rw [distinct_check_one] at h
    simp only [firstSome, Option.getD_some, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at h
    split at h
    · simp at h
    · split at h
      · rename_i hs
        intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact hs
        · exact distinct_check_one_true h c hc
      · simp at h

theorem distinct_check_one_false {a : Term} : ∀ {rest : List Term},
    distinct_check_one a rest = some false → a ∈ rest
  | [], h => by
    rw [distinct_check_one] at h
    simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at h
  | b :: rest, h => by
    rw [distinct_check_one] at h
    simp only [firstSome, Option.getD_some, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at h
    split at h
    · rename_i he; simp [equal_iff] at he; simp [he]
    · split at h
      · exact List.mem_cons_of_mem _ (distinct_check_one_false h)
      · simp at h

theorem distinct_check_true : ∀ {l : List Term},
    distinct_check l = some true → l.Pairwise (fun a b => sure_neq a b = true)
  | [], _ => by simp
  | a :: rest, h => by
    rw [distinct_check] at h
    simp only [firstSome, Option.getD_some, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at h
    cases h1 : distinct_check_one a rest with
    | none => simp [h1] at h
    | some b =>
      cases b
      · simp [h1] at h
      · simp only [h1] at h
        exact List.Pairwise.cons (distinct_check_one_true h1) (distinct_check_true h)

theorem distinct_check_false : ∀ {l : List Term}, distinct_check l = some false → ¬ l.Nodup
  | [], h => by
    rw [distinct_check] at h
    simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at h
  | a :: rest, h => by
    rw [distinct_check] at h
    simp only [firstSome, Option.getD_some, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at h
    cases h1 : distinct_check_one a rest with
    | none => simp [h1] at h
    | some b =>
      cases b
      · have := distinct_check_one_false h1
        simp [this]
      · simp only [h1] at h
        have := distinct_check_false h
        simp [this]

theorem ev_distinct_eq_some {l v} (w : (b_distinct.spec l).WT)
    (e : ev ρ (b_distinct.spec l) = some v) :
    (∃ E, ∀ t ∈ l, t.ty = E ∧ t.WT) ∧ (∀ t ∈ l, ∃ v, ev ρ t = some v) ∧
      v = .bool (decide (l.map (evD ρ)).Nodup) := by
  simp only [b_distinct.spec, Term.WT] at w
  obtain ⟨-, E, wl⟩ := w
  simp only [b_distinct.spec, ev] at e
  cases hv : evList ρ l with
  | none => simp [hv] at e
  | some vs =>
    obtain ⟨hall, rfl⟩ := evList_eq_some.1 hv
    simp [hv] at e
    exact ⟨⟨E, WTList_iff.1 wl⟩, hall, e.symm⟩

end Tiny.Lib
