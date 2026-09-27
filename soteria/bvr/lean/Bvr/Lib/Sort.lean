import Bvr.Lemmas

/-! Evaluation preserves sorts. -/

namespace Bvr.Lib


open Classical

theorem unop_hasSort {FS op a t v v'} (w : op.WT a t) (ha : ∀ va, v' = some va → va.hasSort a)
    (h : evUnop FS op v' = some v) : v.hasSort t := by
  rcases v' with _ | va
  · simp at h
  have ha := ha va rfl
  cases op <;> rcases va with _ | _ | _ | _ | _ | _ <;> simp only [evUnop, reduceCtorEq, Option.some.injEq] at h
  all_goals (try split at h) <;> (try simp only [reduceCtorEq, Option.some.injEq] at h)
  all_goals subst h
  all_goals simp only [Unop.WT] at w
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := w; simp_all [Val.hasSort] <;> omega)
    | (obtain ⟨n, hn, rfl, rfl⟩ := w; simp_all [Val.hasSort] <;> omega)
    | (obtain ⟨hn, rfl, rfl⟩ := w; simp_all [Val.hasSort] <;> omega)
    | (obtain ⟨hn, ⟨p, rfl⟩, rfl⟩ := w; simp_all [Val.hasSort] <;> omega)
    | (obtain ⟨⟨n, hn, rfl⟩, rfl⟩ := w; simp_all [Val.hasSort] <;> omega)
    | (obtain ⟨⟨q, rfl⟩, rfl⟩ := w; simp_all [Val.hasSort] <;> omega)
    | (obtain ⟨n, rfl, h1, h2, h3, rfl⟩ := w; simp_all [Val.hasSort] <;> omega)
    | (obtain ⟨n, hn, rfl, hk, rfl⟩ := w; simp_all [Val.hasSort] <;> omega)

theorem bvBin_eq_some {f : ∀ {n : Nat}, BitVec n → BitVec n → Option Val} {a b v} :
    bvBin f a b = some v ↔
      ∃ n x y, a = some (.bv n x) ∧ b = some (.bv n y) ∧ f x y = some v := by
  constructor
  · intro h
    unfold bvBin at h; split at h
    · rename_i n x m y; split at h
      · rename_i e; subst e; exact ⟨_, x, y, rfl, rfl, h⟩
      · simp at h
    · simp at h
  · rintro ⟨n, x, y, rfl, rfl, h⟩; simpa [bvBin] using h

theorem fBin_eq_some {f : (p : Prec) → FBits p → FBits p → Option Val} {a b v} :
    fBin f a b = some v ↔
      ∃ p x y, a = some (.float p x) ∧ b = some (.float p y) ∧ f p x y = some v := by
  constructor
  · intro h
    unfold fBin at h; split at h
    · rename_i p x q y; split at h
      · rename_i e; subst e; exact ⟨_, x, y, rfl, rfl, h⟩
      · simp at h
    · simp at h
  · rintro ⟨p, x, y, rfl, rfl, h⟩; simpa [fBin] using h

theorem checkedOp_eq_some {c so uo f a b v} :
    checkedOp c so uo f a b = some v ↔
      ∃ n x y, a = some (.bv n x) ∧ b = some (.bv n y) ∧ (c.signed → so x y = false) ∧
        (c.unsigned → uo x y = false) ∧ v = .bv n (f x y) := by
  unfold checkedOp; rw [bvBin_eq_some]
  constructor
  · rintro ⟨n, x, y, rfl, rfl, h⟩
    refine ⟨n, x, y, rfl, rfl, ?_⟩
    split at h
    · simp at h
    · simp at h; grind
  · rintro ⟨n, x, y, rfl, rfl, h1, h2, rfl⟩
    refine ⟨n, x, y, rfl, rfl, ?_⟩
    rw [ite_eq_right_iff.mpr (by grind)]

theorem binop_hasSort {FS op a b t v va vb} (w : op.WT a b t)
    (ha : ∀ x, va = some x → x.hasSort a) (hb : ∀ x, vb = some x → x.hasSort b)
    (h : evBinop FS op va vb = some v) : v.hasSort t := by
  cases op
  all_goals simp only [evBinop, checkedOp, fArith] at h
  all_goals first
    | (rw [pand_eq_some] at h; simp only [Binop.WT] at w; obtain ⟨_, _, rfl⟩ := w
       rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> simp [Val.hasSort])
    | (rw [por_eq_some] at h; simp only [Binop.WT] at w; obtain ⟨_, _, rfl⟩ := w
       rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> simp [Val.hasSort])
    | (rw [fBin_eq_some] at h; obtain ⟨p, x, y, rfl, rfl, h⟩ := h
       have := ha _ rfl; simp only [Binop.WT] at w
       obtain ⟨⟨q, rfl⟩, rfl, rfl⟩ := w
       simp at h; subst h; simp_all [Val.hasSort])
    | (rw [bvBin_eq_some] at h; obtain ⟨n, x, y, rfl, rfl, h⟩ := h
       have := ha _ rfl; simp only [Binop.WT] at w
       obtain ⟨⟨m, hm, rfl⟩, rfl, rfl⟩ := w
       (try split at h) <;> simp at h <;> subst h <;> simp_all [Val.hasSort])
    | (simp only [Binop.WT] at w; obtain ⟨_, rfl⟩ := w
       rcases va with _ | x <;> rcases vb with _ | y <;> simp at h; subst h; simp [Val.hasSort])
    | (simp only [Binop.WT] at w; obtain ⟨n, m, hn, hm, rfl, rfl, rfl⟩ := w
       rcases va with _ | ⟨_ | ⟨n', x⟩ | _ | _ | _ | _⟩ <;>
         rcases vb with _ | ⟨_ | ⟨m', y⟩ | _ | _ | _ | _⟩ <;> simp at h
       subst h; have := ha _ rfl; have := hb _ rfl; simp_all [Val.hasSort]; omega)

mutual
theorem ev_hasSort {FS : FloatSem} {ρ : Env} :
    ∀ (t : Term), t.WT → ∀ v, ev FS ρ t = some v → v.hasSort t.ty
  | .mk (.var x) T, _, v, h => by
      simp only [ev] at h; split at h
      · split at h
        · simp at h; subst h; simpa [Val.hasTy] using ‹_›
        · simp at h
      · simp at h
  | .mk (.bool b) T, w, v, h => by
      simp [Term.WT] at w; simp [ev] at h; subst h w; simp [Val.hasSort]
  | .mk (.float f) T, w, v, h => by
      simp [Term.WT] at w; simp [ev] at h; subst h; rw [w.1]; simp [FloatLit.sem, Val.hasSort]
  | .mk (.bitVec z) T, w, v, h => by
      obtain ⟨n, hn, hT, _⟩ := WT_bitVec.1 w
      simp [ev] at h; subst h
      rcases hT with rfl | rfl <;> simpa [Val.hasSort, Ty.width, size_of_ty] using hn
  | .mk (.ptr l o) T, w, v, h => by
      simp only [Term.WT, Ty.sort_eq] at w
      obtain ⟨n, hn, rfl, hl, ho, wl, wo⟩ := w
      simp only [ev] at h; split at h
      · rename_i n' x m y hl' ho'
        split at h
        · simp at h; subst h
          have := ev_hasSort l wl _ hl'; rw [hl] at this
          simpa [Val.hasSort] using this
        · simp at h
      · simp at h
  | .mk (.seq l) T, w, v, h => by
      simp only [Term.WT] at w
      obtain ⟨e, rfl, wl⟩ := w
      simp only [ev, Option.map_eq_some_iff] at h
      obtain ⟨vs, hvs, rfl⟩ := h
      simpa [Val.hasSort] using evList_hasSort e l wl vs hvs
  | .mk (.unop op a) T, w, v, h => by
      simp only [ev] at h
      have w1 := (WT_unop.1 w).1; simp only [Ty.sort_eq] at w1
      exact unop_hasSort w1 (ev_hasSort a (WT_unop.1 w).2) h
  | .mk (.binop op a b) T, w, v, h => by
      simp only [ev] at h
      have ⟨w1, wa, wb⟩ := WT_binop.1 w
      simp only [Ty.sort_eq] at w1
      exact binop_hasSort w1 (ev_hasSort a wa) (ev_hasSort b wb) h
  | .mk (.triop .ite g a b) T, w, v, h => by
      have ⟨w1, wg, wa, wb⟩ := WT_triop.1 w
      simp only [Triop.WT, Ty.sort_eq] at w1
      obtain ⟨_, hb, rfl⟩ := w1
      simp only [ev] at h
      split at h
      · exact ev_hasSort a wa _ h
      · have := ev_hasSort b wb _ h; rwa [hb] at this
      · simp at h
  | .mk (.triop .fma a b c) T, w, v, h => by
      have ⟨w1, wa, wb, wc⟩ := WT_triop.1 w
      simp only [Triop.WT, Ty.sort_eq] at w1
      obtain ⟨⟨p, hp⟩, _, _, rfl⟩ := w1
      simp only [ev] at h
      unfold evFma at h
      split at h
      · rename_i p' x q y r z ha _ _
        split at h
        · simp at h; subst h
          have := ev_hasSort a wa _ ha; rw [hp] at this ⊢; simpa [Val.hasSort] using this
        · simp at h
      · simp at h
  | .mk (.nop .distinct l) T, w, v, h => by
      simp only [Term.WT] at w; obtain ⟨rfl, _⟩ := w
      simp only [ev, Option.map_eq_some_iff] at h
      obtain ⟨vs, _, rfl⟩ := h; simp [Val.hasSort]
  | .mk (.exists_ bs body) T, w, v, h => by
      simp only [Term.WT] at w; obtain ⟨rfl, _⟩ := w
      simp only [ev] at h; split at h
      · simp at h; subst h; simp [Val.hasSort]
      · simp at h
  | .mk (.extension e) T, _, v, h => by
      simp only [ev] at h; split at h
      · split at h
        · simp at h; subst h; simpa [Val.hasTy] using ‹_›
        · simp at h
      · simp at h

theorem evList_hasSort {FS : FloatSem} {ρ : Env} :
    ∀ (e : Ty) (l : List Term), Term.WTList e l → ∀ vs, evList FS ρ l = some vs →
      Val.hasSortList vs e.sort
  | e, [], _, vs, h => by simp [evList] at h; subst h; simp [Val.hasSortList]
  | e, t :: ts, w, vs, h => by
      simp only [Term.WTList] at w
      obtain ⟨ht, wt, wts⟩ := w
      simp only [evList] at h
      split at h
      · rename_i v vs' h1 h2
        simp at h; subst h
        have := ev_hasSort t wt _ h1
        simp only [Ty.sort_eq] at ht
        rw [ht] at this
        exact ⟨this, evList_hasSort e ts wts vs' h2⟩
      · simp at h
end

theorem eval_hasSort {FS ρ t v} (h : eval FS ρ t = some v) : v.hasSort t.ty := by
  have w := eval_WT h
  rw [eval_eq_ev w] at h
  exact ev_hasSort t w v h

end Bvr.Lib
