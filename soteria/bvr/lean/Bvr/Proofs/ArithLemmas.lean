import Bvr.Lemmas

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Bvr
namespace ArithL

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

/-! ## Bit-vector terms -/

/-- A well-typed bit-vector term of width [n]. -/
def BV (t : Term) (n : Int) : Prop := t.WT ∧ t.ty = .bitVector n ∧ 0 < n

/-- The binary operators typed like addition. -/
inductive IsArith : Binop → Prop
  | add c : IsArith (.add c)
  | sub c : IsArith (.sub c)
  | mul c : IsArith (.mul c)
  | div s : IsArith (.div s)
  | rem s : IsArith (.rem s)
  | mod_ : IsArith .mod_

/-- The binary operators typed like comparisons of bit-vectors. -/
inductive IsCmp : Binop → Prop
  | addOvf s : IsCmp (.addOvf s)
  | subOvf s : IsCmp (.subOvf s)
  | mulOvf s : IsCmp (.mulOvf s)
  | lt s : IsCmp (.lt s)
  | leq s : IsCmp (.leq s)

theorem WT_arith {op a b T} (hop : IsArith op) :
    (Term.mk (.binop op a b) T).WT ↔ ∃ n, BV a n ∧ BV b n ∧ T = .bitVector n := by
  rw [WT_binop]
  cases hop <;> simp only [Binop.WT, Ty.sort_eq, BV] <;> grind

theorem WT_cmp {op a b T} (hop : IsCmp op) :
    (Term.mk (.binop op a b) T).WT ↔ ∃ n, BV a n ∧ BV b n ∧ T = .bool := by
  rw [WT_binop]
  cases hop <;> simp only [Binop.WT, Ty.sort_eq, BV] <;> grind

theorem WT_neg {c a T} :
    (Term.mk (.unop (.neg c) a) T).WT ↔ ∃ n, BV a n ∧ T = .bitVector n := by
  rw [WT_unop]; simp only [Unop.WT, Ty.sort_eq, BV]; grind

theorem BV_of_refines {spec r : Term} {n : Int} (hR : Refines FS spec r) (w : spec.WT)
    (ht : spec.ty = .bitVector n) (hn : 0 < n) : BV r n := by
  obtain ⟨h1, h2⟩ := hR.syn w
  exact ⟨h1, by simpa [ht] using h2, hn⟩

theorem BV_arith {op a b r n} (hop : IsArith op) (hR : Refines FS (.mk (.binop op a b) a.ty) r)
    (wa : BV a n) (wb : BV b n) : BV r n :=
  BV_of_refines hR ((WT_arith hop).2 ⟨n, wa, wb, wa.2.1⟩) wa.2.1 wa.2.2

theorem BV_neg {c a r n} (hR : Refines FS (.mk (.unop (.neg c) a) a.ty) r) (wa : BV a n) :
    BV r n :=
  BV_of_refines hR (WT_neg.2 ⟨n, wa, wa.2.1⟩) wa.2.1 wa.2.2

theorem eval_arith {op a b T n} (hop : IsArith op) (wa : BV a n) (wb : BV b n)
    (hT : T = .bitVector n) {FS ρ} :
    eval FS ρ (.mk (.binop op a b) T) = evBinop FS op (eval FS ρ a) (eval FS ρ b) :=
  eval_binop ((WT_arith hop).2 ⟨n, wa, wb, hT⟩)

theorem eval_cmp {op a b T n} (hop : IsCmp op) (wa : BV a n) (wb : BV b n)
    (hT : T = .bool) {FS ρ} :
    eval FS ρ (.mk (.binop op a b) T) = evBinop FS op (eval FS ρ a) (eval FS ρ b) :=
  eval_binop ((WT_cmp hop).2 ⟨n, wa, wb, hT⟩)

theorem eval_neg {c a T n} (wa : BV a n) (hT : T = .bitVector n) {FS ρ} :
    eval FS ρ (.mk (.unop (.neg c) a) T) = evUnop FS (.neg c) (eval FS ρ a) :=
  eval_unop (WT_neg.2 ⟨n, wa, hT⟩)

/-- The value of a bit-vector term. -/
theorem eval_BV {t n} (w : BV t n) (FS ρ) :
    eval FS ρ t = none ∨ ∃ x : BitVec n.toNat, eval FS ρ t = some (.bv n.toNat x) := by
  rcases h : eval FS ρ t with _ | v
  · exact Or.inl rfl
  · right
    have hs := eval_hasSort h
    rw [w.2.1] at hs
    rcases v with _ | ⟨k, x⟩ | _ | _ | _ | _ <;> simp [Val.hasSort] at hs
    obtain ⟨hk, _⟩ := hs
    have : k = n.toNat := by omega
    subst this; exact ⟨x, rfl⟩

theorem BV_lit {z T n} (w : BV (.mk (.bitVec z) T) n) :
    T = .bitVector n ∧ 0 ≤ z ∧ z < 2 ^ n.toNat := by
  obtain ⟨w, hT, hn⟩ := w
  obtain ⟨m, hm, hT', h1, h2⟩ := WT_bitVec.1 w
  simp at hT; subst hT
  rcases hT' with h | h <;> simp at h
  subst h; simp; omega

theorem eval_lit {z T n} (w : BV (.mk (.bitVec z) T) n) {FS ρ} :
    eval FS ρ (.mk (.bitVec z) T) = some (.bv n.toNat (BitVec.ofInt _ z)) :=
  eval_bitVec' w.1 (Or.inl (by simpa using w.2.1))

theorem BV_mk_masked {n z : Int} (hn : 0 < n) : BV (mk_masked n z) n :=
  ⟨mk_masked_WT hn, rfl, hn⟩

theorem BV_arith_inv {op a b T n} (hop : IsArith op) (w : BV (.mk (.binop op a b) T) n) :
    BV a n ∧ BV b n ∧ T = .bitVector n := by
  obtain ⟨m, wa, wb, hT⟩ := (WT_arith hop).1 w.1
  have := w.2.1; simp only [Term.ty_mk] at this; subst this
  simp at hT; subst hT; exact ⟨wa, wb, rfl⟩

theorem BV_neg_inv {c a T n} (w : BV (.mk (.unop (.neg c) a) T) n) :
    BV a n ∧ T = .bitVector n := by
  obtain ⟨m, wa, hT⟩ := WT_neg.1 w.1
  have := w.2.1; simp only [Term.ty_mk] at this; subst this
  simp at hT; subst hT; exact ⟨wa, rfl⟩

theorem WT_not {a T} :
    (Term.mk (.unop .bvNot a) T).WT ↔ ∃ n, BV a n ∧ T = .bitVector n := by
  rw [WT_unop]; simp only [Unop.WT, Ty.sort_eq, BV]; grind

theorem BV_not_inv {a T n} (w : BV (.mk (.unop .bvNot a) T) n) :
    BV a n ∧ T = .bitVector n := by
  obtain ⟨m, wa, hT⟩ := WT_not.1 w.1
  have := w.2.1; simp only [Term.ty_mk] at this; subst this
  simp at hT; subst hT; exact ⟨wa, rfl⟩

theorem eval_not {a T n} (wa : BV a n) (hT : T = .bitVector n) {FS ρ} :
    eval FS ρ (.mk (.unop .bvNot a) T) = evUnop FS .bvNot (eval FS ρ a) :=
  eval_unop (WT_not.2 ⟨n, wa, hT⟩)

theorem evBinop_arith_none_l {FS op b} (hop : IsArith op ∨ IsCmp op) :
    evBinop FS op none b = none := by
  rcases hop with hop | hop <;> cases hop <;> simp [evBinop, checkedOp]

theorem evBinop_arith_none_r {FS op a} (hop : IsArith op ∨ IsCmp op) :
    evBinop FS op a none = none := by
  rcases hop with hop | hop <;> cases hop <;> simp [evBinop, checkedOp]

/-- The operands of a bit-vector operation that is not poison. -/
theorem evBinop_inv {FS ρ op a b n m v} (hop : IsArith op ∨ IsCmp op) (wa : BV a n)
    (wb : BV b m) (e : evBinop FS op (eval FS ρ a) (eval FS ρ b) = some v) :
    ∃ x y, eval FS ρ a = some (.bv n.toNat x) ∧ eval FS ρ b = some (.bv m.toNat y) ∧
      evBinop FS op (some (.bv n.toNat x)) (some (.bv m.toNat y)) = some v := by
  rcases eval_BV wa FS ρ with hx | ⟨x, hx⟩ <;> rw [hx] at e
  · rw [evBinop_arith_none_l hop] at e; cases e
  rcases eval_BV wb FS ρ with hy | ⟨y, hy⟩ <;> rw [hy] at e
  · rw [evBinop_arith_none_r hop] at e; cases e
  exact ⟨x, y, hx, hy, e⟩

theorem evUnop_inv {FS ρ op a n v} (wa : BV a n) (e : evUnop FS op (eval FS ρ a) = some v) :
    ∃ x, eval FS ρ a = some (.bv n.toNat x) ∧ evUnop FS op (some (.bv n.toNat x)) = some v := by
  rcases eval_BV wa FS ρ with hx | ⟨x, hx⟩ <;> rw [hx] at e
  · simp at e
  exact ⟨x, hx, e⟩

/-! ## If-then-else -/

theorem WT_ite' {g a b T} : (Term.mk (.triop .ite g a b) T).WT ↔
    g.ty = .bool ∧ b.ty = a.ty ∧ T = a.ty ∧ g.WT ∧ a.WT ∧ b.WT := by
  rw [WT_triop]; simp only [Triop.WT, Ty.sort_eq]; grind

theorem BV_ite_inv {g a b T n} (w : BV (.mk (.triop .ite g a b) T) n) :
    g.WT ∧ g.ty = .bool ∧ BV a n ∧ BV b n ∧ T = .bitVector n := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := WT_ite'.1 w.1
  have := w.2.1; simp only [Term.ty_mk] at this; subst this
  exact ⟨h4, h1, ⟨h5, h3.symm, w.2.2⟩, ⟨h6, h2.trans h3.symm, w.2.2⟩, rfl⟩

theorem eval_ite_inv {FS ρ g a b T v} (e : eval FS ρ (.mk (.triop .ite g a b) T) = some v) :
    (eval FS ρ g = some (.bool true) ∧ eval FS ρ a = some v) ∨
      (eval FS ρ g = some (.bool false) ∧ eval FS ρ b = some v) := by
  rw [eval_ite (eval_WT e)] at e
  split at e
  · exact .inl ⟨‹_›, e⟩
  · exact .inr ⟨‹_›, e⟩
  · cases e

theorem O_ite {FS : FloatSem} {O : Ops} (hO : O.Sound FS) {g A B n} (wg : g.WT) (hg : g.ty = .bool) (wA : BV A n)
    (wB : BV B n) : BV (O.b_ite g A B) n ∧ ∀ ρ v,
      ((eval FS ρ g = some (.bool true) ∧ eval FS ρ A = some v) ∨
        (eval FS ρ g = some (.bool false) ∧ eval FS ρ B = some v)) →
      eval FS ρ (O.b_ite g A B) = some v := by
  have w : (b_ite.spec g A B).WT := WT_ite'.2 ⟨hg, wB.2.1.trans wA.2.1.symm, rfl, wg, wA.1, wB.1⟩
  refine ⟨BV_of_refines (hO.b_ite g A B) w wA.2.1 wA.2.2, fun ρ v h => ?_⟩
  refine (hO.b_ite g A B).sem ρ v ?_
  rw [b_ite.spec, eval_ite w]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

/-- Pushing a binary operator into the branches of an [ite] on its left. -/
theorem Refines.ite_push_l {FS : FloatSem} {O : Ops} (hO : O.Sound FS) {op b l r T T' V A B}
    (hop : IsArith op)
    (hA : ∀ n, BV l n → BV V n → T = .bitVector n → BV A n ∧
      ∀ ρ v, evBinop FS op (eval FS ρ l) (eval FS ρ V) = some v → eval FS ρ A = some v)
    (hB : ∀ n, BV r n → BV V n → T = .bitVector n → BV B n ∧
      ∀ ρ v, evBinop FS op (eval FS ρ r) (eval FS ρ V) = some v → eval FS ρ B = some v) :
    Refines FS (.mk (.binop op (.mk (.triop .ite b l r) T) V) T') (O.b_ite b A B) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  all_goals obtain ⟨n, w1, wV, rfl⟩ := (WT_arith hop).1 w
  all_goals obtain ⟨wg, hg, wl, wr, hT⟩ := BV_ite_inv w1
  all_goals have hA := hA n wl wV hT
  all_goals have hB := hB n wr wV hT
  all_goals have hres := O_ite hO wg hg hA.1 hB.1
  · exact ⟨hres.1.1, by simp [hres.1.2.1]⟩
  · rw [eval_arith hop w1 wV rfl] at e
    obtain ⟨x, y, hx, hy, e⟩ := evBinop_inv (.inl hop) w1 wV e
    refine hres.2 ρ v ?_
    rcases eval_ite_inv hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1, hA.2 ρ v (by rw [h2, hy]; exact e)⟩
    · exact .inr ⟨h1, hB.2 ρ v (by rw [h2, hy]; exact e)⟩

/-- Pushing a binary operator into the branches of an [ite] on its right. -/
theorem Refines.ite_push_r {FS : FloatSem} {O : Ops} (hO : O.Sound FS) {op b l r T T' V A B}
    (hop : IsArith op)
    (hA : ∀ n, BV l n → BV V n → T = .bitVector n → BV A n ∧
      ∀ ρ v, evBinop FS op (eval FS ρ V) (eval FS ρ l) = some v → eval FS ρ A = some v)
    (hB : ∀ n, BV r n → BV V n → T = .bitVector n → BV B n ∧
      ∀ ρ v, evBinop FS op (eval FS ρ V) (eval FS ρ r) = some v → eval FS ρ B = some v) :
    Refines FS (.mk (.binop op V (.mk (.triop .ite b l r) T)) T') (O.b_ite b A B) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  all_goals obtain ⟨n, wV, w1, rfl⟩ := (WT_arith hop).1 w
  all_goals obtain ⟨wg, hg, wl, wr, hT⟩ := BV_ite_inv w1
  all_goals have hA := hA n wl wV hT
  all_goals have hB := hB n wr wV hT
  all_goals have hres := O_ite hO wg hg hA.1 hB.1
  · exact ⟨hres.1.1, by simp [hres.1.2.1]⟩
  · rw [eval_arith hop wV w1 rfl] at e
    obtain ⟨y, x, hy, hx, e⟩ := evBinop_inv (.inl hop) wV w1 e
    refine hres.2 ρ v ?_
    rcases eval_ite_inv hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1, hA.2 ρ v (by rw [h2, hy]; exact e)⟩
    · exact .inr ⟨h1, hB.2 ρ v (by rw [h2, hy]; exact e)⟩

/-- A rule function refining an arithmetic operator, as used by the rules. -/
theorem O_arith {FS op a b r n} (hop : IsArith op)
    (hR : Refines FS (.mk (.binop op a b) a.ty) r) (wa : BV a n) (wb : BV b n) :
    BV r n ∧ ∀ ρ v, evBinop FS op (eval FS ρ a) (eval FS ρ b) = some v → eval FS ρ r = some v :=
  ⟨BV_arith hop hR wa wb, fun ρ v h => hR.sem ρ v (by rw [eval_arith hop wa wb wa.2.1]; exact h)⟩

/-- The literal rebuilt by [mk_bv] has the value of the original one. -/
theorem eval_mk_bv_lit {FS ρ z T n} (w : BV (.mk (.bitVec z) T) n) :
    eval FS ρ (mk_bv n z) = eval FS ρ (.mk (.bitVec z) T) := by
  rw [mk_bv, eval_mk_masked w.2.2, eval_lit w]

theorem BV_mk_bv {n z : Int} (hn : 0 < n) : BV (mk_bv n z) n := BV_mk_masked hn

theorem O_arith_lit {FS op a z T n r} (hop : IsArith op)
    (hR : Refines FS (.mk (.binop op a (mk_bv n z)) a.ty) r) (wa : BV a n)
    (wV : BV (.mk (.bitVec z) T) n) : BV r n ∧
      ∀ ρ v, evBinop FS op (eval FS ρ a) (eval FS ρ (.mk (.bitVec z) T)) = some v →
        eval FS ρ r = some v := by
  have := O_arith hop hR wa (BV_mk_bv wV.2.2)
  refine ⟨this.1, fun ρ v e => this.2 ρ v ?_⟩
  rwa [eval_mk_bv_lit wV]

/-! ## Commutativity -/

theorem bvBin_comm {f g : ∀ {n : Nat}, BitVec n → BitVec n → Option Val}
    (h : ∀ n (x y : BitVec n), f x y = g y x) (a b : Option Val) : bvBin f a b = bvBin g b a := by
  apply Option.ext; intro v
  rw [bvBin_eq_some, bvBin_eq_some]
  constructor
  · rintro ⟨n, x, y, h1, h2, h3⟩; exact ⟨n, y, x, h2, h1, by rw [← h]; exact h3⟩
  · rintro ⟨n, x, y, h1, h2, h3⟩; exact ⟨n, y, x, h2, h1, by rw [h]; exact h3⟩

theorem saddOverflow_comm {w} (x y : BitVec w) : x.saddOverflow y = y.saddOverflow x := by
  simp [BitVec.saddOverflow, Int.add_comm]
theorem uaddOverflow_comm {w} (x y : BitVec w) : x.uaddOverflow y = y.uaddOverflow x := by
  simp [BitVec.uaddOverflow, Nat.add_comm]
theorem smulOverflow_comm {w} (x y : BitVec w) : x.smulOverflow y = y.smulOverflow x := by
  simp [BitVec.smulOverflow, Int.mul_comm]
theorem umulOverflow_comm {w} (x y : BitVec w) : x.umulOverflow y = y.umulOverflow x := by
  simp [BitVec.umulOverflow, Nat.mul_comm]

/-- The commutative binary operators. -/
inductive IsComm : Binop → Prop
  | add c : IsComm (.add c)
  | mul c : IsComm (.mul c)
  | addOvf s : IsComm (.addOvf s)
  | mulOvf s : IsComm (.mulOvf s)

theorem evBinop_comm {FS op} (hop : IsComm op) (a b : Option Val) :
    evBinop FS op a b = evBinop FS op b a := by
  cases hop <;> simp only [evBinop, checkedOp] <;> apply bvBin_comm <;> intro n x y
  · rw [saddOverflow_comm, uaddOverflow_comm, BitVec.add_comm]
  · rw [smulOverflow_comm, umulOverflow_comm, BitVec.mul_comm]
  · rw [saddOverflow_comm, uaddOverflow_comm]
  · rw [smulOverflow_comm, umulOverflow_comm]

theorem WT_comm {op a b T} (hop : IsComm op) :
    (Term.mk (.binop op a b) T).WT → (Term.mk (.binop op b a) T).WT := by
  cases hop
  · rw [WT_arith (.add _), WT_arith (.add _)]; rintro ⟨n, h1, h2, h3⟩; exact ⟨n, h2, h1, h3⟩
  · rw [WT_arith (.mul _), WT_arith (.mul _)]; rintro ⟨n, h1, h2, h3⟩; exact ⟨n, h2, h1, h3⟩
  · rw [WT_cmp (.addOvf _), WT_cmp (.addOvf _)]; rintro ⟨n, h1, h2, h3⟩; exact ⟨n, h2, h1, h3⟩
  · rw [WT_cmp (.mulOvf _), WT_cmp (.mulOvf _)]; rintro ⟨n, h1, h2, h3⟩; exact ⟨n, h2, h1, h3⟩

theorem Refines.comm {FS op a b T} (hop : IsComm op) :
    Refines FS (.mk (.binop op a b) T) (.mk (.binop op b a) T) := by
  refine Refines.intro (fun w => ⟨WT_comm hop w, rfl⟩) (fun ρ v w w' e => ?_)
  rw [eval_binop w] at e; rw [eval_binop w', evBinop_comm hop]; exact e

theorem Refines.comm' {FS op a b T T'} (hop : IsComm op)
    (hT : (Term.mk (.binop op a b) T).WT → T' = T) :
    Refines FS (.mk (.binop op a b) T) (.mk (.binop op b a) T') := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · rw [hT w]; exact ⟨WT_comm hop w, rfl⟩
  · rw [eval_binop w] at e; rw [eval_binop w', evBinop_comm hop]; exact e

theorem Refines.commut_binop {FS O op a b T} (hop : IsComm op) :
    Refines FS (.mk (.binop op a b) T) (.mk (mk_commut_binop O op a b) T) := by
  unfold mk_commut_binop; split
  · exact Refines.refl
  · exact Refines.comm hop

theorem O_arith_lit' {FS op a z T n r} (hop : IsComm op) (hop' : IsArith op)
    (hR : Refines FS (.mk (.binop op a (mk_bv n z)) a.ty) r) (wa : BV a n)
    (wV : BV (.mk (.bitVec z) T) n) : BV r n ∧
      ∀ ρ v, evBinop FS op (eval FS ρ (.mk (.bitVec z) T)) (eval FS ρ a) = some v →
        eval FS ρ r = some v := by
  have := O_arith_lit hop' hR wa wV
  refine ⟨this.1, fun ρ v e => this.2 ρ v ?_⟩
  rwa [evBinop_comm hop]

/-! ## Literals as signed and unsigned integers -/

theorem two_pow_pred {w : Nat} (hw : 0 < w) : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  simp [Int.pow_succ]; omega

theorem toNat_ofInt_lit {w : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ w) :
    ((BitVec.ofInt w z).toNat : Int) = z := by
  rw [BitVec.toNat_ofInt]
  have : z % ((2 ^ w : Nat) : Int) = z := Int.emod_eq_of_lt h0 (by simpa using h1)
  rw [this]; omega

theorem toInt_ofInt_lit {w : Nat} {z : Int} (hw : 0 < w) (h0 : 0 ≤ z) (h1 : z < 2 ^ w) :
    (BitVec.ofInt w z).toInt = if 2 ^ (w - 1) ≤ z then z - 2 ^ w else z := by
  rw [BitVec.toInt_eq_toNat_cond]
  have h := toNat_ofInt_lit h0 h1
  have h2 := two_pow_pred hw
  have : ((2 ^ w : Nat) : Int) = 2 ^ w := by simp
  split <;> split <;> omega

theorem zasr_zero (z : Int) : zasr z 0 = z := by simp [zasr]

theorem signed_extract_lit {n z : Int} (hn : 0 < n) (h0 : 0 ≤ z) (h1 : z < 2 ^ n.toNat) :
    signed_extract z 0 n = (BitVec.ofInt n.toNat z).toInt := by
  rw [toInt_ofInt_lit (by omega) h0 h1, signed_extract, zasr_zero]
  simp only [Int.emod_eq_of_lt h0 h1]

theorem bv_to_z_lit {s : Bool} {n z : Int} (hn : 0 < n) (h0 : 0 ≤ z) (h1 : z < 2 ^ n.toNat) :
    bv_to_z s n z =
      if s then (BitVec.ofInt n.toNat z).toInt else ((BitVec.ofInt n.toNat z).toNat : Int) := by
  cases s
  · simp only [bv_to_z, toNat_ofInt_lit h0 h1]; rfl
  · simp [bv_to_z, signed_extract_lit hn h0 h1]

theorem min_for_eq {s : Bool} {n : Int} (_hn : 0 < n) :
    min_for s n = if s then -2 ^ (n.toNat - 1) else 0 := by
  cases s <;> simp [min_for, zshiftl]

theorem max_for_eq {s : Bool} {n : Int} (_hn : 0 < n) :
    max_for s n = if s then 2 ^ (n.toNat - 1) - 1 else 2 ^ n.toNat - 1 := by
  cases s <;> simp [max_for, zshiftl]

theorem bv_to_z_lit' {s : Bool} {n z : Int} (hn : 0 < n) (h0 : 0 ≤ z) (h1 : z < 2 ^ n.toNat) :
    bv_to_z s n z = if s then (if 2 ^ (n.toNat - 1) ≤ z then z - 2 ^ n.toNat else z) else z := by
  rw [bv_to_z_lit hn h0 h1, toInt_ofInt_lit (by omega) h0 h1, toNat_ofInt_lit h0 h1]

/-- Facts about a literal, for `omega`. -/
theorem lit_facts {n z : Int} (hn : 0 < n) (h0 : 0 ≤ z) (h1 : z < 2 ^ n.toNat) :
    ((BitVec.ofInt n.toNat z).toNat : Int) = z ∧
      (BitVec.ofInt n.toNat z).toInt = (if 2 ^ (n.toNat - 1) ≤ z then z - 2 ^ n.toNat else z) ∧
      (2 : Int) ^ n.toNat = 2 * 2 ^ (n.toNat - 1) :=
  ⟨toNat_ofInt_lit h0 h1, toInt_ofInt_lit (by omega) h0 h1, two_pow_pred (by omega)⟩

theorem natCast_two_pow (k : Nat) : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by push_cast; rfl

theorem overflows_add_lit {s : Bool} {n l r : Int} (hn : 0 < n) (hl0 : 0 ≤ l)
    (hl1 : l < 2 ^ n.toNat) (hr0 : 0 ≤ r) (hr1 : r < 2 ^ n.toNat) :
    overflows_add s n l r =
      if s then (BitVec.ofInt n.toNat l).saddOverflow (BitVec.ofInt n.toNat r)
      else (BitVec.ofInt n.toNat l).uaddOverflow (BitVec.ofInt n.toNat r) := by
  rw [overflows_add, bv_to_z_lit hn hl0 hl1, bv_to_z_lit hn hr0 hr1, min_for_eq hn,
    max_for_eq hn]
  have := natCast_two_pow n.toNat
  cases s <;> simp only [BitVec.saddOverflow, BitVec.uaddOverflow] <;>
    simp only [Bool.false_eq_true, ↓reduceIte, ge_iff_le, gt_iff_lt, ← Bool.decide_or,
      decide_eq_decide] <;> omega

theorem overflows_sub_lit {s : Bool} {n l r : Int} (hn : 0 < n) (hl0 : 0 ≤ l)
    (hl1 : l < 2 ^ n.toNat) (hr0 : 0 ≤ r) (hr1 : r < 2 ^ n.toNat) :
    overflows_sub s n l r =
      if s then (BitVec.ofInt n.toNat l).ssubOverflow (BitVec.ofInt n.toNat r)
      else (BitVec.ofInt n.toNat l).usubOverflow (BitVec.ofInt n.toNat r) := by
  rw [overflows_sub, bv_to_z_lit hn hl0 hl1, bv_to_z_lit hn hr0 hr1, min_for_eq hn,
    max_for_eq hn]
  have := natCast_two_pow n.toNat
  have := (BitVec.ofInt n.toNat l).isLt
  cases s <;> simp only [BitVec.ssubOverflow, BitVec.usubOverflow] <;>
    simp only [Bool.false_eq_true, ↓reduceIte, ge_iff_le, gt_iff_lt, ← Bool.decide_or,
      decide_eq_decide] <;> omega

theorem overflows_mul_lit {s : Bool} {n l r : Int} (hn : 0 < n) (hl0 : 0 ≤ l)
    (hl1 : l < 2 ^ n.toNat) (hr0 : 0 ≤ r) (hr1 : r < 2 ^ n.toNat) :
    overflows_mul s n l r =
      if s then (BitVec.ofInt n.toNat l).smulOverflow (BitVec.ofInt n.toNat r)
      else (BitVec.ofInt n.toNat l).umulOverflow (BitVec.ofInt n.toNat r) := by
  rw [overflows_mul, bv_to_z_lit hn hl0 hl1, bv_to_z_lit hn hr0 hr1, min_for_eq hn,
    max_for_eq hn]
  have := natCast_two_pow n.toNat
  have : (((BitVec.ofInt n.toNat l).toNat * (BitVec.ofInt n.toNat r).toNat : Nat) : Int) =
    ((BitVec.ofInt n.toNat l).toNat : Int) * ((BitVec.ofInt n.toNat r).toNat : Int) := by
    push_cast; rfl
  cases s <;> simp only [BitVec.smulOverflow, BitVec.umulOverflow] <;>
    simp only [Bool.false_eq_true, ↓reduceIte, ge_iff_le, gt_iff_lt, ← Bool.decide_or,
      decide_eq_decide] <;> omega

/-! ## Overflow flags -/

section Ovf
variable {w : Nat} {x y z : BitVec w}

theorem sadd_ok : x.saddOverflow y = false ↔
    -2 ^ (w - 1) ≤ x.toInt + y.toInt ∧ x.toInt + y.toInt < 2 ^ (w - 1) := by
  simp [BitVec.saddOverflow]; omega
theorem ssub_ok : x.ssubOverflow y = false ↔
    -2 ^ (w - 1) ≤ x.toInt - y.toInt ∧ x.toInt - y.toInt < 2 ^ (w - 1) := by
  simp [BitVec.ssubOverflow]; omega
theorem smul_ok : x.smulOverflow y = false ↔
    -2 ^ (w - 1) ≤ x.toInt * y.toInt ∧ x.toInt * y.toInt < 2 ^ (w - 1) := by
  simp [BitVec.smulOverflow]; omega
theorem uadd_ok : x.uaddOverflow y = false ↔ x.toNat + y.toNat < 2 ^ w := by
  simp [BitVec.uaddOverflow]
theorem usub_ok : x.usubOverflow y = false ↔ y.toNat ≤ x.toNat := by
  simp [BitVec.usubOverflow]
theorem umul_ok : x.umulOverflow y = false ↔ x.toNat * y.toNat < 2 ^ w := by
  simp [BitVec.umulOverflow]

theorem toInt_add_ok (h : x.saddOverflow y = false) : (x + y).toInt = x.toInt + y.toInt :=
  BitVec.toInt_add_of_not_saddOverflow (by simp [h])
theorem toInt_sub_ok (h : x.ssubOverflow y = false) : (x - y).toInt = x.toInt - y.toInt :=
  BitVec.toInt_sub_of_not_ssubOverflow (by simp [h])
theorem toInt_mul_ok (h : x.smulOverflow y = false) : (x * y).toInt = x.toInt * y.toInt :=
  BitVec.toInt_mul_of_not_smulOverflow (by simp [h])
theorem toNat_add_ok (h : x.uaddOverflow y = false) : (x + y).toNat = x.toNat + y.toNat :=
  BitVec.toNat_add_of_not_uaddOverflow (by simp [h])
theorem toNat_sub_ok (h : x.usubOverflow y = false) : (x - y).toNat = x.toNat - y.toNat :=
  BitVec.toNat_sub_of_not_usubOverflow (by simp [h])
theorem toNat_mul_ok (h : x.umulOverflow y = false) : (x * y).toNat = x.toNat * y.toNat :=
  BitVec.toNat_mul_of_not_umulOverflow (by simp [h])


macro "ovf" : tactic =>
  `(tactic| (simp only [sadd_ok, ssub_ok, smul_ok, uadd_ok, usub_ok, umul_ok] at *; omega))

/-! Reassociations of constants that keep the flags. Each is stated for the signed and the
unsigned flags. -/

-- (x + r) + y  ~>  (x + y) + r
theorem sadd_reassoc (h1 : x.saddOverflow z = false) (h2 : (x + z).saddOverflow y = false)
    (h3 : x.saddOverflow y = false) : (x + y).saddOverflow z = false := by
  have := toInt_add_ok h1; have := toInt_add_ok h3; ovf
theorem uadd_reassoc (h1 : x.uaddOverflow z = false) (h2 : (x + z).uaddOverflow y = false)
    (h3 : x.uaddOverflow y = false) : (x + y).uaddOverflow z = false := by
  have := toNat_add_ok h1; have := toNat_add_ok h3; ovf

-- (l - c) + v  ~>  l + (v - c)
theorem ssub_add_reassoc (h1 : x.ssubOverflow z = false) (h2 : (x - z).saddOverflow y = false)
    (h3 : y.ssubOverflow z = false) : x.saddOverflow (y - z) = false := by
  have := toInt_sub_ok h1; have := toInt_sub_ok h3; ovf
theorem usub_add_reassoc (h1 : x.usubOverflow z = false) (h2 : (x - z).uaddOverflow y = false)
    (h3 : y.usubOverflow z = false) : x.uaddOverflow (y - z) = false := by
  have := toNat_sub_ok h1; have := toNat_sub_ok h3; ovf

-- (c - r) + v  ~>  (c + v) - r
theorem ssub_add_reassoc' (h1 : x.ssubOverflow z = false) (h2 : (x - z).saddOverflow y = false)
    (h3 : x.saddOverflow y = false) : (x + y).ssubOverflow z = false := by
  have := toInt_sub_ok h1; have := toInt_add_ok h3; ovf
theorem usub_add_reassoc' (h1 : x.usubOverflow z = false) (h2 : (x - z).uaddOverflow y = false)
    (h3 : x.uaddOverflow y = false) : (x + y).usubOverflow z = false := by
  have := toNat_sub_ok h1; have := toNat_add_ok h3; ovf

-- (c - s) - v  ~>  (c - v) - s
theorem ssub_sub_reassoc (h1 : x.ssubOverflow z = false) (h2 : (x - z).ssubOverflow y = false)
    (h3 : x.ssubOverflow y = false) : (x - y).ssubOverflow z = false := by
  have := toInt_sub_ok h1; have := toInt_sub_ok h3; ovf
theorem usub_sub_reassoc (h1 : x.usubOverflow z = false) (h2 : (x - z).usubOverflow y = false)
    (h3 : x.usubOverflow y = false) : (x - y).usubOverflow z = false := by
  have := toNat_sub_ok h1; have := toNat_sub_ok h3; ovf

-- (s - c) - v  ~>  s - (c + v)
theorem ssub_sub_reassoc' (h1 : x.ssubOverflow z = false) (h2 : (x - z).ssubOverflow y = false)
    (h3 : z.saddOverflow y = false) : x.ssubOverflow (z + y) = false := by
  have := toInt_sub_ok h1; have := toInt_add_ok h3; ovf
theorem usub_sub_reassoc' (h1 : x.usubOverflow z = false) (h2 : (x - z).usubOverflow y = false)
    (h3 : z.uaddOverflow y = false) : x.usubOverflow (z + y) = false := by
  have := toNat_sub_ok h1; have := toNat_add_ok h3; ovf

-- v - (r + l)  ~>  (v - r) - l
theorem sadd_sub_reassoc (h1 : z.saddOverflow y = false) (h2 : x.ssubOverflow (z + y) = false)
    (h3 : x.ssubOverflow z = false) : (x - z).ssubOverflow y = false := by
  have := toInt_add_ok h1; have := toInt_sub_ok h3; ovf
theorem uadd_sub_reassoc (h1 : z.uaddOverflow y = false) (h2 : x.usubOverflow (z + y) = false)
    (h3 : x.usubOverflow z = false) : (x - z).usubOverflow y = false := by
  have := toNat_add_ok h1; have := toNat_sub_ok h3; ovf

-- (r + l) - v  ~>  l - (v - r)
theorem sadd_sub_reassoc' (h1 : z.saddOverflow x = false) (h2 : (z + x).ssubOverflow y = false)
    (h3 : y.ssubOverflow z = false) : x.ssubOverflow (y - z) = false := by
  have := toInt_add_ok h1; have := toInt_sub_ok h3; ovf
theorem uadd_sub_reassoc' (h1 : z.uaddOverflow x = false) (h2 : (z + x).usubOverflow y = false)
    (h3 : y.usubOverflow z = false) : x.usubOverflow (y - z) = false := by
  have := toNat_add_ok h1; have := toNat_sub_ok h3; ovf

-- (r + l) - v  ~>  l + (r - v)
theorem sadd_sub_reassoc'' (h1 : z.saddOverflow x = false) (h2 : (z + x).ssubOverflow y = false)
    (h3 : z.ssubOverflow y = false) : x.saddOverflow (z - y) = false := by
  have := toInt_add_ok h1; have := toInt_sub_ok h3; ovf
theorem uadd_sub_reassoc'' (h1 : z.uaddOverflow x = false) (h2 : (z + x).usubOverflow y = false)
    (h3 : z.usubOverflow y = false) : x.uaddOverflow (z - y) = false := by
  have := toNat_add_ok h1; have := toNat_sub_ok h3; ovf

end Ovf

theorem mask_lits {c : Checked} {za zb : Int} {Ta Tb : Ty} {is_add : Bool} :
    mask_checked_after_fold c (.mk (.bitVec za) Ta) (.mk (.bitVec zb) Tb) is_add =
      { signed := c.signed && !(if is_add then overflows_add true (size_of_ty Ta) za zb
          else overflows_sub true (size_of_ty Ta) za zb),
        unsigned := c.unsigned && !(if is_add then overflows_add false (size_of_ty Ta) za zb
          else overflows_sub false (size_of_ty Ta) za zb) } := by
  simp [mask_checked_after_fold, firstSome, checked_has, HOrElse.hOrElse, OrElse.orElse,
    Option.orElse]

/-! ## Generic refinement lemmas for the arithmetic rules -/

theorem Refines.arith_intro {FS op a b T r} (hop : IsArith op)
    (hsyn : ∀ n, BV a n → BV b n → T = .bitVector n → BV r n)
    (hsem : ∀ n, BV a n → BV b n → T = .bitVector n → ∀ ρ (x y : BitVec n.toNat) v,
      eval FS ρ a = some (.bv _ x) → eval FS ρ b = some (.bv _ y) →
      evBinop FS op (some (.bv _ x)) (some (.bv _ y)) = some v → eval FS ρ r = some v) :
    Refines FS (.mk (.binop op a b) T) r := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  all_goals obtain ⟨n, wa, wb, hT⟩ := (WT_arith hop).1 w
  · have := hsyn n wa wb hT; exact ⟨this.1, by simp [this.2.1, hT]⟩
  · rw [eval_arith hop wa wb hT] at e
    obtain ⟨x, y, hx, hy, e⟩ := evBinop_inv (.inl hop) wa wb e
    exact hsem n wa wb hT ρ x y v hx hy e

theorem Refines.cmp_intro {FS op a b T r} (hop : IsCmp op)
    (hsyn : ∀ n, BV a n → BV b n → T = .bool → r.WT ∧ r.ty = .bool)
    (hsem : ∀ n, BV a n → BV b n → T = .bool → ∀ ρ (x y : BitVec n.toNat) v,
      eval FS ρ a = some (.bv _ x) → eval FS ρ b = some (.bv _ y) →
      evBinop FS op (some (.bv _ x)) (some (.bv _ y)) = some v → eval FS ρ r = some v) :
    Refines FS (.mk (.binop op a b) T) r := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  all_goals obtain ⟨n, wa, wb, hT⟩ := (WT_cmp hop).1 w
  · have := hsyn n wa wb hT; exact ⟨this.1, by simp [this.2, hT]⟩
  · rw [eval_cmp hop wa wb hT] at e
    obtain ⟨x, y, hx, hy, e⟩ := evBinop_inv (.inr hop) wa wb e
    exact hsem n wa wb hT ρ x y v hx hy e

theorem Refines.neg_intro {FS c a T r}
    (hsyn : ∀ n, BV a n → T = .bitVector n → BV r n)
    (hsem : ∀ n, BV a n → T = .bitVector n → ∀ ρ (x : BitVec n.toNat) v,
      eval FS ρ a = some (.bv _ x) → evUnop FS (.neg c) (some (.bv _ x)) = some v →
      eval FS ρ r = some v) :
    Refines FS (.mk (.unop (.neg c) a) T) r := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  all_goals obtain ⟨n, wa, hT⟩ := WT_neg.1 w
  · have := hsyn n wa hT; exact ⟨this.1, by simp [this.2.1, hT]⟩
  · rw [eval_neg wa hT] at e
    obtain ⟨x, hx, e⟩ := evUnop_inv wa e
    exact hsem n wa hT ρ x v hx e

/-- Evaluating a rule function refining an arithmetic operator. -/
theorem O_eval {FS op a b r n} (hop : IsArith op) (hR : Refines FS (.mk (.binop op a b) a.ty) r)
    (wa : BV a n) (wb : BV b n) {ρ x y v} (hx : eval FS ρ a = some (.bv n.toNat x))
    (hy : eval FS ρ b = some (.bv n.toNat y))
    (e : evBinop FS op (some (.bv n.toNat x)) (some (.bv n.toNat y)) = some v) :
    eval FS ρ r = some v :=
  (O_arith hop hR wa wb).2 ρ v (by rw [hx, hy]; exact e)

theorem O_neg {FS c a r n} (hR : Refines FS (.mk (.unop (.neg c) a) a.ty) r) (wa : BV a n) :
    BV r n ∧ ∀ ρ x v, eval FS ρ a = some (.bv n.toNat x) →
      evUnop FS (.neg c) (some (.bv n.toNat x)) = some v → eval FS ρ r = some v :=
  ⟨BV_neg hR wa, fun ρ x v hx e => hR.sem ρ v (by rw [eval_neg wa wa.2.1, hx]; exact e)⟩

theorem O_cmp {FS op a b r n} (hop : IsCmp op) (hR : Refines FS (.mk (.binop op a b) .bool) r)
    (wa : BV a n) (wb : BV b n) : (r.WT ∧ r.ty = .bool) ∧ ∀ ρ x y v,
      eval FS ρ a = some (.bv n.toNat x) → eval FS ρ b = some (.bv n.toNat y) →
      evBinop FS op (some (.bv n.toNat x)) (some (.bv n.toNat y)) = some v →
      eval FS ρ r = some v := by
  have w : (Term.mk (.binop op a b) .bool).WT := (WT_cmp hop).2 ⟨n, wa, wb, rfl⟩
  refine ⟨?_, fun ρ x y v hx hy e => hR.sem ρ v (by rw [eval_cmp hop wa wb rfl, hx, hy]; exact e)⟩
  have := hR.syn w; exact ⟨this.1, by simpa using this.2⟩

theorem lit_eval_eq {FS ρ z T n x} (w : BV (.mk (.bitVec z) T) n)
    (h : eval FS ρ (.mk (.bitVec z) T) = some (.bv n.toNat x)) : x = BitVec.ofInt _ z := by
  rw [eval_lit w] at h; simp at h; exact h.symm

theorem size_lit {z T n} (w : BV (.mk (.bitVec z) T) n) : size (.mk (.bitVec z) T) = n := by
  obtain ⟨rfl, -⟩ := BV_lit w; rfl

theorem size_BV {t n} (w : BV t n) : size t = n := by simp [w.2.1]


theorem size_ty_lit {z T n} (w : BV (.mk (.bitVec z) T) n) : size_of_ty T = n := by
  obtain ⟨rfl, -⟩ := BV_lit w; rfl

theorem BV_lit_of {z n : Int} (hn : 0 < n) (h0 : 0 ≤ z) (h1 : z < 2 ^ n.toNat) :
    BV (.mk (.bitVec z) (.bitVector n)) n :=
  ⟨WT_bitVec.2 ⟨n.toNat, by omega, Or.inl (by simp; omega), h0, h1⟩, rfl, hn⟩

theorem one_lt_two_pow' {n : Int} (hn : 0 < n) : (1 : Int) < 2 ^ n.toNat := by
  have := two_pow_pred (w := n.toNat) (by omega)
  have := two_pow_pos' (n.toNat - 1); omega

theorem BV_bv_zero {n : Int} (hn : 0 < n) : BV (bv_zero n) n :=
  BV_lit_of hn (Int.le_refl _) (two_pow_pos' _)

theorem BV_bv_one {n : Int} (hn : 0 < n) : BV (bv_one n) n :=
  BV_lit_of hn (by omega) (one_lt_two_pow' hn)

theorem eval_bv_zero {FS ρ} {n : Int} (hn : 0 < n) :
    eval FS ρ (bv_zero n) = some (.bv n.toNat 0) := by
  rw [bv_zero, eval_lit (BV_bv_zero hn)]; simp

theorem eval_bv_one {FS ρ} {n : Int} (hn : 0 < n) :
    eval FS ρ (bv_one n) = some (.bv n.toNat 1) := by
  rw [bv_one, eval_lit (BV_bv_one hn)]; simp

theorem ssubOverflow_zero_intMin {w : Nat} (hw : 0 < w) :
    (0#w).ssubOverflow (BitVec.intMin w) = true := by
  simp [BitVec.ssubOverflow, BitVec.toInt_intMin_of_pos hw]


theorem checkedOp_unchecked {c so uo f a b v} (h : checkedOp c so uo f a b = some v) :
    checkedOp unchecked so uo f a b = some v := by
  rw [checkedOp_eq_some] at *
  obtain ⟨n, x, y, h1, h2, -, -, h3⟩ := h
  exact ⟨n, x, y, h1, h2, by simp [unchecked], by simp [unchecked], h3⟩

theorem evBinop_add_unchecked {FS c a b v} (h : evBinop FS (.add c) a b = some v) :
    evBinop FS (.add unchecked) a b = some v := checkedOp_unchecked h
theorem evBinop_sub_unchecked {FS c a b v} (h : evBinop FS (.sub c) a b = some v) :
    evBinop FS (.sub unchecked) a b = some v := checkedOp_unchecked h
theorem evBinop_mul_unchecked {FS c a b v} (h : evBinop FS (.mul c) a b = some v) :
    evBinop FS (.mul unchecked) a b = some v := checkedOp_unchecked h

theorem WT_bvOfBool {m g T} : (Term.mk (.unop (.bvOfBool m) g) T).WT ↔
    0 < m ∧ g.ty = .bool ∧ T = .bitVector m ∧ g.WT := by
  simp [WT_unop, Unop.WT, and_assoc]

theorem BV_ofBool_inv {m g T n} (w : BV (.mk (.unop (.bvOfBool m) g) T) n) :
    m = n ∧ g.WT ∧ g.ty = .bool ∧ T = .bitVector n := by
  obtain ⟨h1, h2, h3, h4⟩ := WT_bvOfBool.1 w.1
  have := w.2.1; simp only [Term.ty_mk] at this; subst this
  simp at h3; subst h3; exact ⟨rfl, h4, h2, rfl⟩

theorem eval_ofBool_inv {FS ρ m g T n x} (w : BV (.mk (.unop (.bvOfBool m) g) T) n)
    (e : eval FS ρ (.mk (.unop (.bvOfBool m) g) T) = some (.bv n.toNat x)) :
    ∃ b, eval FS ρ g = some (.bool b) ∧ x = if b then 1 else 0 := by
  obtain ⟨rfl, -⟩ := BV_ofBool_inv w
  rw [eval_unop w.1] at e
  rcases eg : eval FS ρ g with _ | ⟨b | _ | _ | _ | _ | _⟩ <;> rw [eg] at e <;>
    simp [evUnop] at e
  exact ⟨b, rfl, e.symm⟩

theorem eval_ite_inv' {FS ρ g a b T n x} (w : BV (.mk (.triop .ite g a b) T) n)
    (e : eval FS ρ (.mk (.triop .ite g a b) T) = some (.bv n.toNat x)) :
    (eval FS ρ g = some (.bool true) ∧ eval FS ρ a = some (.bv n.toNat x)) ∨
      (eval FS ρ g = some (.bool false) ∧ eval FS ρ b = some (.bv n.toNat x)) :=
  eval_ite_inv e


/-! ## Division and remainder -/

theorem smod_formula (a b : Int) :
    (if a.tmod b < 0 ∧ ¬ b < 0 then a.tmod b + b
     else if 0 < a.tmod b ∧ b < 0 then a.tmod b + b else a.tmod b) = a.fmod b := by
  rw [Int.tmod_eq_emod, Int.fmod_eq_emod]
  by_cases hb : b = 0
  · subst hb; simp
  have h1 := Int.emod_nonneg a hb
  have h2 := Int.emod_lt a hb
  simp only [Int.dvd_iff_emod_eq_zero]
  rcases Int.lt_or_lt_of_ne hb with hb' | hb'
  · have : (b.natAbs : Int) = -b := by omega
    repeat' split
    all_goals simp_all <;> omega
  · have : (b.natAbs : Int) = b := by omega
    repeat' split
    all_goals simp_all <;> omega


theorem ne_intMin_of_toInt {w : Nat} {C : BitVec w} (hw : 0 < w) (h : C.toInt ≠ -2 ^ (w - 1)) :
    C ≠ BitVec.intMin w := by
  rintro rfl; exact h (BitVec.toInt_intMin_of_pos hw)

theorem smul_neg_swap {w : Nat} {C X : BitVec w} (hC : C ≠ BitVec.intMin w)
    (hX : X ≠ BitVec.intMin w) (h : C.smulOverflow (-X) = false) :
    (-C).smulOverflow X = false := by
  rw [smul_ok] at *
  rw [BitVec.toInt_neg_of_ne_intMin hC]; rw [BitVec.toInt_neg_of_ne_intMin hX] at h
  rw [Int.neg_mul]; rw [Int.mul_neg] at h; omega


theorem smtSDiv_of_ne_zero {w : Nat} {x y : BitVec w} (h : y ≠ 0#w) : x.smtSDiv y = x.sdiv y := by
  have h' : -y ≠ 0#w := by intro e; apply h; rw [← BitVec.neg_neg (x := y), e]; simp
  rw [BitVec.smtSDiv_eq, BitVec.sdiv_eq]
  cases x.msb <;> cases y.msb <;> simp [BitVec.smtUDiv_eq, h, h'] <;> rfl

theorem one_ne_zero' {w : Nat} (hw : 0 < w) : (1#w) ≠ 0#w := by
  intro e; have := congrArg BitVec.toNat e
  simp [Nat.one_mod_eq_one] at this; omega

theorem Val.bv_congr {n m : Nat} {x : BitVec n} {y : BitVec m} (h : n = m) (hv : x.toNat = y.toNat) :
    Val.bv n x = Val.bv m y := by
  subst h; rw [BitVec.eq_of_toNat_eq hv]


theorem Refines.retype {FS k t t'} (h : (Term.mk k t).WT → t' = t) :
    Refines FS (.mk k t) (.mk k t') := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain rfl := h w; exact ⟨w, rfl⟩
  · obtain rfl := h w; exact e



theorem udiv_mul_cancel {w : Nat} {N X D K : BitVec w} {n d k : Nat} (hN : N.toNat = n)
    (hD : D.toNat = d) (hK : K.toNat = k) (hdk : d = n * k) (hk0 : d = 0 → k = 0)
    (hov : n * X.toNat < 2 ^ w) : (N * X).smtUDiv D = X.smtUDiv K := by
  rw [BitVec.smtUDiv_eq, BitVec.smtUDiv_eq]
  by_cases hd : d = 0
  · have := hk0 hd
    have h1 : D = 0#w := BitVec.eq_of_toNat_eq (by simp [hD, hd])
    have h2 : K = 0#w := BitVec.eq_of_toNat_eq (by simp [hK, this])
    simp [h1, h2]
  · have hn : 0 < n := by rcases Nat.eq_zero_or_pos n with h | h <;> simp_all
    have hk : 0 < k := by rcases Nat.eq_zero_or_pos k with h | h <;> simp_all
    have h1 : D ≠ 0#w := fun h => hd (by rw [← hD, h]; simp)
    have h2 : K ≠ 0#w := fun h => by rw [h] at hK; simp at hK; omega
    simp only [h1, h2, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_udiv, BitVec.toNat_udiv, BitVec.toNat_mul, hN, hD, hK, hdk,
      Nat.mod_eq_of_lt hov, Nat.mul_div_mul_left _ _ hn]

theorem tdiv_facts {n d : Int} (h0 : 0 ≤ n) (h1 : 0 ≤ d) (h : n ∣ d) :
    0 ≤ d.tdiv n ∧ d.tdiv n ≤ d ∧ d.toNat = n.toNat * (d.tdiv n).toNat ∧
      (d = 0 → d.tdiv n = 0) := by
  by_cases hn : n = 0
  · subst hn; obtain rfl : d = 0 := Int.zero_dvd.1 h; simp
  obtain ⟨k, rfl⟩ := h
  rw [Int.mul_tdiv_cancel_left _ hn]
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  have ha : 0 < a := by omega
  have hk : 0 ≤ k := by
    rcases Int.lt_or_le k 0 with hk | hk
    · have : (a : Int) * k < 0 := Int.mul_neg_of_pos_of_neg (by omega) hk
      omega
    · exact hk
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  refine ⟨hk, ?_, ?_, ?_⟩
  · have : b ≤ a * b := Nat.le_mul_of_pos_left b ha
    exact_mod_cast this
  · simp only [Int.toNat_natCast]; exact_mod_cast rfl
  · intro h; have : a * b = 0 := by exact_mod_cast h
    rcases Nat.mul_eq_zero.1 this with h | h <;> simp_all

theorem lit_toNat {w : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ w) :
    (BitVec.ofInt w z).toNat = z.toNat := by
  have := toNat_ofInt_lit h0 h1; omega


/-! ## Extension and most significant bits -/

theorem msb_of_lit (z : Int) (T : Ty) :
    msb_of (.mk (.bitVec z) T) = if 0 < z then log2 z else size_of_ty T - 1 := by
  rw [msb_of]
  by_cases h : 0 < z
  · simp [firstSome, h, HOrElse.hOrElse, OrElse.orElse, Option.orElse]
  · by_cases h' : z = 0
    · subst h'; simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse]
    · simp [firstSome, h, h', HOrElse.hOrElse, OrElse.orElse, Option.orElse]

theorem WT_extend {s k a T} :
    (Term.mk (.unop (.bvExtend s k) a) T).WT ↔
      ∃ m, BV a m ∧ 0 ≤ k ∧ T = .bitVector (m + k) := by
  rw [WT_unop]; simp only [Unop.WT, Ty.sort_eq, BV]; grind

theorem BV_extend_inv {s k a T n} (w : BV (.mk (.unop (.bvExtend s k) a) T) n) :
    ∃ m, BV a m ∧ 0 ≤ k ∧ n = m + k ∧ T = .bitVector n := by
  obtain ⟨m, wa, hk, hT⟩ := WT_extend.1 w.1
  have := w.2.1; simp only [Term.ty_mk] at this; subst this
  simp at hT; exact ⟨m, wa, hk, hT, by rw [hT]⟩

theorem eval_extend_inv {FS ρ k a T n m v} (w : BV (.mk (.unop (.bvExtend false k) a) T) n)
    (wa : BV a m) (e : eval FS ρ (.mk (.unop (.bvExtend false k) a) T) = some v) :
    ∃ X : BitVec m.toNat, eval FS ρ a = some (.bv _ X) ∧
      v = .bv (m.toNat + k.toNat) (X.setWidth _) := by
  rw [eval_unop w.1] at e
  obtain ⟨X, hX, e⟩ := evUnop_inv wa e
  simp [evUnop] at e
  exact ⟨X, hX, e.symm⟩

theorem eval_extend {FS ρ k a m X} (wa : BV a m) (hk : 0 ≤ k)
    (hX : eval FS ρ a = some (.bv m.toNat X)) :
    eval FS ρ (bv_extend.spec false k a) = some (.bv (m.toNat + k.toNat) (X.setWidth _)) := by
  rw [bv_extend.spec, eval_unop (WT_extend.2 ⟨m, wa, hk, by simp [wa.2.1]⟩), hX]
  simp [evUnop]

theorem BV_extend {FS k a m r} (hR : Refines FS (bv_extend.spec false k a) r) (wa : BV a m)
    (hk : 0 ≤ k) : BV r (m + k) :=
  BV_of_refines hR (WT_extend.2 ⟨m, wa, hk, by simp [wa.2.1]⟩) (by simp [bv_extend.spec, wa.2.1])
    (by have := wa.2.2; omega)


theorem Val.bv_toNat_eq {n m : Nat} {x : BitVec n} {y : BitVec m} (h : Val.bv n x = Val.bv m y) :
    n = m ∧ x.toNat = y.toNat := by
  cases h; exact ⟨rfl, rfl⟩


end ArithL
end Bvr
