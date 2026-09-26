import Bvr.Lemmas

/-! Lemmas for the proofs of the boolean rules. -/

namespace Bvr
namespace BoolL

open Classical

/-! ## Sorts of the values of operators -/

theorem unop_hasSort {FS : FloatSem} {op : Unop} {A T : Ty} {x v : Val}
    (w : op.WT A T) (hx : x.hasSort A) (e : evUnop FS op (some x) = some v) :
    v.hasSort T := by
  cases op <;> simp only [Unop.WT] at w
  case not_ => obtain ⟨rfl, rfl⟩ := w; cases x <;> simp [evUnop] at e; subst e; simp [Val.hasSort]
  case getPtrLoc | getPtrOfs =>
    obtain ⟨n, hn, rfl, rfl⟩ := w; cases x <;> simp [evUnop] at e <;> simp [Val.hasSort] at hx
    subst e; simp [Val.hasSort]; omega
  case bvOfBool n =>
    obtain ⟨hn, rfl, rfl⟩ := w; cases x <;> simp [evUnop] at e; subst e; simp [Val.hasSort]; omega
  case bvOfFloat n =>
    obtain ⟨hn, ⟨p, rfl⟩, rfl⟩ := w; cases x <;> simp [evUnop] at e; subst e
    simp [Val.hasSort]; omega
  case floatOfBv p =>
    obtain ⟨⟨n, hn, rfl⟩, rfl⟩ := w; cases x <;> simp [evUnop] at e; subst e; simp [Val.hasSort]
  case floatOfBvRaw p =>
    obtain ⟨rfl, rfl⟩ := w; cases x <;> simp [evUnop] at e; obtain ⟨_, rfl⟩ := e
    simp [Val.hasSort]
  case floatOfFloat p =>
    obtain ⟨⟨q, rfl⟩, rfl⟩ := w; cases x <;> simp [evUnop] at e; subst e; simp [Val.hasSort]
  case bvExtract i j =>
    obtain ⟨n, rfl, h1, h2, h3, rfl⟩ := w; cases x <;> simp [evUnop] at e; subst e
    simp [Val.hasSort]; omega
  case bvExtend s k =>
    obtain ⟨n, hn, rfl, hk, rfl⟩ := w; cases x <;> simp [evUnop] at e <;> simp [Val.hasSort] at hx
    subst e; simp [Val.hasSort]; omega
  case bvNot | neg =>
    obtain ⟨n, hn, rfl, rfl⟩ := w; cases x <;> simp [evUnop] at e <;> simp [Val.hasSort] at hx
    all_goals (try obtain ⟨_, e⟩ := e); subst_vars; simp [Val.hasSort]; omega
  case fAbs | fNeg | fSqrt | fRound =>
    obtain ⟨⟨q, rfl⟩, rfl⟩ := w; cases x <;> simp [evUnop] at e <;> simp [Val.hasSort] at hx
    subst e hx; simp [Val.hasSort]
  case fIs | fIsNeg | fIsPos =>
    obtain ⟨⟨q, rfl⟩, rfl⟩ := w; cases x <;> simp [evUnop] at e; subst e; simp [Val.hasSort]
theorem bvBin_eq_some {f : ∀ {n : Nat}, BitVec n → BitVec n → Option Val} {a b : Option Val}
    {v : Val} : bvBin f a b = some v ↔
      ∃ n x y, a = some (.bv n x) ∧ b = some (.bv n y) ∧ f x y = some v := by
  constructor
  · intro h
    unfold bvBin at h
    split at h
    · split at h
      · rename_i h'; subst h'; exact ⟨_, _, _, rfl, rfl, h⟩
      · cases h
    · cases h
  · rintro ⟨n, x, y, rfl, rfl, h⟩; simpa [bvBin] using h

theorem fBin_eq_some {f : (p : Prec) → FBits p → FBits p → Option Val} {a b : Option Val}
    {v : Val} : fBin f a b = some v ↔
      ∃ p x y, a = some (.float p x) ∧ b = some (.float p y) ∧ f p x y = some v := by
  constructor
  · intro h
    unfold fBin at h
    split at h
    · split at h
      · rename_i h'; subst h'; exact ⟨_, _, _, rfl, rfl, h⟩
      · cases h
    · cases h
  · rintro ⟨n, x, y, rfl, rfl, h⟩; simpa [fBin] using h

theorem binop_hasSort {FS : FloatSem} {op : Binop} {A B T : Ty} {x y : Option Val} {v : Val}
    (w : op.WT A B T) (hx : ∀ u, x = some u → u.hasSort A) (hy : ∀ u, y = some u → u.hasSort B)
    (e : evBinop FS op x y = some v) : v.hasSort T := by
  cases op <;> simp only [Binop.WT] at w
  case and_ =>
    obtain ⟨-, -, rfl⟩ := w
    simp only [evBinop, pand_eq_some] at e
    rcases e with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> simp [Val.hasSort]
  case or_ =>
    obtain ⟨-, -, rfl⟩ := w
    simp only [evBinop, por_eq_some] at e
    rcases e with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> simp [Val.hasSort]
  case eq =>
    obtain ⟨-, rfl⟩ := w
    cases x <;> cases y <;> simp [evBinop] at e; subst e; simp [Val.hasSort]
  case fEq | fLeq | fLt =>
    obtain ⟨-, -, rfl⟩ := w
    simp only [evBinop, fBin_eq_some] at e
    obtain ⟨_, _, _, _, _, e⟩ := e; cases e; simp [Val.hasSort]
  case fAdd | fSub | fMul | fDiv | fRem | fMin | fMax =>
    obtain ⟨⟨p, rfl⟩, -, rfl⟩ := w
    simp only [evBinop, fArith, fBin_eq_some] at e
    obtain ⟨q, _, _, h1, _, e⟩ := e; cases e
    have := hx _ h1; simp [Val.hasSort] at this; subst this; simp [Val.hasSort]
  case addOvf | subOvf | mulOvf | lt | leq =>
    obtain ⟨-, -, rfl⟩ := w
    simp only [evBinop, bvBin_eq_some] at e
    obtain ⟨_, _, _, _, _, e⟩ := e; cases e; simp [Val.hasSort]
  case bvConcat =>
    obtain ⟨n, m, hn, hm, rfl, rfl, rfl⟩ := w
    cases x with
    | none => simp [evBinop] at e
    | some x =>
    cases y with
    | none => cases x <;> simp [evBinop] at e
    | some y =>
    have h1 := hx _ rfl; have h2 := hy _ rfl
    cases x <;> cases y <;> simp [evBinop] at e <;> simp [Val.hasSort] at h1 h2
    subst e; simp [Val.hasSort]; omega
  case add | sub | mul =>
    obtain ⟨⟨n, hn, rfl⟩, -, rfl⟩ := w
    simp only [evBinop, checkedOp, bvBin_eq_some] at e
    obtain ⟨_, _, _, h1, _, e⟩ := e
    have := hx _ h1
    split at e
    · cases e
    · cases e; simpa [Val.hasSort] using this
  all_goals
    obtain ⟨⟨n, hn, rfl⟩, -, rfl⟩ := w
    simp only [evBinop, bvBin_eq_some] at e
    obtain ⟨_, _, _, h1, _, e⟩ := e
    have := hx _ h1
    cases e; simpa [Val.hasSort] using this
theorem evFma_eq_some {FS : FloatSem} {a b c : Option Val} {v : Val}
    (h : evFma FS a b c = some v) : ∃ p x y, a = some (.float p x) ∧ v = .float p y := by
  unfold evFma at h
  split at h
  · split at h
    · cases h; exact ⟨_, _, _, rfl, rfl⟩
    · cases h
  · cases h

/-! ## Evaluation respects sorts -/

mutual
theorem ev_hasSort {FS : FloatSem} :
    ∀ (t : Term) (ρ : Env) (v : Val), t.WT → ev FS ρ t = some v → v.hasSort t.ty.sort
  | .mk (.var x) T, ρ, v, _, e => by
      simp only [ev] at e
      split at e
      · split at e
        · cases e; assumption
        · cases e
      · cases e
  | .mk (.bool b) T, ρ, v, w, e => by
      simp only [Term.WT] at w; subst w; simp only [ev] at e; cases e; simp [Val.hasSort]
  | .mk (.float f) T, ρ, v, w, e => by
      simp only [Term.WT] at w; obtain ⟨rfl, _⟩ := w
      simp only [ev] at e; cases e; simp [FloatLit.sem, Val.hasSort]
  | .mk (.bitVec z) T, ρ, v, w, e => by
      obtain ⟨n, hn, hT, _, _⟩ := WT_bitVec.1 w
      simp only [ev] at e; cases e
      rcases hT with rfl | rfl <;> simp [Ty.width, size_of_ty, Val.hasSort] <;> omega
  | .mk (.ptr l o) T, ρ, v, w, e => by
      simp only [Term.WT] at w
      obtain ⟨n, hn, rfl, hl, ho, wl, wo⟩ := w
      simp only [ev] at e
      split at e
      · rename_i n' x m y hx hy
        split at e
        · cases e
          have := ev_hasSort l ρ _ wl hx
          rw [hl] at this
          simp only [Val.hasSort] at this
          simp [Val.hasSort]; omega
        · cases e
      · cases e
  | .mk (.seq l) T, ρ, v, w, e => by
      simp only [Term.WT] at w
      obtain ⟨E, rfl, wl⟩ := w
      simp only [ev] at e
      cases h : evList FS ρ l with
      | none => rw [h] at e; cases e
      | some vs =>
        rw [h] at e; cases e
        simpa [Val.hasSort, Ty.sort] using evList_hasSort l E ρ vs wl h
  | .mk (.unop op a) T, ρ, v, w, e => by
      obtain ⟨w1, wa⟩ := WT_unop.1 w
      simp only [ev] at e
      cases ha : ev FS ρ a with
      | none => rw [ha] at e; simp at e
      | some x =>
        rw [ha] at e
        exact unop_hasSort w1 (ev_hasSort a ρ x wa ha) e
  | .mk (.binop op a b) T, ρ, v, w, e => by
      obtain ⟨w1, wa, wb⟩ := WT_binop.1 w
      simp only [ev] at e
      exact binop_hasSort w1 (fun u h => ev_hasSort a ρ u wa h)
        (fun u h => ev_hasSort b ρ u wb h) e
  | .mk (.triop op g a b) T, ρ, v, w, e => by
      obtain ⟨w1, wg, wa, wb⟩ := WT_triop.1 w
      cases op with
      | ite =>
        simp only [Triop.WT] at w1
        obtain ⟨_, h2, h3⟩ := w1
        simp only [ev] at e
        split at e
        · simp only [Ty.sort_eq] at h3 ⊢; rw [h3]; exact ev_hasSort a ρ v wa e
        · simp only [Ty.sort_eq] at h2 h3 ⊢; rw [h3, ← h2]; exact ev_hasSort b ρ v wb e
        · cases e
      | fma =>
        simp only [Triop.WT] at w1
        obtain ⟨⟨p, hp⟩, h2, h3, h4⟩ := w1
        simp only [ev] at e
        cases hg : ev FS ρ g with
        | none => rw [hg] at e; simp [evFma] at e
        | some x =>
          have hx := ev_hasSort g ρ x wg hg
          rw [hg] at e
          simp only [Ty.sort_eq] at hp h4 hx ⊢
          simp only [Term.ty_mk, h4, hp]
          rw [hp] at hx
          obtain ⟨q, x', y, h1, rfl⟩ := evFma_eq_some e
          cases h1
          simpa [Val.hasSort] using hx
  | .mk (.nop op l) T, ρ, v, w, e => by
      simp only [Term.WT] at w
      obtain ⟨rfl, _⟩ := w
      cases op
      simp only [ev] at e
      cases h : evList FS ρ l with
      | none => rw [h] at e; cases e
      | some vs => rw [h] at e; cases e; simp [Val.hasSort]
  | .mk (.exists_ bs body) T, ρ, v, w, e => by
      simp only [Term.WT] at w
      obtain ⟨rfl, _⟩ := w
      simp only [ev] at e
      split at e
      · cases e; simp [Val.hasSort]
      · cases e
  | .mk (.extension x) T, ρ, v, _, e => by
      simp only [ev] at e
      split at e
      · split at e
        · cases e; assumption
        · cases e
      · cases e

theorem evList_hasSort {FS : FloatSem} :
    ∀ (l : List Term) (E : Ty) (ρ : Env) (vs : List Val), Term.WTList E l →
      evList FS ρ l = some vs → Val.hasSortList vs E.sort
  | [], E, ρ, vs, _, e => by simp only [evList] at e; cases e; simp [Val.hasSortList]
  | t :: ts, E, ρ, vs, w, e => by
      simp only [Term.WTList] at w
      obtain ⟨h1, wt, wts⟩ := w
      simp only [evList] at e
      split at e
      · rename_i x xs hx hxs
        cases e
        have := ev_hasSort t ρ x wt hx
        rw [h1] at this
        exact ⟨this, evList_hasSort ts E ρ xs wts hxs⟩
      · cases e
end

theorem eval_hasSort {FS ρ t v} (h : eval FS ρ t = some v) : v.hasSort t.ty.sort := by
  have w := eval_WT h
  rw [eval_eq_ev w] at h
  exact ev_hasSort t ρ v w h

theorem eval_bool_of_sort {FS ρ t v} (h : eval FS ρ t = some v) (hs : t.ty.sort = .bool) :
    ∃ b, v = .bool b := by
  have := eval_hasSort h
  rw [hs] at this
  cases v <;> simp_all [Val.hasSort]

theorem eval_bv_of_sort {FS ρ t v} {n : Int} (h : eval FS ρ t = some v)
    (hs : t.ty.sort = .bitVector n) : 0 < n ∧ ∃ x : BitVec n.toNat, v = .bv n.toNat x := by
  have := eval_hasSort h
  rw [hs] at this
  cases v <;> simp [Val.hasSort] at this
  rename_i m x
  obtain ⟨rfl, h2⟩ := this
  exact ⟨by omega, x, by simp⟩

end BoolL
end Bvr

namespace Bvr
namespace BoolL

open Classical

/-! ## Boolean nodes -/

theorem WT_or {a b t} : (Term.mk (.binop .or_ a b) t).WT ↔
    a.ty = .bool ∧ b.ty = .bool ∧ t = .bool ∧ a.WT ∧ b.WT := by
  simp [Term.WT, Binop.WT, and_assoc]

theorem WT_and' {a b t} : (Term.mk (.binop .and_ a b) t).WT ↔
    a.ty = .bool ∧ b.ty = .bool ∧ t = .bool ∧ a.WT ∧ b.WT := by
  simp [Term.WT, Binop.WT, and_assoc]

theorem WT_not {a t} : (Term.mk (.unop .not_ a) t).WT ↔ a.ty = .bool ∧ t = .bool ∧ a.WT := by
  simp [Term.WT, Unop.WT, and_assoc]

theorem WT_ite {g a b t} : (Term.mk (.triop .ite g a b) t).WT ↔
    g.ty = .bool ∧ b.ty = a.ty ∧ t = a.ty ∧ g.WT ∧ a.WT ∧ b.WT := by
  simp [Term.WT, Triop.WT, and_assoc]

theorem WT_eq {a b t} : (Term.mk (.binop .eq a b) t).WT ↔
    a.ty = b.ty ∧ t = .bool ∧ a.WT ∧ b.WT := by
  simp [Term.WT, Binop.WT, and_assoc]

theorem WT_cmp {op a b t} (hop : op = Binop.lt s ∨ op = Binop.leq s) :
    (Term.mk (.binop op a b) t).WT ↔
      (∃ n : Int, 0 < n ∧ a.ty = .bitVector n) ∧ b.ty = a.ty ∧ t = .bool ∧ a.WT ∧ b.WT := by
  rcases hop with rfl | rfl <;> simp [Term.WT, Binop.WT, and_assoc]

theorem evUnop_not_eq_some {FS a v} :
    evUnop FS .not_ a = some v ↔ ∃ b, a = some (.bool b) ∧ v = .bool (!b) := by
  constructor
  · intro h
    rcases a with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> simp [evUnop] at h
    exact ⟨_, rfl, h.symm⟩
  · rintro ⟨b, rfl, rfl⟩; rfl

theorem eval_not {FS ρ a t} (h : (Term.mk (.unop .not_ a) t).WT) :
    eval FS ρ (.mk (.unop .not_ a) t) = evUnop FS .not_ (eval FS ρ a) := eval_unop h

theorem evBinop_eq {FS a b} :
    evBinop FS .eq a b = (match a, b with
      | some x, some y => some (.bool (decide (x = y)))
      | _, _ => none) := by
  cases a <;> cases b <;> rfl

theorem eval_bool_val {FS ρ t v} (h : eval FS ρ t = some v) (ht : t.ty = .bool) :
    ∃ b, v = .bool b := eval_bool_of_sort h (by simpa using ht)

/-- A term whose evaluation is known to be a given boolean. -/
theorem Refines.of_bool {FS : FloatSem} {spec r : Term} (hr : r.WT) (hrt : r.ty = .bool)
    (hs : spec.WT → spec.ty = .bool)
    (h : ∀ ρ v, spec.WT → eval FS ρ spec = some v → eval FS ρ r = some v) :
    Refines FS spec r :=
  Refines.intro (fun w => ⟨hr, by simp [hrt, hs w]⟩) (fun ρ v w _ e => h ρ v w e)

/-- The result of a rule fired on the argument of `b_not`. -/
theorem Refines.not_of {FS : FloatSem} {O : Ops} (hO : O.Sound FS) {spec a : Term}
    (h : Refines FS spec (.mk (.unop .not_ a) .bool)) : Refines FS spec (O.b_not a) :=
  h.trans (hO.b_not a)

/-! ## Comparisons -/

/-- The integer that a bit-vector stands for, in a signedness. -/
def bz (s : Bool) {n : Nat} (x : BitVec n) : Int := if s then x.toInt else (x.toNat : Int)

theorem lt_val (s : Bool) {n : Nat} (x y : BitVec n) :
    (if s then x.slt y else x.ult y) = decide (bz s x < bz s y) := by
  cases s <;> simp [bz, BitVec.slt, BitVec.ult]

theorem leq_val (s : Bool) {n : Nat} (x y : BitVec n) :
    (if s then x.sle y else x.ule y) = decide (bz s x ≤ bz s y) := by
  cases s <;> simp [bz, BitVec.sle, BitVec.ule]

theorem bz_inj {s : Bool} {n : Nat} {x y : BitVec n} (h : bz s x = bz s y) : x = y := by
  cases s <;> simp [bz] at h
  · exact BitVec.eq_of_toNat_eq (by omega)
  · exact BitVec.eq_of_toInt_eq h

theorem equal_iff {a b : Term} : equal a b = true ↔ a = b := by simp [equal]

end BoolL
end Bvr
