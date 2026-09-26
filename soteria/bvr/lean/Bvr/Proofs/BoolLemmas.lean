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

namespace Bvr
namespace BoolL

open Classical

set_option linter.unusedSimpArgs false

/-! ## Rule helpers -/

/-- Clean up the hypothesis `h : rule = some res` after the rule's match was split. -/
macro "bool_fire" h:ident : tactic => `(tactic| (
  simp only [Option.some.injEq, reduceCtorEq, Option.ite_none_right_eq_some, equal_iff] at $h:ident <;>
  first
    | subst $h:ident
    | (obtain ⟨he, hr⟩ := $h:ident; subst hr
       try simp only [equal_iff, Bool.and_eq_true, decide_eq_true_eq] at he
       try obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
       try obtain ⟨rfl, rfl⟩ := he
       try subst he)) <;>
  (try simp only [equal_iff] at *) <;> try subst_vars)

/-- Split a hypothesis `h : alt1 <|> alt2 <|> ... = some res` into one goal per alternative. -/
macro "bool_alts" h:ident : tactic => `(tactic| repeat'
  (have h' := orElse_eq_some $h:ident; clear $h:ident; rcases h' with $h:ident | $h:ident))

/-- The syntactic part of a boolean rule. -/
macro "bool_syn" : tactic => `(tactic| (
  simp only [b_and.spec, b_or.spec, b_not.spec, WT_and', WT_or, WT_not, WT_ite, Term.ty_mk,
    v_true_WT, v_false_WT, v_true_ty, v_false_ty] at * <;> grind))

/-- The end of the semantic part of a boolean rule. -/
macro "bool_fin" : tactic => `(tactic| (
  simp only [evBinop, pand_eq_some, por_eq_some, evUnop_not_eq_some, eval_v_true,
    eval_v_false] at * <;> grind))

theorem pand_comm (a b : Option Val) : pand a b = pand b a := by
  apply Option.ext; intro v; simp only [pand_eq_some]; grind

theorem por_comm (a b : Option Val) : por a b = por b a := by
  apply Option.ext; intro v; simp only [por_eq_some]; grind

/-- `not (lt s a b)` is `leq s b a`, and `not (leq s a b)` is `lt s b a`. -/
theorem Refines.not_cmp {FS : FloatSem} {s : Bool} {a b : Term} {op op' : Binop}
    (hop : (op = .lt s ∧ op' = .leq s) ∨ (op = .leq s ∧ op' = .lt s)) {t : Ty} :
    Refines FS (.mk (.unop .not_ (.mk (.binop op a b) t)) .bool) (.mk (.binop op' b a) .bool) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · have ⟨h1, _, w1⟩ := WT_not.1 w
    simp only [Term.ty_mk] at h1; subst h1
    have hc : op = .lt s ∨ op = .leq s := by grind
    have hc' : op' = .lt s ∨ op' = .leq s := by grind
    obtain ⟨⟨n, hn, h2⟩, h3, -, wa, wb⟩ := (WT_cmp hc).1 w1
    refine ⟨(WT_cmp hc').2 ⟨⟨n, hn, by rw [h3, h2]⟩, h3.symm, rfl, wb, wa⟩, rfl⟩
  · have ⟨_, _, w1⟩ := WT_not.1 w
    rw [eval_unop w, eval_binop w1] at e
    rw [eval_binop w']
    rw [evUnop_not_eq_some] at e
    obtain ⟨c, e, rfl⟩ := e
    rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      simp only [evBinop] at e ⊢
      rw [bvBin_eq_some] at e ⊢
      obtain ⟨n, x, y, hx, hy, e⟩ := e
      refine ⟨n, y, x, hy, hx, ?_⟩
      simp only [lt_val, leq_val, Option.some.injEq, Val.bool.injEq] at e ⊢
      subst e; by_cases hh : bz s x < bz s y <;> by_cases hh2 : bz s x ≤ bz s y <;> simp [hh, hh2] <;> omega

/-- De Morgan, with the children of the result refined further. -/
theorem Refines.not_andor {FS : FloatSem} {op op' : Binop} {a b a' b' : Term} {t : Ty}
    (hop : (op = .or_ ∧ op' = .and_) ∨ (op = .and_ ∧ op' = .or_))
    (ha : Refines FS (.mk (.unop .not_ a) .bool) a')
    (hb : Refines FS (.mk (.unop .not_ b) .bool) b') :
    Refines FS (.mk (.unop .not_ (.mk (.binop op a b) t)) .bool) (.mk (.binop op' a' b') .bool) := by
  refine Refines.trans (b := .mk (.binop op' (.mk (.unop .not_ a) .bool)
    (.mk (.unop .not_ b) .bool)) .bool) ?_ (Refines.binop ha hb (fun _ => rfl))
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · have ⟨h1, _, w1⟩ := WT_not.1 w
    simp only [Term.ty_mk] at h1; subst h1
    rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨h2, h3, -, wa, wb⟩ := WT_or.1 w1
      exact ⟨WT_and'.2 ⟨rfl, rfl, rfl, WT_not.2 ⟨h2, rfl, wa⟩, WT_not.2 ⟨h3, rfl, wb⟩⟩, rfl⟩
    · obtain ⟨h2, h3, -, wa, wb⟩ := WT_and'.1 w1
      exact ⟨WT_or.2 ⟨rfl, rfl, rfl, WT_not.2 ⟨h2, rfl, wa⟩, WT_not.2 ⟨h3, rfl, wb⟩⟩, rfl⟩
  · have ⟨_, _, w1⟩ := WT_not.1 w
    have ⟨wa, wb⟩ : (Term.mk (.unop .not_ a) .bool).WT ∧ (Term.mk (.unop .not_ b) .bool).WT := by
      rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨(WT_and'.1 w').2.2.2.1, (WT_and'.1 w').2.2.2.2⟩
      · exact ⟨(WT_or.1 w').2.2.2.1, (WT_or.1 w').2.2.2.2⟩
    rw [eval_unop w, eval_binop w1] at e
    rw [eval_binop w', eval_unop wa, eval_unop wb]
    rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> bool_fin

theorem bitVec_one (y : BitVec 1) : y = 0#1 ∨ y = 1#1 := by revert y; decide

/-- `not (c = v)` on one bit is `(1 - c) = v`. -/
theorem Refines.not_eq_bit {FS : FloatSem} {c v : Term} {bv : Int} {t : Ty}
    (hc : c = .mk (.bitVec bv) (.bitVector 1)) (hop : a = c ∧ b = v ∨ a = v ∧ b = c) :
    Refines FS (.mk (.unop .not_ (.mk (.binop .eq a b) t)) .bool)
      (.mk (.binop .eq (mk_bv 1 (1 - bv)) v) .bool) := by
  subst hc
  refine Refines.intro (fun w => ?_) (fun ρ x w w' e => ?_)
  · have ⟨_, _, w1⟩ := WT_not.1 w
    have ⟨h1, _, wa, wb⟩ := WT_eq.1 w1
    refine ⟨WT_eq.2 ⟨?_, rfl, mk_masked_WT (by omega), ?_⟩, rfl⟩ <;>
      rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [mk_bv, mk_masked]
  · have ⟨_, _, w1⟩ := WT_not.1 w
    have ⟨h1, _, wa, wb⟩ := WT_eq.1 w1
    rw [eval_unop w, eval_binop w1] at e
    rw [eval_binop w', mk_bv, eval_mk_masked (by omega)]
    have wc : (Term.mk (.bitVec bv) (.bitVector 1)).WT := by
      rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hv : v.ty = .bitVector 1 := by
      rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
    obtain ⟨n, hn, hT, h0, h2⟩ := WT_bitVec.1 wc
    simp at hT; obtain rfl : n = 1 := by omega
    have hb : bv = 0 ∨ bv = 1 := by omega
    have ec := eval_bitVec' (FS := FS) (ρ := ρ) (n := 1) wc (Or.inl rfl)
    simp only [evUnop_not_eq_some] at e
    obtain ⟨c, e, rfl⟩ := e
    cases ev : eval FS ρ v with
    | none =>
      rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [ev, evBinop] at e
    | some y =>
      obtain ⟨-, y, rfl⟩ := eval_bv_of_sort ev (by simpa using hv)
      rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [ec, ev] at e <;>
        simp only [evBinop, Option.some.injEq, Val.bool.injEq, Val.bv.injEq] at e ⊢ <;>
        subst e <;> simp only [heq_eq_eq, true_and] <;>
        rcases hb with rfl | rfl <;> simp <;> rcases bitVec_one y with rfl | rfl <;> decide

theorem eval_bool_lit {FS ρ b t} (w : (Term.mk (.bool b) t).WT) :
    eval FS ρ (.mk (.bool b) t) = some (.bool b) := eval_bool (WT_bool.1 w)

theorem eval_ite_eq_some {FS ρ g a b t v} (h : (Term.mk (.triop .ite g a b) t).WT) :
    eval FS ρ (.mk (.triop .ite g a b) t) = some v ↔
      (eval FS ρ g = some (.bool true) ∧ eval FS ρ a = some v) ∨
        (eval FS ρ g = some (.bool false) ∧ eval FS ρ b = some v) := by
  rw [eval_ite h]; split <;> simp_all

/-- The syntactic part of an `ite` rule. -/
macro "bool_isyn" : tactic => `(tactic| (
  simp only [b_ite.spec, b_and.spec, b_or.spec, b_not.spec, WT_and', WT_or, WT_not, WT_ite,
    WT_bool, Term.ty_mk, ty_eq] at * <;> grind))

/-- `ite` on boolean branches, as a boolean formula. -/
theorem Refines.ite_bool {FS : FloatSem} {g a b r : Term} {t : Ty} (ha : a.WT → a.ty = .bool)
    (hr : ∀ ρ, g.ty = .bool → b.ty = .bool → g.WT → a.WT → b.WT →
      r.WT ∧ r.ty = .bool ∧ ∀ v, (eval FS ρ g = some (.bool true) ∧ eval FS ρ a = some v) ∨
        (eval FS ρ g = some (.bool false) ∧ eval FS ρ b = some v) → eval FS ρ r = some v) :
    Refines FS (.mk (.triop .ite g a b) t) r := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · obtain ⟨h1, h2, h3, wg, wa, wb⟩ := WT_ite.1 w
    obtain ⟨wr, hrt, -⟩ := hr ⟨fun _ => none, fun _ _ => none⟩ h1 (h2.trans (ha wa)) wg wa wb
    exact ⟨wr, by simp [hrt, h3, ha wa]⟩
  · obtain ⟨h1, h2, h3, wg, wa, wb⟩ := WT_ite.1 w
    rw [eval_ite_eq_some w] at e
    exact (hr ρ h1 (h2.trans (ha wa)) wg wa wb).2.2 v e

/-- An `ite` that refines another one, by their branch conditions. -/
theorem Refines.ite_ite {FS : FloatSem} {g a b g' a' b' : Term} {t : Ty}
    (hsyn : (Term.mk (.triop .ite g a b) t).WT →
      (Term.mk (.triop .ite g' a' b') a'.ty).WT ∧ a'.ty = t)
    (hsem : ∀ ρ v, (Term.mk (.triop .ite g a b) t).WT →
      (Term.mk (.triop .ite g' a' b') a'.ty).WT →
      (eval FS ρ g = some (.bool true) ∧ eval FS ρ a = some v) ∨
        (eval FS ρ g = some (.bool false) ∧ eval FS ρ b = some v) →
      (eval FS ρ g' = some (.bool true) ∧ eval FS ρ a' = some v) ∨
        (eval FS ρ g' = some (.bool false) ∧ eval FS ρ b' = some v)) :
    Refines FS (.mk (.triop .ite g a b) t) (.mk (.triop .ite g' a' b') a'.ty) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · have := hsyn w; exact ⟨this.1, by simp [this.2]⟩
  · rw [eval_ite_eq_some w] at e; rw [eval_ite_eq_some w']
    exact hsem ρ v w w' e

theorem is_bv_true {t : Ty} (h : is_bv t = true) : ∃ n, t = .bitVector n := by
  cases t <;> simp [is_bv, firstSome] at h ⊢

theorem two_pow_succ_int (n : Nat) : (2 : Int) ^ (n + 1) = 2 * 2 ^ n := by
  rw [Int.pow_succ]; omega

theorem bz_ofInt {s : Bool} {n : Nat} {c : Int} (hn : 0 < n) (h0 : 0 ≤ c) (h1 : c < 2 ^ n) :
    bz s (BitVec.ofInt n c) = bv_to_z s n c := by
  cases s
  · simp only [bz, bv_to_z, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofInt]
    rw [Int.toNat_of_nonneg (by omega)]
    push_cast
    exact Int.emod_eq_of_lt h0 h1
  · simp only [bz, bv_to_z, ↓reduceIte, BitVec.toInt_ofInt, signed_extract, zasr,
      Int.toNat_natCast]
    simp only [Int.toNat_zero, Int.pow_zero, Int.ediv_one]
    rw [Int.emod_eq_of_lt h0 h1]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have h2 := two_pow_succ_int m
    have h3 : (0 : Int) < 2 ^ m := two_pow_pos' m
    rw [Int.bmod_def]
    push_cast
    rw [Int.emod_eq_of_lt h0 h1]
    rw [h2] at h1 ⊢
    have : (2 * 2 ^ m + 1) / 2 = (2 : Int) ^ m := by omega
    rw [this]
    split <;> split <;> omega

theorem getD_firstSome_orElse {α} {o : Option α} {l : List (Option α)} {d : α} :
    (firstSome (o :: l)).getD d = match o with | some x => x | none => (firstSome l).getD d := by
  cases o <;> simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

theorem as_upper_bound_cases {v : Term} {r : Term × Bool × Term × Int}
    (h : as_upper_bound v = some r) :
    (∃ s a c T T', v = .mk (.binop (.lt s) a (.mk (.bitVec c) T)) T' ∧
      r = (a, s, v, bv_to_z s (size a) c - 1)) ∨
    (∃ s a c T T', v = .mk (.binop (.leq s) a (.mk (.bitVec c) T)) T' ∧
      r = (a, s, v, bv_to_z s (size a) c)) := by
  unfold as_upper_bound at h
  simp only [getD_firstSome_orElse, firstSome, Option.getD_none] at h
  split at h
  · left; simp at h; exact ⟨_, _, _, _, _, rfl, h.symm⟩
  · split at h
    · right; simp at h; exact ⟨_, _, _, _, _, rfl, h.symm⟩
    · simp at h

theorem as_lower_bound_cases {v : Term} {r : Term × Bool × Term × Int}
    (h : as_lower_bound v = some r) :
    (∃ s a c T T', v = .mk (.binop (.lt s) (.mk (.bitVec c) T) a) T' ∧
      r = (a, s, v, bv_to_z s (size a) c + 1)) ∨
    (∃ s a c T T', v = .mk (.binop (.leq s) (.mk (.bitVec c) T) a) T' ∧
      r = (a, s, v, bv_to_z s (size a) c)) := by
  unfold as_lower_bound at h
  simp only [getD_firstSome_orElse, firstSome, Option.getD_none] at h
  split at h
  · left; simp at h; exact ⟨_, _, _, _, _, rfl, h.symm⟩
  · split at h
    · right; simp at h; exact ⟨_, _, _, _, _, rfl, h.symm⟩
    · simp at h

/-- [v] is a boolean condition [p] on the (signed or unsigned) value of the
bit-vector [a], of width [n]. -/
def BoundOn (FS : FloatSem) (v a : Term) (n : Nat) (s : Bool) (p : Int → Bool) : Prop :=
  ∀ ρ, (∀ val, eval FS ρ v = some val →
      ∃ x : BitVec n, eval FS ρ a = some (.bv n x) ∧ val = .bool (p (bz s x))) ∧
    (∀ x : BitVec n, eval FS ρ a = some (.bv n x) → eval FS ρ v = some (.bool (p (bz s x))))

theorem BoundOn.congr {FS v a n s p q} (h : BoundOn FS v a n s p) (hpq : ∀ z, p z = q z) :
    BoundOn FS v a n s q := by
  intro ρ
  refine ⟨fun val e => ?_, fun x e => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := (h ρ).1 val e; exact ⟨x, hx, by rw [hpq]⟩
  · rw [← hpq]; exact (h ρ).2 x e

/-- The operator of a comparison, on integers. -/
def cmpZ (op : Binop) (x y : Int) : Bool :=
  match op with
  | .lt _ => decide (x < y)
  | _ => decide (x ≤ y)

theorem cmp_val {FS : FloatSem} {op : Binop} {s : Bool} (hop : op = .lt s ∨ op = .leq s)
    {n : Nat} (x y : BitVec n) :
    evBinop FS op (some (.bv n x)) (some (.bv n y)) = some (.bool (cmpZ op (bz s x) (bz s y))) := by
  rcases hop with rfl | rfl <;> simp [evBinop, bvBin, lt_val, leq_val, cmpZ]

theorem WT_lit_of_ty {c : Int} {T : Ty} {m : Int} (w : (Term.mk (.bitVec c) T).WT)
    (hT : T = .bitVector m) :
    ∃ n : Nat, 0 < n ∧ m = n ∧ 0 ≤ c ∧ c < 2 ^ n := by
  obtain ⟨n, hn, hT', h0, h1⟩ := WT_bitVec.1 w
  subst hT
  rcases hT' with h | h <;> simp at h
  exact ⟨n, hn, h, h0, h1⟩

/-- A comparison of [a] with a literal on the right. -/
theorem cmp_right_sem {FS : FloatSem} {op : Binop} {s : Bool} {a : Term} {c : Int} {T T' : Ty}
    (hop : op = .lt s ∨ op = .leq s)
    (w : (Term.mk (.binop op a (.mk (.bitVec c) T)) T').WT) :
    ∃ n : Nat, 0 < n ∧ a.ty = .bitVector n ∧ size a = n ∧
      BoundOn FS (.mk (.binop op a (.mk (.bitVec c) T)) T') a n s
        (fun z => cmpZ op z (bv_to_z s n c)) := by
  obtain ⟨⟨m, hm, ha⟩, hc, -, wa, wc⟩ := (WT_cmp hop).1 w
  simp only [Term.ty_mk] at hc
  obtain ⟨n, hn, rfl, h0, h1⟩ := WT_lit_of_ty wc (hc.trans ha)
  have ec : ∀ ρ, eval FS ρ (.mk (.bitVec c) T) = some (.bv n (BitVec.ofInt n c)) := fun ρ => by
    have := eval_bitVec' (FS := FS) (ρ := ρ) (n := n) wc (Or.inl (hc.trans ha))
    simpa using this
  refine ⟨n, hn, ha, by simp [ha], fun ρ => ⟨fun val e => ?_, fun x e => ?_⟩⟩
  · rw [eval_binop w, ec] at e
    cases hA : eval FS ρ a with
    | none => rw [hA] at e; rcases hop with rfl | rfl <;> simp [evBinop] at e
    | some A =>
      rw [hA] at e
      obtain ⟨-, x, rfl⟩ := eval_bv_of_sort hA (by simpa using ha)
      simp only [Int.toNat_natCast] at x e hA ⊢
      rw [cmp_val hop] at e
      refine ⟨x, rfl, ?_⟩
      simp only [Option.some.injEq] at e
      rw [← e, bz_ofInt hn h0 h1]
  · rw [eval_binop w, ec, e, cmp_val hop, bz_ofInt hn h0 h1]

/-- A comparison of [a] with a literal on the left. -/
theorem cmp_left_sem {FS : FloatSem} {op : Binop} {s : Bool} {a : Term} {c : Int} {T T' : Ty}
    (hop : op = .lt s ∨ op = .leq s)
    (w : (Term.mk (.binop op (.mk (.bitVec c) T) a) T').WT) :
    ∃ n : Nat, 0 < n ∧ a.ty = .bitVector n ∧ size a = n ∧
      BoundOn FS (.mk (.binop op (.mk (.bitVec c) T) a) T') a n s
        (fun z => cmpZ op (bv_to_z s n c) z) := by
  obtain ⟨⟨m, hm, hT⟩, hc, -, wc, wa⟩ := (WT_cmp hop).1 w
  simp only [Term.ty_mk] at hc hT
  obtain ⟨n, hn, rfl, h0, h1⟩ := WT_lit_of_ty wc hT
  have ha : a.ty = .bitVector n := hc.trans hT
  have ec : ∀ ρ, eval FS ρ (.mk (.bitVec c) T) = some (.bv n (BitVec.ofInt n c)) := fun ρ => by
    have := eval_bitVec' (FS := FS) (ρ := ρ) (n := n) wc (Or.inl hT)
    simpa using this
  refine ⟨n, hn, ha, by simp [ha], fun ρ => ⟨fun val e => ?_, fun x e => ?_⟩⟩
  · rw [eval_binop w, ec] at e
    cases hA : eval FS ρ a with
    | none => rw [hA] at e; rcases hop with rfl | rfl <;> simp [evBinop] at e
    | some A =>
      rw [hA] at e
      obtain ⟨-, x, rfl⟩ := eval_bv_of_sort hA (by simpa using ha)
      simp only [Int.toNat_natCast] at x e hA ⊢
      rw [cmp_val hop] at e
      refine ⟨x, rfl, ?_⟩
      simp only [Option.some.injEq] at e
      rw [← e, bz_ofInt hn h0 h1]
  · rw [eval_binop w, ec, e, cmp_val hop, bz_ofInt hn h0 h1]

theorem upper_bound_sem {FS : FloatSem} {v a w : Term} {s : Bool} {u : Int}
    (h : as_upper_bound v = some (a, s, w, u)) (wv : v.WT) :
    w = v ∧ ∃ n : Nat, 0 < n ∧ a.ty = .bitVector n ∧ BoundOn FS v a n s (fun z => decide (z ≤ u)) := by
  rcases as_upper_bound_cases h with ⟨s', a', c, T, T', rfl, hr⟩ | ⟨s', a', c, T, T', rfl, hr⟩ <;>
    simp only [Prod.mk.injEq] at hr <;> obtain ⟨rfl, rfl, rfl, rfl⟩ := hr <;> refine ⟨rfl, ?_⟩
  · obtain ⟨n, hn, ha, hs, hb⟩ := cmp_right_sem (FS := FS) (Or.inl rfl) wv
    refine ⟨n, hn, ha, hb.congr fun z => ?_⟩
    simp only [cmpZ, hs]; simp only [decide_eq_decide]; omega
  · obtain ⟨n, hn, ha, hs, hb⟩ := cmp_right_sem (FS := FS) (Or.inr rfl) wv
    exact ⟨n, hn, ha, hb.congr fun z => by simp [cmpZ, ha]⟩

theorem lower_bound_sem {FS : FloatSem} {v a w : Term} {s : Bool} {l : Int}
    (h : as_lower_bound v = some (a, s, w, l)) (wv : v.WT) :
    w = v ∧ ∃ n : Nat, 0 < n ∧ a.ty = .bitVector n ∧ BoundOn FS v a n s (fun z => decide (l ≤ z)) := by
  rcases as_lower_bound_cases h with ⟨s', a', c, T, T', rfl, hr⟩ | ⟨s', a', c, T, T', rfl, hr⟩ <;>
    simp only [Prod.mk.injEq] at hr <;> obtain ⟨rfl, rfl, rfl, rfl⟩ := hr <;> refine ⟨rfl, ?_⟩
  · obtain ⟨n, hn, ha, hs, hb⟩ := cmp_left_sem (FS := FS) (Or.inl rfl) wv
    refine ⟨n, hn, ha, hb.congr fun z => ?_⟩
    simp only [cmpZ, hs]; simp only [decide_eq_decide]; omega
  · obtain ⟨n, hn, ha, hs, hb⟩ := cmp_left_sem (FS := FS) (Or.inr rfl) wv
    exact ⟨n, hn, ha, hb.congr fun z => by simp [cmpZ, ha]⟩

/-! ### Combining two bounds on the same bit-vector -/

section
variable {FS : FloatSem} {ρ : Env} {v1 v2 a : Term} {n : Nat} {s : Bool} {p1 p2 : Int → Bool}

theorem pand_keep_left (hb1 : BoundOn FS v1 a n s p1) (hb2 : BoundOn FS v2 a n s p2)
    (himp : ∀ z, p1 z = true → p2 z = true) {v : Val}
    (e : pand (eval FS ρ v1) (eval FS ρ v2) = some v) : eval FS ρ v1 = some v := by
  rw [pand_eq_some] at e
  rcases e with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, -, rfl⟩
  · exact h
  · obtain ⟨x, hx, hv⟩ := (hb2 ρ).1 _ h
    rw [(hb1 ρ).2 x hx]
    cases h1 : p1 (bz s x)
    · rfl
    · simp [himp _ h1] at hv
  · exact h

theorem por_keep_left (hb1 : BoundOn FS v1 a n s p1) (hb2 : BoundOn FS v2 a n s p2)
    (himp : ∀ z, p2 z = true → p1 z = true) {v : Val}
    (e : por (eval FS ρ v1) (eval FS ρ v2) = some v) : eval FS ρ v1 = some v := by
  rw [por_eq_some] at e
  rcases e with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, -, rfl⟩
  · exact h
  · obtain ⟨x, hx, hv⟩ := (hb2 ρ).1 _ h
    rw [(hb1 ρ).2 x hx]
    cases h2 : p2 (bz s x)
    · simp [h2] at hv
    · simp [himp _ h2]
  · exact h

theorem por_all (hb1 : BoundOn FS v1 a n s p1) (hb2 : BoundOn FS v2 a n s p2)
    (hall : ∀ z, p1 z = true ∨ p2 z = true) {v : Val}
    (e : por (eval FS ρ v1) (eval FS ρ v2) = some v) : v = .bool true := by
  rw [por_eq_some] at e
  rcases e with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h1, h2, rfl⟩
  · rfl
  · rfl
  · obtain ⟨x, hx, hv1⟩ := (hb1 ρ).1 _ h1
    have hv2 := (hb2 ρ).2 x hx
    rw [h2] at hv2
    simp only [Val.bool.injEq, Option.some.injEq] at hv1 hv2
    rcases hall (bz s x) with h | h <;> simp_all

end



theorem pand_comm' (a b : Option Val) : pand a b = pand b a := by
  apply Option.ext; intro v; simp only [pand_eq_some]; grind

theorem por_comm' (a b : Option Val) : por a b = por b a := by
  apply Option.ext; intro v; simp only [por_eq_some]; grind

theorem width_unique {a : Term} {n m : Nat} (h1 : a.ty = .bitVector n) (h2 : a.ty = .bitVector m) :
    n = m := by
  rw [h1] at h2; simp at h2; omega

/-- Two bounds of the same kind on the same bit-vector, with the conditions they stand for. -/
theorem bounds_sem {FS : FloatSem} {v1 v2 a : Term} {s : Bool} {p1 p2 : Int → Bool}
    (hb1 : v1.WT → ∃ n : Nat, 0 < n ∧ a.ty = .bitVector n ∧ BoundOn FS v1 a n s p1)
    (hb2 : v2.WT → ∃ n : Nat, 0 < n ∧ a.ty = .bitVector n ∧ BoundOn FS v2 a n s p2)
    (w1 : v1.WT) (w2 : v2.WT) :
    ∃ n : Nat, BoundOn FS v1 a n s p1 ∧ BoundOn FS v2 a n s p2 := by
  obtain ⟨n, -, ha, b1⟩ := hb1 w1
  obtain ⟨m, -, ha', b2⟩ := hb2 w2
  obtain rfl := width_unique ha ha'
  exact ⟨n, b1, b2⟩

/-- A conjunction of two bounds, one of which implies the other. -/
theorem Refines.and_bounds {FS : FloatSem} {v1 v2 a : Term} {s : Bool} {p1 p2 : Int → Bool}
    (c : Bool)
    (hb1 : v1.WT → ∃ n : Nat, 0 < n ∧ a.ty = .bitVector n ∧ BoundOn FS v1 a n s p1)
    (hb2 : v2.WT → ∃ n : Nat, 0 < n ∧ a.ty = .bitVector n ∧ BoundOn FS v2 a n s p2)
    (h12 : c = true → ∀ z, p1 z = true → p2 z = true)
    (h21 : c = false → ∀ z, p2 z = true → p1 z = true) :
    Refines FS (b_and.spec v1 v2) (if c then v1 else v2) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · obtain ⟨h1, h2, -, w1, w2⟩ := WT_and'.1 w; split <;> simp_all [b_and.spec]
  · simp only [b_and.spec] at w e
    obtain ⟨-, -, -, w1, w2⟩ := WT_and'.1 w
    obtain ⟨n, b1, b2⟩ := bounds_sem hb1 hb2 w1 w2
    rw [eval_binop w] at e; simp only [evBinop] at e
    cases c
    · rw [pand_comm'] at e; exact pand_keep_left b2 b1 (h21 rfl) e
    · exact pand_keep_left b1 b2 (h12 rfl) e

/-- A disjunction of two bounds, one of which implies the other. -/
theorem Refines.or_bounds {FS : FloatSem} {v1 v2 a : Term} {s : Bool} {p1 p2 : Int → Bool}
    (c : Bool)
    (hb1 : v1.WT → ∃ n : Nat, 0 < n ∧ a.ty = .bitVector n ∧ BoundOn FS v1 a n s p1)
    (hb2 : v2.WT → ∃ n : Nat, 0 < n ∧ a.ty = .bitVector n ∧ BoundOn FS v2 a n s p2)
    (h21 : c = true → ∀ z, p2 z = true → p1 z = true)
    (h12 : c = false → ∀ z, p1 z = true → p2 z = true) :
    Refines FS (b_or.spec v1 v2) (if c then v1 else v2) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · obtain ⟨h1, h2, -, w1, w2⟩ := WT_or.1 w; split <;> simp_all [b_or.spec]
  · simp only [b_or.spec] at w e
    obtain ⟨-, -, -, w1, w2⟩ := WT_or.1 w
    obtain ⟨n, b1, b2⟩ := bounds_sem hb1 hb2 w1 w2
    rw [eval_binop w] at e; simp only [evBinop] at e
    cases c
    · rw [por_comm'] at e; exact por_keep_left b2 b1 (h12 rfl) e
    · exact por_keep_left b1 b2 (h21 rfl) e

theorem combine_upper_bounds_eq {v1 v2 a1 a2 w1 w2 : Term} {s1 s2 k : Bool} {u1 u2 : Int}
    (h1 : as_upper_bound v1 = some (a1, s1, w1, u1))
    (h2 : as_upper_bound v2 = some (a2, s2, w2, u2)) :
    combine_upper_bounds k v1 v2 = if decide (u1 ≤ u2) = k then v1 else v2 := by
  simp [combine_upper_bounds, getD_firstSome_orElse, firstSome, h1, h2]

theorem combine_lower_bounds_eq {v1 v2 a1 a2 w1 w2 : Term} {s1 s2 k : Bool} {l1 l2 : Int}
    (h1 : as_lower_bound v1 = some (a1, s1, w1, l1))
    (h2 : as_lower_bound v2 = some (a2, s2, w2, l2)) :
    combine_lower_bounds k v1 v2 = if decide (l1 ≥ l2) = k then v1 else v2 := by
  simp [combine_lower_bounds, getD_firstSome_orElse, firstSome, h1, h2]

theorem Refines.and_upper_bounds {FS : FloatSem} {v1 v2 a w1 w2 : Term} {s : Bool} {u1 u2 : Int}
    (h1 : as_upper_bound v1 = some (a, s, w1, u1))
    (h2 : as_upper_bound v2 = some (a, s, w2, u2)) :
    Refines FS (b_and.spec v1 v2) (combine_upper_bounds true v1 v2) := by
  rw [combine_upper_bounds_eq h1 h2]
  exact Refines.and_bounds _ (fun w => (upper_bound_sem h1 w).2) (fun w => (upper_bound_sem h2 w).2)
    (fun hc z => by simp at hc ⊢; omega) (fun hc z => by simp at hc ⊢; omega)

theorem Refines.or_upper_bounds {FS : FloatSem} {v1 v2 a w1 w2 : Term} {s : Bool} {u1 u2 : Int}
    (h1 : as_upper_bound v1 = some (a, s, w1, u1))
    (h2 : as_upper_bound v2 = some (a, s, w2, u2)) :
    Refines FS (b_or.spec v1 v2) (combine_upper_bounds false v1 v2) := by
  have : combine_upper_bounds false v1 v2 = if decide (u2 < u1) = true then v1 else v2 := by
    rw [combine_upper_bounds_eq h1 h2]; by_cases h : u1 ≤ u2 <;> simp [h] <;> omega
  rw [this]
  exact Refines.or_bounds _ (fun w => (upper_bound_sem h1 w).2) (fun w => (upper_bound_sem h2 w).2)
    (fun hc z => by simp at hc ⊢; omega) (fun hc z => by simp at hc ⊢; omega)

theorem Refines.and_lower_bounds {FS : FloatSem} {v1 v2 a w1 w2 : Term} {s : Bool} {l1 l2 : Int}
    (h1 : as_lower_bound v1 = some (a, s, w1, l1))
    (h2 : as_lower_bound v2 = some (a, s, w2, l2)) :
    Refines FS (b_and.spec v1 v2) (combine_lower_bounds true v1 v2) := by
  rw [combine_lower_bounds_eq h1 h2]
  exact Refines.and_bounds _ (fun w => (lower_bound_sem h1 w).2) (fun w => (lower_bound_sem h2 w).2)
    (fun hc z => by simp at hc ⊢; omega) (fun hc z => by simp at hc ⊢; omega)

theorem Refines.or_lower_bounds {FS : FloatSem} {v1 v2 a w1 w2 : Term} {s : Bool} {l1 l2 : Int}
    (h1 : as_lower_bound v1 = some (a, s, w1, l1))
    (h2 : as_lower_bound v2 = some (a, s, w2, l2)) :
    Refines FS (b_or.spec v1 v2) (combine_lower_bounds false v1 v2) := by
  have : combine_lower_bounds false v1 v2 = if decide (l1 < l2) = true then v1 else v2 := by
    rw [combine_lower_bounds_eq h1 h2]; by_cases h : l1 < l2 <;> simp [h] <;> omega
  rw [this]
  exact Refines.or_bounds _ (fun w => (lower_bound_sem h1 w).2) (fun w => (lower_bound_sem h2 w).2)
    (fun hc z => by simp at hc ⊢; omega) (fun hc z => by simp at hc ⊢; omega)

theorem as_upper_bound_lt {s : Bool} {a : Term} {c : Int} {T T' : Ty} :
    as_upper_bound (.mk (.binop (.lt s) a (.mk (.bitVec c) T)) T') =
      some (a, s, .mk (.binop (.lt s) a (.mk (.bitVec c) T)) T', bv_to_z s (size a) c - 1) := by
  simp [as_upper_bound, firstSome]

theorem as_upper_bound_leq {s : Bool} {a : Term} {c : Int} {T T' : Ty} :
    as_upper_bound (.mk (.binop (.leq s) a (.mk (.bitVec c) T)) T') =
      some (a, s, .mk (.binop (.leq s) a (.mk (.bitVec c) T)) T', bv_to_z s (size a) c) := by
  simp [as_upper_bound, firstSome]

theorem as_lower_bound_lt {s : Bool} {a : Term} {c : Int} {T T' : Ty} :
    as_lower_bound (.mk (.binop (.lt s) (.mk (.bitVec c) T) a) T') =
      some (a, s, .mk (.binop (.lt s) (.mk (.bitVec c) T) a) T', bv_to_z s (size a) c + 1) := by
  simp [as_lower_bound, firstSome]

theorem as_lower_bound_leq {s : Bool} {a : Term} {c : Int} {T T' : Ty} :
    as_lower_bound (.mk (.binop (.leq s) (.mk (.bitVec c) T) a) T') =
      some (a, s, .mk (.binop (.leq s) (.mk (.bitVec c) T) a) T', bv_to_z s (size a) c) := by
  simp [as_lower_bound, firstSome]

theorem complementary_bounds_true {ub lb : Term} (h : complementary_bounds ub lb = true) :
    ∃ a s w1 u w2 l, as_upper_bound ub = some (a, s, w1, u) ∧
      as_lower_bound lb = some (a, s, w2, l) ∧ l ≤ u + 1 := by
  unfold complementary_bounds at h
  simp only [getD_firstSome_orElse, firstSome] at h
  split at h
  · rename_i a1 s1 w1 u a2 s2 w2 l h1 h2
    simp [equal_iff] at h
    obtain ⟨rfl, rfl, hl⟩ := h
    exact ⟨_, _, _, _, _, _, h1, h2, hl⟩
  · simp at h

/-- A disjunction of two bounds that cover every value. -/
theorem Refines.or_bounds_true {FS : FloatSem} {v1 v2 a : Term} {s : Bool} {p1 p2 : Int → Bool}
    (hb1 : v1.WT → ∃ n : Nat, 0 < n ∧ a.ty = .bitVector n ∧ BoundOn FS v1 a n s p1)
    (hb2 : v2.WT → ∃ n : Nat, 0 < n ∧ a.ty = .bitVector n ∧ BoundOn FS v2 a n s p2)
    (hall : ∀ z, p1 z = true ∨ p2 z = true) :
    Refines FS (b_or.spec v1 v2) v_true := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · simp [b_or.spec]
  · simp only [b_or.spec] at w e
    obtain ⟨-, -, -, w1, w2⟩ := WT_or.1 w
    obtain ⟨n, b1, b2⟩ := bounds_sem hb1 hb2 w1 w2
    rw [eval_binop w] at e; simp only [evBinop] at e
    rw [por_all b1 b2 hall e]; simp

theorem Refines.or_complementary {FS : FloatSem} {v1 v2 : Term}
    (h : (complementary_bounds v1 v2 || complementary_bounds v2 v1) = true) :
    Refines FS (b_or.spec v1 v2) v_true := by
  simp only [Bool.or_eq_true] at h
  rcases h with h | h <;> obtain ⟨a, s, w1, u, w2, l, h1, h2, hl⟩ := complementary_bounds_true h
  · exact Refines.or_bounds_true (p1 := fun z => decide (z ≤ u)) (p2 := fun z => decide (l ≤ z))
      (fun w => (upper_bound_sem h1 w).2)
      (fun w => (lower_bound_sem h2 w).2) (fun z => by simp; omega)
  · exact Refines.or_bounds_true (p1 := fun z => decide (l ≤ z)) (p2 := fun z => decide (z ≤ u))
      (fun w => (lower_bound_sem h2 w).2)
      (fun w => (upper_bound_sem h1 w).2) (fun z => by simp; omega)

/-- The bound that [a = k] implies. -/
def BoundImplied (boundv a : Term) (k : Int) : Prop :=
  (∃ s w u, as_upper_bound boundv = some (a, s, w, u) ∧ bv_to_z s (size a) k ≤ u) ∨
    (∃ s w l, as_lower_bound boundv = some (a, s, w, l) ∧ l ≤ bv_to_z s (size a) k)

set_option hygiene false in
/-- Read a [BoundImplied] off the boolean that [bound_implied_by_eq] computes. -/
macro "bool_bimp" : tactic => `(tactic| (
  simp [firstSome] at h
  rcases h with h | h
  · left
    cases hu : as_upper_bound boundv with
    | none => simp [hu] at h
    | some r =>
      obtain ⟨ba, s, w, u⟩ := r
      simp [hu, equal_iff] at h
      obtain ⟨rfl, h⟩ := h
      exact ⟨s, w, u, rfl, by first | exact h | exact of_decide_eq_true h⟩
  · right
    cases hu : as_lower_bound boundv with
    | none => simp [hu] at h
    | some r =>
      obtain ⟨ba, s, w, l⟩ := r
      simp [hu, equal_iff] at h
      obtain ⟨rfl, h⟩ := h
      exact ⟨s, w, l, rfl, by first | exact h | exact of_decide_eq_true h⟩))

theorem bound_implied_by_eq_true {boundv eqv : Term} (h : bound_implied_by_eq boundv eqv = true) :
    ∃ a k Tk Te, (eqv = .mk (.binop .eq a (.mk (.bitVec k) Tk)) Te ∨
      eqv = .mk (.binop .eq (.mk (.bitVec k) Tk) a) Te) ∧ BoundImplied boundv a k := by
  unfold bound_implied_by_eq at h
  split at h
  · refine ⟨_, _, _, _, Or.inl rfl, ?_⟩
    bool_bimp
  · split at h
    · refine ⟨_, _, _, _, Or.inr rfl, ?_⟩
      bool_bimp
    · simp [firstSome] at h

theorem BoundImplied.sem {FS : FloatSem} {v a : Term} {k : Int} (h : BoundImplied v a k)
    (w : v.WT) : ∃ (n : Nat) (s : Bool) (p : Int → Bool), a.ty = .bitVector n ∧
      BoundOn FS v a n s p ∧ p (bv_to_z s n k) = true := by
  rcases h with ⟨s, w', u, h1, hk⟩ | ⟨s, w', l, h1, hk⟩
  · obtain ⟨-, n, -, ha, hb⟩ := upper_bound_sem (FS := FS) h1 w
    refine ⟨n, s, _, ha, hb, ?_⟩
    simp only [size_eq, ha, size_of_ty_bitVector] at hk; simpa using hk
  · obtain ⟨-, n, -, ha, hb⟩ := lower_bound_sem (FS := FS) h1 w
    refine ⟨n, s, _, ha, hb, ?_⟩
    simp only [size_eq, ha, size_of_ty_bitVector] at hk; simpa using hk

theorem eval_eq_true {FS ρ a b t} (w : (Term.mk (.binop .eq a b) t).WT)
    (e : eval FS ρ (.mk (.binop .eq a b) t) = some (.bool true)) :
    ∃ x, eval FS ρ a = some x ∧ eval FS ρ b = some x := by
  rw [eval_binop w, evBinop_eq] at e
  split at e
  · simp at e; subst e; exact ⟨_, by assumption, by assumption⟩
  · simp at e

theorem Refines.or_bound_eq {FS : FloatSem} {v1 v2 : Term}
    (h : bound_implied_by_eq v1 v2 = true) : Refines FS (b_or.spec v1 v2) v1 := by
  obtain ⟨a, k, Tk, Te, heq, hb⟩ := bound_implied_by_eq_true h
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · obtain ⟨h1, -, -, w1, -⟩ := WT_or.1 w; simp_all [b_or.spec]
  · simp only [b_or.spec] at w e
    obtain ⟨-, -, -, w1, w2⟩ := WT_or.1 w
    obtain ⟨n, s, p, ha, B, hp⟩ := hb.sem (FS := FS) w1
    have hK : ∃ n' : Nat, 0 < n' ∧ (n : Int) = n' ∧ 0 ≤ k ∧ k < 2 ^ n' ∧
        ∀ ρ, eval FS ρ (.mk (.bitVec k) Tk) = some (.bv n (BitVec.ofInt n k)) := by
      have : (Term.mk (.bitVec k) Tk).WT ∧ Tk = a.ty := by
        rcases heq with rfl | rfl <;> obtain ⟨h1, -, wa, wb⟩ := WT_eq.1 w2
        · exact ⟨wb, h1.symm⟩
        · exact ⟨wa, h1⟩
      obtain ⟨n', hn', hn, h0, h1⟩ := WT_lit_of_ty this.1 (this.2.trans ha)
      refine ⟨n', hn', hn, h0, h1, fun ρ => ?_⟩
      have := eval_bitVec' (FS := FS) (ρ := ρ) (n := n) this.1 (Or.inl (this.2.trans ha))
      simpa using this
    obtain ⟨n', hn', hnn, h0, h1, ek⟩ := hK
    obtain rfl : n = n' := by omega
    rw [eval_binop w] at e; simp only [evBinop, por_eq_some] at e
    rcases e with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, -, rfl⟩
    · exact h
    · have hx : eval FS ρ a = some (.bv n (BitVec.ofInt n k)) := by
        rcases heq with rfl | rfl <;> obtain ⟨x, hx1, hx2⟩ := eval_eq_true w2 h
        · rw [ek] at hx2; rw [hx1, hx2]
        · rw [ek] at hx1; rw [hx2, hx1]
      rw [(B ρ).2 _ hx, bz_ofInt hn' h0 h1, hp]
    · exact h

theorem Refines.or_comm {FS : FloatSem} {v1 v2 r : Term} (h : Refines FS (b_or.spec v2 v1) r) :
    Refines FS (b_or.spec v1 v2) r := by
  refine Refines.trans ?_ h
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨h1, h2, -, w1, w2⟩ := WT_or.1 w; exact ⟨WT_or.2 ⟨h2, h1, rfl, w2, w1⟩, rfl⟩
  · simp only [b_or.spec] at w w' e ⊢
    rw [eval_binop w] at e; rw [eval_binop w']
    simpa [evBinop, por_comm'] using e

theorem sure_neq_cases {a b : Term} (h : sure_neq a b = true) :
    a.ty ≠ b.ty ∨
    (∃ za zb Ta Tb, a = .mk (.bitVec za) Ta ∧ b = .mk (.bitVec zb) Tb ∧ za ≠ zb) ∨
    (∃ fa fb Ta Tb, a = .mk (.float fa) Ta ∧ b = .mk (.float fb) Tb ∧ fa ≠ fb) ∨
    (∃ ba bb Ta Tb, a = .mk (.bool ba) Ta ∧ b = .mk (.bool bb) Tb ∧ ba ≠ bb) ∨
    (∃ la oa lb ob Ta Tb, a = .mk (.ptr la oa) Ta ∧ b = .mk (.ptr lb ob) Tb ∧
      (sure_neq la lb = true ∨ sure_neq oa ob = true)) := by
  unfold sure_neq at h
  simp only [getD_firstSome_orElse, Bool.or_eq_true, Bool.not_eq_true', ty_eq] at h
  rcases h with h | h
  · left; exact of_decide_eq_false h
  right
  rcases a with ⟨ka, Ta⟩; rcases b with ⟨kb, Tb⟩
  cases ka <;> cases kb <;> simp [firstSome, f_equal] at h ⊢ <;>
    first | assumption | exact ⟨_, _, ⟨rfl, rfl⟩, _, _, ⟨rfl, rfl⟩, h⟩

theorem eval_ptr_eq_some {FS ρ l o T u} (e : eval FS ρ (.mk (.ptr l o) T) = some u) :
    ∃ n x y, u = .ptr n x y ∧ eval FS ρ l = some (.bv n x) ∧ eval FS ρ o = some (.bv n y) := by
  have w := eval_WT e
  have w' := w
  obtain ⟨_, _, _, _, _, wl, wo⟩ := w'
  rw [eval_eq_ev w] at e; rw [eval_eq_ev wl, eval_eq_ev wo]
  simp only [ev] at e
  split at e
  · split at e
    · rename_i h; subst h; cases e; exact ⟨_, _, _, rfl, by assumption, by assumption⟩
    · cases e
  · cases e

theorem sure_neq_sound_aux {FS : FloatSem} (k : Nat) : ∀ {a b : Term} {ρ : Env} {u : Val},
    sizeOf a < k → sure_neq a b = true →
    a.ty = b.ty → eval FS ρ a = some u → eval FS ρ b = some u → False := by
  induction k with
  | zero => intros; omega
  | succ k ih =>
    intro a b ρ u hk h ht ea eb
    rcases sure_neq_cases h with h | ⟨za, zb, Ta, Tb, rfl, rfl, hz⟩ |
      ⟨fa, fb, Ta, Tb, rfl, rfl, hf⟩ | ⟨ba, bb, Ta, Tb, rfl, rfl, hb⟩ |
      ⟨la, oa, lb, ob, Ta, Tb, rfl, rfl, hp⟩
    · exact h ht
    · simp only [Term.ty_mk] at ht; subst ht
      have wa := eval_WT ea; have wb := eval_WT eb
      obtain ⟨n, hn, hT, h0, h1⟩ := WT_bitVec.1 wa
      obtain ⟨n', hn', hT', h0', h1'⟩ := WT_bitVec.1 wb
      have : n' = n := by
        rcases hT with rfl | rfl <;> rcases hT' with h | h <;> simp at h <;> omega
      subst this
      rw [eval_bitVec' wa hT] at ea; rw [eval_bitVec' wb hT, ← ea] at eb
      simp only [Option.some.injEq, Val.bv.injEq, heq_eq_eq, true_and] at eb
      have := congrArg BitVec.toNat eb
      simp only [BitVec.toNat_ofInt] at this
      simp only [Int.toNat_natCast] at this; push_cast at this
      rw [Int.emod_eq_of_lt h0' h1', Int.emod_eq_of_lt h0 h1] at this
      exact hz (by omega)
    · have wa := eval_WT ea; have wb := eval_WT eb
      rw [eval_eq_ev wa, ev] at ea; rw [eval_eq_ev wb, ev, ← ea] at eb
      simp only [Term.WT] at wa wb
      rcases fa with ⟨p, x⟩; rcases fb with ⟨q, y⟩
      simp only [FloatLit.sem, FloatLit.val, Option.some.injEq, Val.float.injEq] at eb
      obtain ⟨rfl, eb⟩ := eb
      simp only [heq_eq_eq] at eb
      have := congrArg BitVec.toNat eb
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt wa.2, Nat.mod_eq_of_lt wb.2] at this
      exact hf (by simp at this ⊢; omega)
    · simp only [eval_bool (WT_bool.1 (eval_WT ea)), eval_bool (WT_bool.1 (eval_WT eb))] at ea eb
      rw [← ea] at eb; simp at eb; exact hb eb.symm
    · obtain ⟨n, x, y, rfl, hla, hoa⟩ := eval_ptr_eq_some ea
      obtain ⟨n', x', y', he, hlb, hob⟩ := eval_ptr_eq_some eb
      simp only [Val.ptr.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      obtain ⟨m, -, hTa, hla', hoa', -, -⟩ := eval_WT ea
      obtain ⟨m', -, hTb, hlb', hob', -, -⟩ := eval_WT eb
      simp only [Term.ty_mk] at ht; rw [hTa, hTb] at ht; simp only [Ty.pointer.injEq] at ht
      subst ht
      simp only [Ty.sort_eq] at *
      rcases hp with hp | hp
      · exact ih (by simp at hk; omega) hp (hla'.trans hlb'.symm) hla hlb
      · exact ih (by simp at hk; omega) hp (hoa'.trans hob'.symm) hoa hob

theorem sure_neq_sound {FS : FloatSem} {a b : Term} {ρ : Env} {u : Val} (h : sure_neq a b = true)
    (ht : a.ty = b.ty) (ea : eval FS ρ a = some u) (eb : eval FS ρ b = some u) : False :=
  sure_neq_sound_aux (sizeOf a + 1) (Nat.lt_succ_self _) h ht ea eb

theorem Refines.and_eq_neq {FS : FloatSem} {p1 q1 p2 q2 x y a : Term} {T1 T2 : Ty}
    (o1 : (p1 = a ∧ q1 = x) ∨ (p1 = x ∧ q1 = a)) (o2 : (p2 = a ∧ q2 = y) ∨ (p2 = y ∧ q2 = a))
    (hn : sure_neq x y = true) :
    Refines FS (b_and.spec (.mk (.binop .eq p1 q1) T1) (.mk (.binop .eq p2 q2) T2)) v_false := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · simp [b_and.spec]
  · simp only [b_and.spec] at w e
    obtain ⟨-, -, -, w1, w2⟩ := WT_and'.1 w
    obtain ⟨ht1, -, -, -⟩ := WT_eq.1 w1
    obtain ⟨ht2, -, -, -⟩ := WT_eq.1 w2
    rw [eval_binop w] at e; simp only [evBinop, pand_eq_some] at e
    rcases e with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨e1, e2, rfl⟩
    · simp
    · simp
    · exfalso
      have k1 : ∃ u, eval FS ρ a = some u ∧ eval FS ρ x = some u ∧ a.ty = x.ty := by
        obtain ⟨u, h1, h2⟩ := eval_eq_true w1 e1
        rcases o1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨u, h1, h2, ht1⟩
        · exact ⟨u, h2, h1, ht1.symm⟩
      have k2 : ∃ u, eval FS ρ a = some u ∧ eval FS ρ y = some u ∧ a.ty = y.ty := by
        obtain ⟨u, h1, h2⟩ := eval_eq_true w2 e2
        rcases o2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨u, h1, h2, ht2⟩
        · exact ⟨u, h2, h1, ht2.symm⟩
      obtain ⟨u, ha, hx, tx⟩ := k1
      obtain ⟨u', ha', hy, ty⟩ := k2
      rw [ha] at ha'; cases ha'
      exact sure_neq_sound hn (tx.symm.trans ty) hx hy

theorem eval_cmp_eq_some {FS ρ op s a b T v} (hop : op = Binop.lt s ∨ op = Binop.leq s)
    (w : (Term.mk (.binop op a b) T).WT) (e : eval FS ρ (.mk (.binop op a b) T) = some v) :
    ∃ n x y, eval FS ρ a = some (.bv n x) ∧ eval FS ρ b = some (.bv n y) ∧
      v = .bool (cmpZ op (bz s x) (bz s y)) := by
  rw [eval_binop w] at e
  rcases hop with rfl | rfl <;> simp only [evBinop, bvBin_eq_some] at e <;>
    obtain ⟨n, x, y, hx, hy, e⟩ := e <;> refine ⟨n, x, y, hx, hy, ?_⟩ <;>
    simp only [lt_val, leq_val, Option.some.injEq] at e <;> simp [cmpZ, ← e]

theorem bv_val_inj {n m : Nat} {x : BitVec n} {y : BitVec m} (h : Val.bv n x = Val.bv m y) :
    ∃ h : n = m, h ▸ x = y := by
  cases h; exact ⟨rfl, rfl⟩

theorem Refines.or_lt_lt {FS : FloatSem} {s : Bool} {a b : Term} {T1 T2 : Ty} :
    Refines FS (b_or.spec (.mk (.binop (.lt s) a b) T1) (.mk (.binop (.lt s) b a) T2))
      (.mk (.unop .not_ (.mk (.binop .eq a b) .bool)) .bool) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨-, -, -, w1, -⟩ := WT_or.1 w
    obtain ⟨-, hb, -, wa, wb⟩ := (WT_cmp (Or.inl rfl)).1 w1
    exact ⟨WT_not.2 ⟨rfl, rfl, WT_eq.2 ⟨hb.symm, rfl, wa, wb⟩⟩, rfl⟩
  · simp only [b_or.spec] at w e
    obtain ⟨-, -, -, w1, w2⟩ := WT_or.1 w
    obtain ⟨-, -, w3⟩ := WT_not.1 w'
    rw [eval_binop w] at e; simp only [evBinop, por_eq_some] at e
    rw [eval_unop w', eval_binop w3]
    rcases e with ⟨e1, rfl⟩ | ⟨e2, rfl⟩ | ⟨e1, e2, rfl⟩
    · obtain ⟨n, x, y, ha, hb, hv⟩ := eval_cmp_eq_some (Or.inl rfl) w1 e1
      rw [ha, hb]; simp [cmpZ] at hv; simp [evBinop, evUnop]; intro h; subst h; omega
    · obtain ⟨n, y, x, hb, ha, hv⟩ := eval_cmp_eq_some (Or.inl rfl) w2 e2
      rw [ha, hb]; simp [cmpZ] at hv; simp [evBinop, evUnop]; intro h; subst h; omega
    · obtain ⟨n, x, y, ha, hb, hv⟩ := eval_cmp_eq_some (Or.inl rfl) w1 e1
      obtain ⟨n', y', x', hb', ha', hv'⟩ := eval_cmp_eq_some (Or.inl rfl) w2 e2
      rw [ha] at ha'; rw [hb] at hb'
      cases ha'; cases hb'
      simp [cmpZ] at hv hv'
      have := bz_inj (s := s) (x := x) (y := y) (by omega)
      subst this
      rw [ha, hb]; simp [evBinop, evUnop]

theorem Refines.or_lt_leq {FS : FloatSem} {s : Bool} {a b : Term} {T1 T2 : Ty} :
    Refines FS (b_or.spec (.mk (.binop (.lt s) a b) T1) (.mk (.binop (.leq s) b a) T2)) v_true := by
  refine Refines.intro (fun w => by simp [b_or.spec]) (fun ρ v w w' e => ?_)
  simp only [b_or.spec] at w e
  obtain ⟨-, -, -, w1, w2⟩ := WT_or.1 w
  rw [eval_binop w] at e; simp only [evBinop, por_eq_some] at e
  rcases e with ⟨e1, rfl⟩ | ⟨e2, rfl⟩ | ⟨e1, e2, rfl⟩
  · simp
  · simp
  · obtain ⟨n, x, y, ha, hb, hv⟩ := eval_cmp_eq_some (Or.inl rfl) w1 e1
    obtain ⟨n', y', x', hb', ha', hv'⟩ := eval_cmp_eq_some (Or.inr rfl) w2 e2
    rw [ha] at ha'; rw [hb] at hb'
    cases ha'; cases hb'
    simp [cmpZ] at hv hv'
    omega

end BoolL
end Bvr
