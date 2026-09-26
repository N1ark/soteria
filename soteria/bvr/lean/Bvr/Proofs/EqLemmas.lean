import Bvr.Lemmas

/-! Lemmas for the equality, float and pointer rules. -/

namespace Bvr
namespace EqL

open Classical

/-! ## Evaluation yields values of the sort of the term -/

theorem hasSort_bool_iff {v : Val} : v.hasSort .bool ↔ ∃ b, v = .bool b := by
  cases v <;> simp [Val.hasSort]

@[simp] theorem Val.hasSort_bool {b : Bool} {T : Ty} : (Val.bool b).hasSort T ↔ T = .bool := by
  cases T <;> simp [Val.hasSort]

@[simp] theorem Val.hasSort_bv {n : Nat} {x : BitVec n} {T : Ty} :
    (Val.bv n x).hasSort T ↔ (T = .bitVector n ∨ T = .loc n) ∧ 0 < n := by
  cases T <;> simp [Val.hasSort, eq_comm]

@[simp] theorem Val.hasSort_ptr {n : Nat} {l o : BitVec n} {T : Ty} :
    (Val.ptr n l o).hasSort T ↔ T = .pointer n ∧ 0 < n := by
  cases T <;> simp [Val.hasSort, eq_comm]

@[simp] theorem Val.hasSort_float {p : Prec} {x : FBits p} {T : Ty} :
    (Val.float p x).hasSort T ↔ T = .float p := by
  cases T <;> simp [Val.hasSort, eq_comm]

mutual
theorem ev_hasSort {FS : FloatSem} : ∀ (ρ : Env) (t : Term), t.WT → ∀ v, ev FS ρ t = some v →
    v.hasSort t.ty.sort
  | ρ, .mk (.var x) T, w, v, e => by
    simp only [ev] at e; split at e
    · split at e <;> simp_all [Val.hasTy]
    · simp at e
  | ρ, .mk (.bool b) T, w, v, e => by
    simp [Term.WT] at w; subst w; simp [ev] at e; subst e; simp [Val.hasSort]
  | ρ, .mk (.float f) T, w, v, e => by
    simp [Term.WT] at w; obtain ⟨rfl, _⟩ := w; simp [ev] at e; subst e
    simp [FloatLit.sem]
  | ρ, .mk (.bitVec z) T, w, v, e => by
    obtain ⟨n, hn, hT, _⟩ := WT_bitVec.1 w
    simp [ev] at e; subst e
    simp only [Term.ty_mk, Ty.sort_eq, Ty.width_of_sort hT, Val.hasSort_bv]
    exact ⟨by rcases hT with rfl | rfl <;> simp, hn⟩
  | ρ, .mk (.ptr l o) T, w, v, e => by
    simp only [Term.WT] at w
    obtain ⟨n, hn, rfl, hl, ho, wl, wo⟩ := w
    simp only [ev] at e
    split at e <;> try simp at e
    rename_i n1 x m y h1 h2
    obtain ⟨rfl, rfl⟩ := e
    have := ev_hasSort ρ l wl _ h1
    rw [hl] at this
    simp [Val.hasSort] at this ⊢; omega
  | ρ, .mk (.seq l) T, w, v, e => by
    simp only [Term.WT] at w
    obtain ⟨E, rfl, wl⟩ := w
    simp only [ev, Option.map_eq_some_iff] at e
    obtain ⟨vs, h, rfl⟩ := e
    simp only [Term.ty_mk, Ty.sort, Val.hasSort]
    exact evList_hasSort ρ E l wl vs h
  | ρ, .mk (.unop op a) T, w, v, e => by
    have ⟨w1, wa⟩ := WT_unop.1 w
    simp only [ev] at e
    cases h : ev FS ρ a with
    | none => simp [h] at e
    | some x =>
      have hx := ev_hasSort ρ a wa x h
      rw [h] at e
      generalize a.ty.sort = A at hx w1
      simp only [Term.ty_mk]
      generalize T.sort = T' at w1
      rcases x with b | ⟨n, x⟩ | ⟨n, l, o⟩ | ⟨p, x⟩ | vs | x <;> cases op <;>
        simp only [evUnop, reduceCtorEq, Option.some.injEq] at e <;> (try subst e) <;>
        simp only [Unop.WT] at w1
      all_goals (try simp at e)
      all_goals (try obtain ⟨_, rfl⟩ := e)
      all_goals (simp only [Val.hasSort_bool, Val.hasSort_bv, Val.hasSort_float,
        Val.hasSort_ptr] at hx ⊢)
      all_goals grind
  | ρ, .mk (.binop op a b) T, w, v, e => by
    have ⟨w1, wa, wb⟩ := WT_binop.1 w
    simp only [ev] at e
    simp only [Term.ty_mk]
    generalize T.sort = T' at w1
    cases op
    case and_ =>
      simp only [evBinop, pand_eq_some] at e; simp only [Binop.WT] at w1; grind [Val.hasSort_bool]
    case or_ =>
      simp only [evBinop, por_eq_some] at e; simp only [Binop.WT] at w1; grind [Val.hasSort_bool]
    all_goals
      cases ha : ev FS ρ a with
      | none => rw [ha] at e; simp [evBinop, fArith, checkedOp] at e
      | some x =>
        cases hb : ev FS ρ b with
        | none =>
          rw [ha, hb] at e
          rcases x with _ | _ | _ | _ | _ | _ <;> simp [evBinop, fArith, checkedOp] at e
        | some y =>
          have hx := ev_hasSort ρ a wa x ha
          have hy := ev_hasSort ρ b wb y hb
          rw [ha, hb] at e
          generalize a.ty.sort = A at hx w1
          generalize b.ty.sort = B at hy w1
          simp only [Binop.WT] at w1
          rcases x with _ | ⟨n, x⟩ | _ | ⟨p, x⟩ | _ | _ <;> rcases y with _ | ⟨m, y⟩ | _ | ⟨q, y⟩ | _ | _ <;>
            simp only [evBinop, bvBin, fBin, fArith, checkedOp, reduceCtorEq, Option.some.injEq]
              at e <;>
            (try split at e) <;>
            (try simp only [Option.some.injEq, reduceCtorEq] at e) <;>
            (try split at e) <;>
            (try simp only [Option.some.injEq, reduceCtorEq] at e) <;>
            (try subst e) <;>
            simp only [Val.hasSort_bool, Val.hasSort_bv, Val.hasSort_float,
              Val.hasSort_ptr] at hx hy ⊢ <;> grind
  | ρ, .mk (.triop op a b c) T, w, v, e => by
    have ⟨w1, wa, wb, wc⟩ := WT_triop.1 w
    simp only [Term.ty_mk]
    cases op
    case ite =>
      simp only [Triop.WT] at w1
      obtain ⟨_, h2, h3⟩ := w1
      simp only [ev] at e
      split at e
      · rw [h3]; exact ev_hasSort ρ b wb v e
      · rw [h3, ← h2]; exact ev_hasSort ρ c wc v e
      · simp at e
    case fma =>
      simp only [ev] at e
      cases ha : ev FS ρ a with
      | none => simp [ha, evFma] at e
      | some x =>
        have hx := ev_hasSort ρ a wa x ha
        rw [ha] at e
        simp only [evFma] at e
        split at e
        · split at e
          · simp only [Option.some.injEq] at *; subst_vars
            simp only [Triop.WT] at w1
            simp only [Val.hasSort_float] at hx ⊢
            grind
          · simp at e
        · simp at e
  | ρ, .mk (.nop op l) T, w, v, e => by
    cases op
    simp only [Term.WT] at w
    simp only [ev, Option.map_eq_some_iff] at e
    obtain ⟨_, _, rfl⟩ := e
    simp [w.1]
  | ρ, .mk (.exists_ bs body) T, w, v, e => by
    simp only [Term.WT] at w
    simp only [ev] at e
    split at e <;> simp at e
    subst e; simp [w.1]
  | ρ, .mk (.extension x) T, w, v, e => by
    simp only [ev] at e; split at e
    · split at e <;> simp_all [Val.hasTy]
    · simp at e

theorem evList_hasSort {FS : FloatSem} : ∀ (ρ : Env) (E : Ty) (l : List Term), Term.WTList E l →
    ∀ vs, evList FS ρ l = some vs → Val.hasSortList vs E.sort
  | ρ, E, [], _, vs, e => by simp [evList] at e; subst e; simp [Val.hasSortList]
  | ρ, E, t :: ts, w, vs, e => by
    simp only [Term.WTList] at w
    obtain ⟨h1, wt, wts⟩ := w
    simp only [evList] at e
    split at e <;> simp at e
    rename_i v vs' h2 h3
    subst e
    have := ev_hasSort ρ t wt v h2
    rw [h1] at this
    exact ⟨this, evList_hasSort ρ E ts wts vs' h3⟩
end

theorem eval_hasSort {FS ρ t v} (h : eval FS ρ t = some v) : v.hasSort t.ty.sort :=
  ev_hasSort ρ t (eval_WT h) v (by rw [← eval_eq_ev (eval_WT h)]; exact h)

theorem eval_bool_val {FS ρ t v} (h : eval FS ρ t = some v) (ht : t.ty = .bool) :
    ∃ b, v = .bool b := by
  have := eval_hasSort h; rw [Ty.sort_eq, ht] at this
  cases v <;> simp_all [Val.hasSort]

/-! ## Equality -/

theorem WT_eq {a b t} : (Term.mk (.binop .eq a b) t).WT ↔
    a.ty = b.ty ∧ t = .bool ∧ a.WT ∧ b.WT := by
  simp [Term.WT, Binop.WT, and_assoc]

theorem eval_eq_some {FS ρ a b t v} (h : eval FS ρ (.mk (.binop .eq a b) t) = some v) :
    ∃ x y, eval FS ρ a = some x ∧ eval FS ρ b = some y ∧ v = .bool (decide (x = y)) := by
  rw [eval_binop (eval_WT h)] at h
  cases ha : eval FS ρ a <;> cases hb : eval FS ρ b <;> simp_all [evBinop]

theorem eval_eq_of {FS ρ a b t x y} (w : (Term.mk (.binop .eq a b) t).WT)
    (ha : eval FS ρ a = some x) (hb : eval FS ρ b = some y) :
    eval FS ρ (.mk (.binop .eq a b) t) = some (.bool (decide (x = y))) := by
  rw [eval_binop w, ha, hb]; simp [evBinop]

theorem WT_sem_eq {a b} : (sem_eq.spec a b).WT ↔ a.ty = b.ty ∧ a.WT ∧ b.WT := by
  simp [sem_eq.spec, WT_eq]

@[simp] theorem sem_eq_ty {a b} : (sem_eq.spec a b).ty = .bool := rfl

/-- Two equalities with the same truth value. -/
theorem Refines.eq_eq {FS a b a' b'}
    (syn : a.ty = b.ty → a.WT → b.WT → a'.ty = b'.ty ∧ a'.WT ∧ b'.WT)
    (sem : ∀ ρ x y, a.ty = b.ty → a.WT → b.WT → eval FS ρ a = some x →
      eval FS ρ b = some y → ∃ x' y', eval FS ρ a' = some x' ∧ eval FS ρ b' = some y' ∧
        (x = y ↔ x' = y')) :
    Refines FS (sem_eq.spec a b) (sem_eq.spec a' b') := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · have ⟨h1, h2, h3⟩ := WT_sem_eq.1 w
    exact ⟨WT_sem_eq.2 (syn h1 h2 h3), rfl⟩
  · have ⟨h1, h2, h3⟩ := WT_sem_eq.1 w
    obtain ⟨x, y, hx, hy, rfl⟩ := eval_eq_some e
    obtain ⟨x', y', hx', hy', hxy⟩ := sem ρ x y h1 h2 h3 hx hy
    rw [sem_eq.spec, eval_eq_of w' hx' hy']
    simp [hxy]

/-- An equality with a known truth value. -/
theorem Refines.eq_const {FS a b r}
    (syn : a.ty = b.ty → a.WT → b.WT → r.WT ∧ r.ty = .bool)
    (sem : ∀ ρ x y, a.ty = b.ty → a.WT → b.WT → eval FS ρ a = some x →
      eval FS ρ b = some y → eval FS ρ r = some (.bool (decide (x = y)))) :
    Refines FS (sem_eq.spec a b) r := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · have ⟨h1, h2, h3⟩ := WT_sem_eq.1 w
    simpa using syn h1 h2 h3
  · have ⟨h1, h2, h3⟩ := WT_sem_eq.1 w
    obtain ⟨x, y, hx, hy, rfl⟩ := eval_eq_some e
    exact sem ρ x y h1 h2 h3 hx hy

theorem Refines.sem_eq {FS : FloatSem} {O : Ops} {a b a' b'} (hO : O.Sound FS) (ha : Refines FS a a')
    (hb : Refines FS b b') : Refines FS (sem_eq.spec a b) (O.sem_eq a' b') :=
  Refines.trans (Refines.binop ha hb (fun _ => rfl)) (hO.sem_eq a' b')

theorem Refines.b_and {FS : FloatSem} {O : Ops} {a b a' b'} (hO : O.Sound FS) (ha : Refines FS a a')
    (hb : Refines FS b b') : Refines FS (b_and.spec a b) (O.b_and a' b') :=
  Refines.trans (Refines.binop ha hb (fun _ => rfl)) (hO.b_and a' b')

theorem Refines.b_not {FS : FloatSem} {O : Ops} {a a'} (hO : O.Sound FS) (ha : Refines FS a a') :
    Refines FS (b_not.spec a) (O.b_not a') :=
  Refines.trans (Refines.unop ha (fun _ => rfl)) (hO.b_not a')

theorem Refines.b_ite {FS : FloatSem} {O : Ops} {g a b g' a' b'} (hO : O.Sound FS) (hg : Refines FS g g')
    (ha : Refines FS a a') (hb : Refines FS b b') :
    Refines FS (b_ite.spec g a b) (O.b_ite g' a' b') := by
  refine Refines.trans (Refines.ite hg ha hb (fun w => ?_)) (hO.b_ite g' a' b')
  exact (ha.syn (WT_triop.1 w).2.2.1).2

/-! ## Literals -/

@[simp] theorem of_bool_WT (b : Bool) : (of_bool b).WT := by cases b <;> simp [of_bool]
@[simp] theorem of_bool_ty (b : Bool) : (of_bool b).ty = .bool := by cases b <;> rfl
@[simp] theorem eval_of_bool {FS ρ} (b : Bool) : eval FS ρ (of_bool b) = some (.bool b) := by
  cases b <;> simp [of_bool]

theorem Refines.of_bool_WT' {b : Bool} : (of_bool b).WT ∧ (of_bool b).ty = .bool := by simp

theorem WT_float {f t} : (Term.mk (.float f) t).WT ↔ t = .float f.prec ∧ f.bits < 2 ^ f.prec.size := by
  simp [Term.WT]

theorem eval_float {FS ρ f t} (h : (Term.mk (.float f) t).WT) :
    eval FS ρ (.mk (.float f) t) = some f.sem := by
  rw [eval_eq_ev h, ev]

theorem FloatLit.WF_of_WT {f t} (h : (Term.mk (.float f) t).WT) : f.WF := (WT_float.1 h).2

theorem FloatLit.eq_of_val {f g : FloatLit} (hp : f.prec = g.prec) (hf : f.WF) (hg : g.WF)
    (h : f.val.toNat = g.val.toNat) : f = g := by
  cases f; cases g; simp only [FloatLit.mk.injEq] at *; subst hp
  simp only [FloatLit.val, BitVec.toNat_ofNat] at h
  simp only [FloatLit.WF] at hf hg
  refine ⟨rfl, ?_⟩
  rwa [Nat.mod_eq_of_lt hf, Nat.mod_eq_of_lt hg] at h

theorem WT_ptr {l o t} : (Term.mk (.ptr l o) t).WT ↔ ∃ n : Int, 0 < n ∧ t = .pointer n ∧
    l.ty = .loc n ∧ o.ty = .bitVector n ∧ l.WT ∧ o.WT := by
  simp [Term.WT]

theorem eval_ptr_eq_some {FS ρ l o t v} (h : (Term.mk (.ptr l o) t).WT) :
    eval FS ρ (.mk (.ptr l o) t) = some v ↔
      ∃ n x y, eval FS ρ l = some (.bv n x) ∧ eval FS ρ o = some (.bv n y) ∧ v = .ptr n x y := by
  obtain ⟨_, _, _, _, _, wl, wo⟩ := WT_ptr.1 h
  rw [eval_eq_ev h]
  simp only [ev]
  rw [← eval_eq_ev wl, ← eval_eq_ev wo]
  split
  · rename_i n x m y hl ho
    rw [hl, ho]
    constructor
    · intro e; split at e <;> simp at e
      subst_vars; exact ⟨_, _, _, rfl, rfl, rfl⟩
    · rintro ⟨n', x', y', h1, h2, rfl⟩
      simp at h1 h2; obtain ⟨rfl, h1⟩ := h1; obtain ⟨rfl, h2⟩ := h2
      subst h1 h2; simp
  · rename_i hne
    simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro n x y h1 h2 _
    exact hne n x n y h1 h2

theorem eval_bitVec_range {FS ρ z t} (h : (Term.mk (.bitVec z) t).WT) :
    ∃ n : Nat, 0 < n ∧ (t = .bitVector n ∨ t = .loc n) ∧ 0 ≤ z ∧ z < 2 ^ n ∧
      eval FS ρ (.mk (.bitVec z) t) = some (.bv n (BitVec.ofInt n z)) := by
  obtain ⟨n, hn, hT, h1, h2⟩ := WT_bitVec.1 h
  exact ⟨n, hn, hT, h1, h2, by rw [eval_bitVec' (n := n) h hT]; simp⟩

theorem BitVec.ofInt_inj {n : Nat} {a b : Int} (ha : 0 ≤ a) (ha' : a < 2 ^ n) (hb : 0 ≤ b)
    (hb' : b < 2 ^ n) : BitVec.ofInt n a = BitVec.ofInt n b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofInt] at this
    rw [Int.emod_eq_of_lt ha (by exact_mod_cast ha'), Int.emod_eq_of_lt hb (by exact_mod_cast hb')]
      at this
    omega
  · rintro rfl; rfl

/-! ## Floats -/

end EqL

namespace FBits

variable {p : Prec}

theorem eq_comm' (x y : FBits p) : x.eq y = y.eq x := by
  unfold eq
  cases x.isNaN <;> cases y.isNaN <;> cases x.isZero <;> cases y.isZero <;>
    simp [Bool.and_comm, BEq.comm]

@[simp] theorem eq_self' (x : FBits p) : x.eq x = !x.isNaN := by
  unfold eq; cases x.isNaN <;> simp

theorem not_isNaN_of_isZero {x : FBits p} (h : x.isZero = true) : x.isNaN = false := by
  simp only [isZero, isNaN, Bool.and_eq_true, beq_iff_eq] at h ⊢
  simp [h.2]

theorem eq_of_isNaN_left {x : FBits p} (y : FBits p) (h : x.isNaN = true) : x.eq y = false := by
  simp [eq, h]

theorem eq_of_isNaN_right (x : FBits p) {y : FBits p} (h : y.isNaN = true) : x.eq y = false := by
  simp [eq, h]

theorem eq_of_isZero_left {x : FBits p} (y : FBits p) (h : x.isZero = true) :
    x.eq y = y.isZero := by
  have hx := not_isNaN_of_isZero h
  unfold eq
  by_cases hy : y.isZero = true
  · simp [hx, hy, h, not_isNaN_of_isZero hy]
  · have : (x == y) = false := by
      simp only [beq_eq_false_iff_ne]; rintro rfl; exact hy h
    simp [hx, hy, this]

theorem eq_of_isZero_right (x : FBits p) {y : FBits p} (h : y.isZero = true) :
    x.eq y = x.isZero := by
  rw [eq_comm']; exact eq_of_isZero_left x h

theorem eq_of_ne_left {x : FBits p} (y : FBits p) (h1 : x.isNaN = false) (h2 : x.isZero = false) :
    x.eq y = decide (x = y) := by
  unfold eq
  by_cases hxy : x = y
  · subst hxy; simp [h1]
  · have : (x == y) = false := by simp [hxy]
    simp [h2, this, hxy]

theorem abs_abs (x : FBits p) : x.abs.abs = x.abs := by
  simp [abs, BitVec.and_assoc]

theorem neg_neg (x : FBits p) : x.neg.neg = x := by
  simp [neg, BitVec.xor_assoc]

end FBits

namespace EqL

theorem fBin_eq_some {f : (p : Prec) → FBits p → FBits p → Option Val} {a b v} :
    fBin f a b = some v ↔
      ∃ p x y, a = some (.float p x) ∧ b = some (.float p y) ∧ f p x y = some v := by
  constructor
  · intro h
    rcases a with _ | ⟨_ | _ | _ | ⟨p, x⟩ | _ | _⟩ <;>
      rcases b with _ | ⟨_ | _ | _ | ⟨q, y⟩ | _ | _⟩ <;> simp [fBin] at h
    obtain ⟨rfl, h⟩ := h
    exact ⟨_, _, _, rfl, rfl, h⟩
  · rintro ⟨p, x, y, rfl, rfl, h⟩; simp [fBin, h]

theorem WT_fcmp {op a b t} (hop : op = .fEq ∨ op = .fLt ∨ op = .fLeq) :
    (Term.mk (.binop op a b) t).WT ↔
      (∃ p, a.ty = .float p) ∧ b.ty = a.ty ∧ t = .bool ∧ a.WT ∧ b.WT := by
  rcases hop with rfl | rfl | rfl <;> simp [Term.WT, Binop.WT, and_assoc]

theorem WT_farith {op a b t}
    (hop : op = .fAdd ∨ op = .fSub ∨ op = .fMul ∨ op = .fDiv ∨ op = .fRem ∨ op = .fMin ∨
      op = .fMax) :
    (Term.mk (.binop op a b) t).WT ↔
      (∃ p, a.ty = .float p) ∧ b.ty = a.ty ∧ t = a.ty ∧ a.WT ∧ b.WT := by
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Term.WT, Binop.WT, and_assoc]

theorem WT_funop {op a t}
    (hop : op = .fAbs ∨ op = .fNeg ∨ op = .fSqrt ∨ ∃ rm, op = .fRound rm) :
    (Term.mk (.unop op a) t).WT ↔ (∃ p, a.ty = .float p) ∧ t = a.ty ∧ a.WT := by
  rcases hop with rfl | rfl | rfl | ⟨rm, rfl⟩ <;> simp [Term.WT, Unop.WT, and_assoc]

theorem WT_ftest {op a t}
    (hop : op = .fIsNeg ∨ op = .fIsPos ∨ ∃ fc, op = .fIs fc) :
    (Term.mk (.unop op a) t).WT ↔ (∃ p, a.ty = .float p) ∧ t = .bool ∧ a.WT := by
  rcases hop with rfl | rfl | ⟨fc, rfl⟩ <;> simp [Term.WT, Unop.WT, and_assoc]

/-- Constant folding of a binary float operation on literals. -/
theorem Refines.float_bin_lits {FS : FloatSem} {O : Ops} (hO : O.Sound FS) {op lit}
    (hmem : (op, lit) ∈ [(.fAdd, O.orc.f_add), (.fSub, O.orc.f_sub), (.fMul, O.orc.f_mul),
      (.fDiv, O.orc.f_div), (.fRem, O.orc.f_rem), (.fMin, O.orc.f_min), (.fMax, O.orc.f_max)])
    {f1 f2 : FloatLit} {T1 T2 : Ty} :
    Refines FS (.mk (.binop op (.mk (.float f1) T1) (.mk (.float f2) T2)) T1)
      (.mk (.float (lit f1 f2)) T1) := by
  have hop : op = .fAdd ∨ op = .fSub ∨ op = .fMul ∨ op = .fDiv ∨ op = .fRem ∨ op = .fMin ∨
      op = .fMax := by
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h | h | h | h <;> simp [h.1]
  have key : (Term.mk (.binop op (.mk (.float f1) T1) (.mk (.float f2) T2)) T1).WT →
      T1 = .float f1.prec ∧ f1.WF ∧ f2.WF ∧ f1.prec = f2.prec := by
    intro w
    obtain ⟨_, h2, _, w1, w2⟩ := (WT_farith hop).1 w
    obtain ⟨h3, h4⟩ := WT_float.1 w1
    obtain ⟨h5, h6⟩ := WT_float.1 w2
    simp only [Term.ty_mk] at h2
    subst h3 h5
    simp only [Ty.float.injEq] at h2
    exact ⟨rfl, h4, h6, h2.symm⟩
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨hT, h1, h2, hp⟩ := key w
    have := hO.orc.bin op lit hmem f1 f2 h1 h2 hp
    exact ⟨WT_float.2 ⟨by rw [hT, this.1], this.2.1⟩, rfl⟩
  · obtain ⟨hT, h1, h2, hp⟩ := key w
    have := hO.orc.bin op lit hmem f1 f2 h1 h2 hp
    have ⟨_, w1, w2⟩ := WT_binop.1 w
    rw [eval_binop w, eval_float w1, eval_float w2, this.2.2] at e
    rw [eval_float w']; exact e

/-- Constant folding of a unary operation on a float literal. -/
theorem Refines.lit_of_unop {FS : FloatSem} {op : Unop} {f g : FloatLit} {T T' : Ty}
    (hsyn : (Term.mk (.unop op (.mk (.float f) T)) T').WT → T' = .float g.prec ∧ g.WF)
    (hsem : f.WF → evUnop FS op (some f.sem) = some g.sem) :
    Refines FS (.mk (.unop op (.mk (.float f) T)) T') (.mk (.float g) T') := by
  refine Refines.intro (fun w => ⟨WT_float.2 (hsyn w), rfl⟩) (fun ρ v w w' e => ?_)
  have ⟨_, w1⟩ := WT_unop.1 w
  rw [eval_unop w, eval_float w1, hsem (FloatLit.WF_of_WT w1)] at e
  rw [eval_float w']; exact e

/-- A unary test on a float literal. -/
theorem Refines.test_of_unop {FS : FloatSem} {op : Unop} {f : FloatLit} {T T' : Ty} {b : Bool}
    (hsyn : (Term.mk (.unop op (.mk (.float f) T)) T').WT → T' = .bool)
    (hsem : evUnop FS op (some f.sem) = some (.bool b)) :
    Refines FS (.mk (.unop op (.mk (.float f) T)) T') (of_bool b) := by
  refine Refines.intro (fun w => ⟨by simp, by simp [hsyn w]⟩) (fun ρ v w w' e => ?_)
  have ⟨_, w1⟩ := WT_unop.1 w
  rw [eval_unop w, eval_float w1, hsem] at e
  rw [eval_of_bool]; exact e

theorem FloatLit.val_ofNat_toNat {p : Prec} (x : FBits p) :
    (⟨p, x.toNat⟩ : FloatLit).val = x := by
  simp [FloatLit.val]

theorem Refines.raw_fmod {FS : FloatSem} {r r' v1 v2 : Term} (hr : Refines FS r r') :
    Refines FS (raw_fmod_of_rem r v1 v2) (raw_fmod_of_rem r' v1 v2) := by
  have hs : ∀ w : r.WT, r'.ty = r.ty := fun w => by simpa using (hr.syn w).2
  refine Refines.ite (Refines.binop (Refines.unop hr (fun _ => rfl)) Refines.refl (fun _ => rfl))
    hr (Refines.binop hr Refines.refl (fun w => ?_)) (fun w => ?_)
  · simpa using hs (WT_binop.1 w).2.1
  · simpa using hs (WT_triop.1 w).2.2.1

/-! ## Bit-vector operations -/

theorem eval_bv_of_ty {FS ρ t v} {n : Int} (h : eval FS ρ t = some v)
    (ht : t.ty = .bitVector n ∨ t.ty = .loc n) : 0 < n ∧ ∃ x, v = .bv n.toNat x := by
  have := eval_hasSort h
  rw [Ty.sort_eq] at this
  rcases v with _ | ⟨m, x⟩ | _ | _ | _ | _ <;> rcases ht with ht | ht <;> rw [ht] at this <;>
    simp [Val.hasSort] at this
  all_goals
    obtain ⟨h1, h2⟩ := this
    subst h1
    exact ⟨by omega, x, by simp⟩

theorem checkedOp_eq_some {c : Checked} {so uo : ∀ {n : Nat}, BitVec n → BitVec n → Bool}
    {f : ∀ {n : Nat}, BitVec n → BitVec n → BitVec n} {a b v} :
    checkedOp c so uo f a b = some v ↔ ∃ n x y, a = some (.bv n x) ∧ b = some (.bv n y) ∧
      ((c.signed && so x y) || (c.unsigned && uo x y)) = false ∧ v = .bv n (f x y) := by
  constructor
  · intro h
    rcases a with _ | ⟨_ | ⟨n, x⟩ | _ | _ | _ | _⟩ <;>
      rcases b with _ | ⟨_ | ⟨m, y⟩ | _ | _ | _ | _⟩ <;> simp [checkedOp, bvBin] at h
    obtain ⟨rfl, hc, rfl⟩ := h
    refine ⟨_, _, _, rfl, rfl, ?_, rfl⟩
    cases c; rename_i s u; cases s <;> cases u <;> simp_all
  · rintro ⟨n, x, y, rfl, rfl, hc, rfl⟩; simp [checkedOp, bvBin, hc]

theorem bvBin_eq_some {f : ∀ {n : Nat}, BitVec n → BitVec n → Option Val} {a b v} :
    bvBin f a b = some v ↔ ∃ n x y, a = some (.bv n x) ∧ b = some (.bv n y) ∧ f x y = some v := by
  constructor
  · intro h
    rcases a with _ | ⟨_ | ⟨n, x⟩ | _ | _ | _ | _⟩ <;>
      rcases b with _ | ⟨_ | ⟨m, y⟩ | _ | _ | _ | _⟩ <;> simp [bvBin] at h
    obtain ⟨rfl, h⟩ := h
    exact ⟨_, _, _, rfl, rfl, h⟩
  · rintro ⟨n, x, y, rfl, rfl, h⟩; simp [bvBin, h]

theorem WT_bvbin {op a b t}
    (hop : (∃ c, op = .add c) ∨ (∃ c, op = .sub c) ∨ (∃ c, op = .mul c) ∨ op = .bitAnd ∨
      op = .bitOr) :
    (Term.mk (.binop op a b) t).WT ↔
      (∃ n : Int, 0 < n ∧ a.ty = .bitVector n) ∧ b.ty = a.ty ∧ t = a.ty ∧ a.WT ∧ b.WT := by
  rcases hop with ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩ | rfl | rfl <;>
    simp [Term.WT, Binop.WT, and_assoc]

theorem WT_bvunop {op a t} (hop : (∃ c, op = .neg c) ∨ op = .bvNot) :
    (Term.mk (.unop op a) t).WT ↔
      (∃ n : Int, 0 < n ∧ a.ty = .bitVector n) ∧ t = a.ty ∧ a.WT := by
  rcases hop with ⟨c, rfl⟩ | rfl <;> simp [Term.WT, Unop.WT] <;> grind

theorem eval_add_some {FS ρ c a b t v} (h : eval FS ρ (.mk (.binop (.add c) a b) t) = some v) :
    ∃ n x y, eval FS ρ a = some (.bv n x) ∧ eval FS ρ b = some (.bv n y) ∧ v = .bv n (x + y) := by
  rw [eval_binop (eval_WT h)] at h
  obtain ⟨n, x, y, h1, h2, _, rfl⟩ := checkedOp_eq_some.1 h
  exact ⟨n, x, y, h1, h2, rfl⟩

theorem eval_sub_some {FS ρ c a b t v} (h : eval FS ρ (.mk (.binop (.sub c) a b) t) = some v) :
    ∃ n x y, eval FS ρ a = some (.bv n x) ∧ eval FS ρ b = some (.bv n y) ∧ v = .bv n (x - y) := by
  rw [eval_binop (eval_WT h)] at h
  obtain ⟨n, x, y, h1, h2, _, rfl⟩ := checkedOp_eq_some.1 h
  exact ⟨n, x, y, h1, h2, rfl⟩

theorem eval_add_unchecked {FS ρ a b t n x y} (w : (Term.mk (.binop (.add unchecked) a b) t).WT)
    (ha : eval FS ρ a = some (.bv n x)) (hb : eval FS ρ b = some (.bv n y)) :
    eval FS ρ (.mk (.binop (.add unchecked) a b) t) = some (.bv n (x + y)) := by
  rw [eval_binop w, ha, hb]; simp [evBinop, checkedOp, bvBin, unchecked]

theorem eval_sub_unchecked {FS ρ a b t n x y} (w : (Term.mk (.binop (.sub unchecked) a b) t).WT)
    (ha : eval FS ρ a = some (.bv n x)) (hb : eval FS ρ b = some (.bv n y)) :
    eval FS ρ (.mk (.binop (.sub unchecked) a b) t) = some (.bv n (x - y)) := by
  rw [eval_binop w, ha, hb]; simp [evBinop, checkedOp, bvBin, unchecked]

theorem Refines.eq_symm {FS : FloatSem} {a b : Term} :
    Refines FS (sem_eq.spec a b) (sem_eq.spec b a) :=
  Refines.eq_eq (fun h wa wb => ⟨h.symm, wb, wa⟩) (fun _ x y _ _ _ hx hy => ⟨y, x, hy, hx, eq_comm⟩)

/-- Widths of two bit-vector values of the same type. -/
theorem bv_width_eq {FS ρ a b n m x y} {N : Int} (ha : eval FS ρ a = some (.bv n x))
    (hb : eval FS ρ b = some (.bv m y)) (hta : a.ty = .bitVector N) (htb : b.ty = .bitVector N) :
    n = m := by
  obtain ⟨_, x', hx⟩ := eval_bv_of_ty ha (Or.inl hta)
  obtain ⟨_, y', hy⟩ := eval_bv_of_ty hb (Or.inl htb)
  simp at hx hy; omega

/-- Moving an invertible unary operation to the other side of an equality. -/
theorem Refines.eq_unop_move {FS : FloatSem} {op op' : Unop} {f : ∀ {n : Nat}, BitVec n → BitVec n}
    (hop : (∃ c, op = .neg c) ∨ op = .bvNot) (hop' : (∃ c, op' = .neg c) ∨ op' = .bvNot)
    (hev : ∀ v r, evUnop FS op v = some r → ∃ n x, v = some (.bv n x) ∧ r = .bv n (f x))
    (hev' : ∀ n x, evUnop FS op' (some (.bv n x)) = some (.bv n (f x)))
    (hf : ∀ n (a b : BitVec n), a = f b ↔ f a = b) {c y : Term} {T2 : Ty} :
    Refines FS (sem_eq.spec c (.mk (.unop op y) T2)) (sem_eq.spec (.mk (.unop op' c) c.ty) y) := by
  have syn : c.ty = T2 → c.WT → (Term.mk (.unop op y) T2).WT →
      (∃ N : Int, 0 < N ∧ c.ty = .bitVector N ∧ y.ty = .bitVector N) ∧
      (Term.mk (.unop op' c) c.ty).WT ∧ y.WT := by
    intro hT wc w2
    obtain ⟨⟨n, hn, hy⟩, hT2, wy⟩ := (WT_bvunop hop).1 w2
    subst hT
    exact ⟨⟨n, hn, by rw [hT2, hy], hy⟩,
      (WT_bvunop hop').2 ⟨⟨n, hn, by rw [hT2, hy]⟩, rfl, wc⟩, wy⟩
  refine Refines.eq_eq (fun hT wc w2 => ?_) (fun ρ x y' hT wc w2 hx hy => ?_)
  · obtain ⟨⟨N, _, h1, h2⟩, w, wy⟩ := syn hT wc w2
    exact ⟨by simp [h1, h2], w, wy⟩
  · obtain ⟨⟨N, _, h1, h2⟩, w, wy⟩ := syn hT wc w2
    rw [eval_unop w2] at hy
    obtain ⟨n, b, hb, rfl⟩ := hev _ _ hy
    obtain ⟨_, a, rfl⟩ := eval_bv_of_ty hx (Or.inl h1)
    obtain ⟨_, b', hb'⟩ := eval_bv_of_ty hb (Or.inl h2)
    simp at hb'; obtain ⟨rfl, hb'⟩ := hb'; subst hb'
    refine ⟨_, _, by rw [eval_unop w, hx, hev'], hb, ?_⟩
    simp [hf]

/-- Moving an operand of an arithmetic operation to the other side of an equality. -/
theorem Refines.eq_bin_move {FS : FloatSem} {op op' : Binop}
    {f g : ∀ {n : Nat}, BitVec n → BitVec n → BitVec n}
    (hop : (∃ c, op = .add c) ∨ (∃ c, op = .sub c) ∨ (∃ c, op = .mul c) ∨ op = .bitAnd ∨
      op = .bitOr)
    (hop' : (∃ c, op' = .add c) ∨ (∃ c, op' = .sub c) ∨ (∃ c, op' = .mul c) ∨ op' = .bitAnd ∨
      op' = .bitOr)
    (hev : ∀ a b r, evBinop FS op a b = some r →
      ∃ n x y, a = some (.bv n x) ∧ b = some (.bv n y) ∧ r = .bv n (f x y))
    (hev' : ∀ n x y, evBinop FS op' (some (.bv n x)) (some (.bv n y)) = some (.bv n (g x y)))
    {c p q : Term} {T2 : Ty} (A B D : Term) (hA : A = c ∨ A = p ∨ A = q)
    (hB : B = c ∨ B = p ∨ B = q) (hD : D = c ∨ D = p ∨ D = q)
    (hsel : ∀ ρ n (a x y : BitVec n), eval FS ρ c = some (.bv n a) →
      eval FS ρ p = some (.bv n x) → eval FS ρ q = some (.bv n y) →
      ∃ a' b' d', eval FS ρ A = some (.bv n a') ∧ eval FS ρ B = some (.bv n b') ∧
        eval FS ρ D = some (.bv n d') ∧ (a = f x y ↔ g a' b' = d')) :
    Refines FS (sem_eq.spec c (.mk (.binop op p q) T2))
      (sem_eq.spec (.mk (.binop op' A B) A.ty) D) := by
  have syn : c.ty = T2 → c.WT → (Term.mk (.binop op p q) T2).WT →
      (∃ N : Int, 0 < N ∧ c.ty = .bitVector N ∧ p.ty = .bitVector N ∧ q.ty = .bitVector N) ∧
      (Term.mk (.binop op' A B) A.ty).WT ∧ A.ty = D.ty ∧ D.WT := by
    intro hT wc w2
    obtain ⟨⟨n, hn, hp⟩, hq, hT2, wp, wq⟩ := (WT_bvbin hop).1 w2
    subst hT
    have hc : c.ty = .bitVector n := by rw [hT2, hp]
    have hq' : q.ty = .bitVector n := by rw [hq, hp]
    have key : ∀ X, (X = c ∨ X = p ∨ X = q) → X.ty = .bitVector n ∧ X.WT := by
      rintro X (rfl | rfl | rfl) <;> simp_all
    obtain ⟨tA, wA⟩ := key A hA
    obtain ⟨tB, wB⟩ := key B hB
    obtain ⟨tD, wD⟩ := key D hD
    exact ⟨⟨n, hn, hc, hp, hq'⟩, (WT_bvbin hop').2 ⟨⟨n, hn, tA⟩, by rw [tA, tB], rfl, wA, wB⟩,
      by rw [tA, tD], wD⟩
  refine Refines.eq_eq (fun hT wc w2 => ?_) (fun ρ x y' hT wc w2 hx hy => ?_)
  · obtain ⟨_, w, h1, wD⟩ := syn hT wc w2
    exact ⟨h1, w, wD⟩
  · obtain ⟨⟨N, _, h1, h2, h3⟩, w, _, _⟩ := syn hT wc w2
    rw [eval_binop w2] at hy
    obtain ⟨n, a1, a2, hp, hq, rfl⟩ := hev _ _ _ hy
    obtain ⟨_, a, rfl⟩ := eval_bv_of_ty hx (Or.inl h1)
    obtain ⟨_, b', hb'⟩ := eval_bv_of_ty hp (Or.inl h2)
    simp at hb'; obtain ⟨rfl, hb'⟩ := hb'; subst hb'
    obtain ⟨a', b', d', hA', hB', hD', hiff⟩ := hsel ρ _ a a1 a2 hx hp hq
    refine ⟨_, _, by rw [eval_binop w, hA', hB', hev'], hD', ?_⟩
    simp [hiff]

theorem evBinop_add_some {FS c a b r} (h : evBinop FS (.add c) a b = some r) :
    ∃ n x y, a = some (.bv n x) ∧ b = some (.bv n y) ∧ r = .bv n (x + y) := by
  obtain ⟨n, x, y, h1, h2, _, rfl⟩ := checkedOp_eq_some.1 h
  exact ⟨n, x, y, h1, h2, rfl⟩

theorem evBinop_sub_some {FS c a b r} (h : evBinop FS (.sub c) a b = some r) :
    ∃ n x y, a = some (.bv n x) ∧ b = some (.bv n y) ∧ r = .bv n (x - y) := by
  obtain ⟨n, x, y, h1, h2, _, rfl⟩ := checkedOp_eq_some.1 h
  exact ⟨n, x, y, h1, h2, rfl⟩

@[simp] theorem evBinop_add_unchecked {FS n} {x y : BitVec n} :
    evBinop FS (.add unchecked) (some (.bv n x)) (some (.bv n y)) = some (.bv n (x + y)) := by
  simp [evBinop, checkedOp, bvBin, unchecked]

@[simp] theorem evBinop_sub_unchecked {FS n} {x y : BitVec n} :
    evBinop FS (.sub unchecked) (some (.bv n x)) (some (.bv n y)) = some (.bv n (x - y)) := by
  simp [evBinop, checkedOp, bvBin, unchecked]

theorem eval_lit_bv {FS ρ z T n b} (w : (Term.mk (.bitVec z) T).WT)
    (h : eval FS ρ (.mk (.bitVec z) T) = some (.bv n b)) :
    b = BitVec.ofInt n z ∧ 0 ≤ z ∧ z < 2 ^ n ∧ (T = .bitVector n ∨ T = .loc n) := by
  obtain ⟨m, _, hT, h1, h2, e⟩ := eval_bitVec_range (FS := FS) (ρ := ρ) w
  rw [e] at h; simp at h; obtain ⟨rfl, h⟩ := h; subst h
  exact ⟨rfl, h1, h2, hT⟩

theorem lit_eq_zero_iff {n : Nat} {z : Int} (h1 : 0 ≤ z) (h2 : z < 2 ^ n) :
    BitVec.ofInt n z = 0 ↔ z = 0 := by
  have := BitVec.ofInt_inj (n := n) h1 h2 (Int.le_refl 0) (two_pow_pos' n)
  simpa using this

/-- Two additions compared, and one addition moved to the other side. -/
theorem Refines.eq_add_add {FS : FloatSem} {c1 c2 : Checked} {A1 B1 A2 B2 : Term} {T1 T2 : Ty}
    (x y l r : Term) (hx : x = A1 ∨ x = B1 ∨ x = A2 ∨ x = B2)
    (hy : y = A1 ∨ y = B1 ∨ y = A2 ∨ y = B2) (hl : l = A1 ∨ l = B1 ∨ l = A2 ∨ l = B2)
    (hr : r = A1 ∨ r = B1 ∨ r = A2 ∨ r = B2)
    (hsel : ∀ ρ n (a1 b1 a2 b2 : BitVec n), eval FS ρ A1 = some (.bv n a1) →
      eval FS ρ B1 = some (.bv n b1) → eval FS ρ A2 = some (.bv n a2) →
      eval FS ρ B2 = some (.bv n b2) →
      ∃ xv yv lv rv, eval FS ρ x = some (.bv n xv) ∧ eval FS ρ y = some (.bv n yv) ∧
        eval FS ρ l = some (.bv n lv) ∧ eval FS ρ r = some (.bv n rv) ∧
        (a1 + b1 = a2 + b2 ↔ xv = yv + (lv - rv))) :
    Refines FS (sem_eq.spec (.mk (.binop (.add c1) A1 B1) T1) (.mk (.binop (.add c2) A2 B2) T2))
      (sem_eq.spec x (bv_add.spec unchecked y (bv_sub.spec unchecked l r))) := by
  have syn : T1 = T2 → (Term.mk (.binop (.add c1) A1 B1) T1).WT →
      (Term.mk (.binop (.add c2) A2 B2) T2).WT →
      (∃ N : Int, 0 < N ∧ A1.ty = .bitVector N ∧ A2.ty = .bitVector N) ∧
      x.ty = y.ty ∧ x.WT ∧ (bv_sub.spec unchecked l r).WT ∧
      (bv_add.spec unchecked y (bv_sub.spec unchecked l r)).WT := by
    intro hT w1 w2
    obtain ⟨⟨n, hn, h1⟩, h2, h3, wa1, wb1⟩ := (WT_bvbin (Or.inl ⟨_, rfl⟩)).1 w1
    obtain ⟨⟨m, hm, h4⟩, h5, h6, wa2, wb2⟩ := (WT_bvbin (Or.inl ⟨_, rfl⟩)).1 w2
    subst hT
    have key : ∀ X, (X = A1 ∨ X = B1 ∨ X = A2 ∨ X = B2) → X.ty = .bitVector n ∧ X.WT := by
      rintro X (rfl | rfl | rfl | rfl) <;> simp_all
    obtain ⟨tx, wx⟩ := key x hx
    obtain ⟨ty', wy⟩ := key y hy
    obtain ⟨tl, wl⟩ := key l hl
    obtain ⟨tr, wr⟩ := key r hr
    have ws : (bv_sub.spec unchecked l r).WT :=
      (WT_bvbin (Or.inr (Or.inl ⟨_, rfl⟩))).2 ⟨⟨n, hn, tl⟩, by rw [tl, tr], rfl, wl, wr⟩
    refine ⟨⟨n, hn, h1, by rw [(key A2 (by simp)).1]⟩, by rw [tx, ty'], wx, ws, ?_⟩
    exact (WT_bvbin (Or.inl ⟨_, rfl⟩)).2 ⟨⟨n, hn, ty'⟩, by simp [bv_sub.spec, tl, ty'], rfl, wy, ws⟩
  refine Refines.eq_eq (fun hT w1 w2 => ?_) (fun ρ u v hT w1 w2 hu hv => ?_)
  · obtain ⟨_, h1, h2, _, h3⟩ := syn hT w1 w2
    exact ⟨by simp [bv_add.spec, h1], h2, h3⟩
  · obtain ⟨⟨N, _, h1, h2⟩, _, _, ws, wa⟩ := syn hT w1 w2
    rw [eval_binop w1] at hu; rw [eval_binop w2] at hv
    obtain ⟨n, a1, b1, e1, e2, rfl⟩ := evBinop_add_some hu
    obtain ⟨m, a2, b2, e3, e4, rfl⟩ := evBinop_add_some hv
    obtain ⟨_, a1', h⟩ := eval_bv_of_ty e1 (Or.inl h1)
    obtain ⟨_, a2', h'⟩ := eval_bv_of_ty e3 (Or.inl h2)
    simp at h h'; obtain ⟨rfl, -⟩ := h; obtain ⟨rfl, -⟩ := h'
    obtain ⟨xv, yv, lv, rv, ex, ey, el, er, hiff⟩ := hsel ρ _ a1 b1 a2 b2 e1 e2 e3 e4
    refine ⟨_, .bv _ (yv + (lv - rv)), ex, ?_, ?_⟩
    · rw [bv_add.spec, eval_add_unchecked wa ey (by rw [bv_sub.spec, eval_sub_unchecked ws el er])]
    · simp [hiff]

theorem self_eq_add_lit_iff {n : Nat} {z : Int} (a : BitVec n) (h1 : 0 ≤ z) (h2 : z < 2 ^ n) :
    (a = a + BitVec.ofInt n z ↔ z = 0) := by
  rw [← lit_eq_zero_iff h1 h2]; grind

theorem self_eq_lit_add_iff {n : Nat} {z : Int} (a : BitVec n) (h1 : 0 ≤ z) (h2 : z < 2 ^ n) :
    (a = BitVec.ofInt n z + a ↔ z = 0) := by
  rw [← lit_eq_zero_iff h1 h2]; grind

theorem orElse_eq_some4 {α} {a b c d : Option α} {r : α} (h : (a <|> b <|> c <|> d) = some r) :
    a = some r ∨ b = some r ∨ c = some r ∨ d = some r := by
  rcases orElse_eq_some h with h | h
  · exact Or.inl h
  rcases orElse_eq_some h with h | h
  · exact Or.inr (Or.inl h)
  exact Or.inr (Or.inr (orElse_eq_some h))

/-! ## If-then-else -/

theorem WT_ite {g a b t} : (Term.mk (.triop .ite g a b) t).WT ↔
    g.ty = .bool ∧ b.ty = a.ty ∧ t = a.ty ∧ g.WT ∧ a.WT ∧ b.WT := by
  simp [Term.WT, Triop.WT, and_assoc]

theorem eval_ite_eq_some {FS ρ g a b t v} (w : (Term.mk (.triop .ite g a b) t).WT) :
    eval FS ρ (.mk (.triop .ite g a b) t) = some v ↔
      (eval FS ρ g = some (.bool true) ∧ eval FS ρ a = some v) ∨
        (eval FS ρ g = some (.bool false) ∧ eval FS ρ b = some v) := by
  rw [eval_ite w]; split <;> simp_all

theorem eval_ite_of {FS ρ g a b t} (w : (Term.mk (.triop .ite g a b) t).WT) {c : Bool}
    (hg : eval FS ρ g = some (.bool c)) :
    eval FS ρ (.mk (.triop .ite g a b) t) = if c then eval FS ρ a else eval FS ρ b := by
  rw [eval_ite w, hg]; cases c <;> rfl

theorem WT_b_ite_eqs {g a b c d : Term} (hg : g.ty = .bool) (wg : g.WT)
    (h1 : (sem_eq.spec a b).WT) (h2 : (sem_eq.spec c d).WT) :
    (b_ite.spec g (sem_eq.spec a b) (sem_eq.spec c d)).WT := by
  exact WT_triop.2 ⟨by simp [Triop.WT, hg, b_ite.spec], wg, h1, h2⟩

/-- An equality between two [ite]s on the same guard. -/
theorem Refines.eq_ite_ite {FS : FloatSem} {g l r l' r' : Term} {T1 T2 : Ty} :
    Refines FS (sem_eq.spec (.mk (.triop .ite g l r) T1) (.mk (.triop .ite g l' r') T2))
      (b_ite.spec g (sem_eq.spec l l') (sem_eq.spec r r')) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨hT, w1, w2⟩ := WT_sem_eq.1 w
    obtain ⟨hg, h1, h2, wg, wl, wr⟩ := WT_ite.1 w1
    obtain ⟨_, h1', h2', _, wl', wr'⟩ := WT_ite.1 w2
    simp only [Term.ty_mk] at hT
    refine ⟨WT_b_ite_eqs hg wg (WT_sem_eq.2 ⟨?_, wl, wl'⟩) (WT_sem_eq.2 ⟨?_, wr, wr'⟩), rfl⟩
    · rw [← h2, hT, h2']
    · rw [h1, ← h2, hT, h2', h1']
  · obtain ⟨hT, w1, w2⟩ := WT_sem_eq.1 w
    obtain ⟨x, y, hx, hy, rfl⟩ := eval_eq_some e
    have ⟨_, wg, wa, wb⟩ := WT_triop.1 w'
    rw [eval_ite_eq_some w1] at hx; rw [eval_ite_eq_some w2] at hy
    rcases hx with ⟨hg, hx⟩ | ⟨hg, hx⟩ <;> rcases hy with ⟨hg', hy⟩ | ⟨hg', hy⟩ <;>
      rw [hg] at hg' <;> simp at hg'
    · rw [b_ite.spec, eval_ite_of w' hg]; simp [sem_eq.spec, eval_eq_of wa hx hy]
    · rw [b_ite.spec, eval_ite_of w' hg]; simp [sem_eq.spec, eval_eq_of wb hx hy]

/-- An equality with an [ite] on the left. -/
theorem Refines.eq_ite_l {FS : FloatSem} {g l r c : Term} {T : Ty} :
    Refines FS (sem_eq.spec (.mk (.triop .ite g l r) T) c)
      (b_ite.spec g (sem_eq.spec l c) (sem_eq.spec r c)) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨hT, w1, w2⟩ := WT_sem_eq.1 w
    obtain ⟨hg, h1, h2, wg, wl, wr⟩ := WT_ite.1 w1
    simp only [Term.ty_mk] at hT
    refine ⟨WT_b_ite_eqs hg wg (WT_sem_eq.2 ⟨?_, wl, w2⟩) (WT_sem_eq.2 ⟨?_, wr, w2⟩), rfl⟩
    · rw [← h2, hT]
    · rw [h1, ← h2, hT]
  · obtain ⟨hT, w1, w2⟩ := WT_sem_eq.1 w
    obtain ⟨x, y, hx, hy, rfl⟩ := eval_eq_some e
    have ⟨_, wg, wa, wb⟩ := WT_triop.1 w'
    rw [eval_ite_eq_some w1] at hx
    rcases hx with ⟨hg, hx⟩ | ⟨hg, hx⟩
    · rw [b_ite.spec, eval_ite_of w' hg]; simp [sem_eq.spec, eval_eq_of wa hx hy]
    · rw [b_ite.spec, eval_ite_of w' hg]; simp [sem_eq.spec, eval_eq_of wb hx hy]

/-- An equality with an [ite] on the right. -/
theorem Refines.eq_ite_r {FS : FloatSem} {g l r c : Term} {T : Ty} :
    Refines FS (sem_eq.spec c (.mk (.triop .ite g l r) T))
      (b_ite.spec g (sem_eq.spec c l) (sem_eq.spec c r)) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨hT, w1, w2⟩ := WT_sem_eq.1 w
    obtain ⟨hg, h1, h2, wg, wl, wr⟩ := WT_ite.1 w2
    simp only [Term.ty_mk] at hT
    refine ⟨WT_b_ite_eqs hg wg (WT_sem_eq.2 ⟨?_, w1, wl⟩) (WT_sem_eq.2 ⟨?_, w1, wr⟩), rfl⟩
    · rw [hT, h2]
    · rw [hT, h2, h1]
  · obtain ⟨hT, w1, w2⟩ := WT_sem_eq.1 w
    obtain ⟨x, y, hx, hy, rfl⟩ := eval_eq_some e
    have ⟨_, wg, wa, wb⟩ := WT_triop.1 w'
    rw [eval_ite_eq_some w2] at hy
    rcases hy with ⟨hg, hy⟩ | ⟨hg, hy⟩
    · rw [b_ite.spec, eval_ite_of w' hg]; simp [sem_eq.spec, eval_eq_of wa hx hy]
    · rw [b_ite.spec, eval_ite_of w' hg]; simp [sem_eq.spec, eval_eq_of wb hx hy]

theorem BitVec.append_inj_iff {n m : Nat} {a c : BitVec n} {b d : BitVec m} :
    a ++ b = c ++ d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have h1 := congrArg (fun x => x.extractLsb' m n) h
    have h2 := congrArg (fun x => x.extractLsb' 0 m) h
    simp only [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem BitVec.one_ne_zero' {k : Nat} (hk : 0 < k) : (1 : BitVec k) ≠ 0 := by
  intro e
  have := congrArg BitVec.toNat e
  simp at this; omega

theorem BitVec.ofBool_inj {k : Nat} (hk : 0 < k) {b1 b2 : Bool} :
    ((if b1 then 1 else 0 : BitVec k) = if b2 then 1 else 0) ↔ b1 = b2 := by
  cases b1 <;> cases b2 <;> simp <;> omega


theorem pand_bools (a b : Bool) :
    pand (some (.bool a)) (some (.bool b)) = some (.bool (a && b)) := by
  cases a <;> cases b <;> rfl

/-- An equality that splits into the conjunction of two equalities. -/
theorem Refines.eq_and {FS : FloatSem} {a b c d e f : Term}
    (syn : a.ty = b.ty → a.WT → b.WT → c.ty = d.ty ∧ c.WT ∧ d.WT ∧ e.ty = f.ty ∧ e.WT ∧ f.WT)
    (sem : ∀ ρ x y, a.ty = b.ty → a.WT → b.WT → eval FS ρ a = some x →
      eval FS ρ b = some y → ∃ xc xd xe xf, eval FS ρ c = some xc ∧ eval FS ρ d = some xd ∧
        eval FS ρ e = some xe ∧ eval FS ρ f = some xf ∧ (x = y ↔ xc = xd ∧ xe = xf)) :
    Refines FS (sem_eq.spec a b) (b_and.spec (sem_eq.spec c d) (sem_eq.spec e f)) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' hev => ?_)
  · have ⟨h1, h2, h3⟩ := WT_sem_eq.1 w
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := syn h1 h2 h3
    exact ⟨WT_and.2 ⟨by simp, by simp, rfl, WT_sem_eq.2 ⟨k1, k2, k3⟩, WT_sem_eq.2 ⟨k4, k5, k6⟩⟩,
      rfl⟩
  · have ⟨h1, h2, h3⟩ := WT_sem_eq.1 w
    obtain ⟨x, y, hx, hy, rfl⟩ := eval_eq_some hev
    obtain ⟨xc, xd, xe, xf, ec, ed, ee, ef, hiff⟩ := sem ρ x y h1 h2 h3 hx hy
    have ⟨_, wl, wr⟩ := WT_binop.1 w'
    simp only [sem_eq.spec] at wl wr
    rw [b_and.spec, eval_binop w', sem_eq.spec, sem_eq.spec, eval_eq_of wl ec ed,
      eval_eq_of wr ee ef, evBinop, pand_bools]
    simp only [Option.some.injEq, Val.bool.injEq]
    by_cases h : x = y <;> simp_all


/-- An equality between [bv_of_bool] and a literal. -/
theorem Refines.eq_of_bool_lit {FS : FloatSem} {b r : Term} {k z : Int} {T1 T2 : Ty}
    (hsyn : b.ty = .bool → b.WT → r.WT ∧ r.ty = .bool)
    (hsem : ∀ ρ (c : Bool) (n : Nat), 0 < n → 0 ≤ z → z < 2 ^ n →
      eval FS ρ b = some (.bool c) →
      eval FS ρ r = some (.bool (decide (((if c then 1 else 0) : BitVec n) = BitVec.ofInt n z)))) :
    Refines FS (sem_eq.spec (.mk (.unop (.bvOfBool k) b) T1) (.mk (.bitVec z) T2)) r := by
  refine Refines.eq_const (fun hT w1 w2 => ?_) (fun ρ x y hT w1 w2 hx hy => ?_)
  · have ⟨h1, wb⟩ := WT_unop.1 w1
    simp only [Unop.WT, Ty.sort_eq] at h1
    exact hsyn h1.2.1 wb
  · have ⟨h1, wb⟩ := WT_unop.1 w1
    simp only [Unop.WT, Ty.sort_eq, Term.ty_mk] at h1 hT
    obtain ⟨hk, hb, rfl⟩ := h1
    rw [eval_unop w1] at hx
    cases he : eval FS ρ b with
    | none => rw [he] at hx; simp at hx
    | some vb =>
      obtain ⟨c, rfl⟩ := eval_bool_val he hb
      rw [he] at hx; simp only [evUnop, Option.some.injEq] at hx; subst hx
      obtain ⟨n, hn, hT2, z1, z2, e⟩ := eval_bitVec_range (FS := FS) (ρ := ρ) w2
      rw [e] at hy; cases hy
      rw [← hT] at hT2
      have : k.toNat = n := by rcases hT2 with h | h <;> simp at h; omega
      subst this
      rw [hsem ρ c _ hn z1 z2 he]; simp

end EqL
end Bvr
