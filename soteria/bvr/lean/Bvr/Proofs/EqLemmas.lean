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


theorem lit_WT' {z n : Int} (hn : 0 < n) (h0 : 0 ≤ z) (h1 : z < 2 ^ n.toNat) :
    (Term.mk (.bitVec z) (.bitVector n)).WT :=
  WT_bitVec.2 ⟨n.toNat, by omega, Or.inl (by simp; omega), h0, h1⟩

theorem eval_lit' {FS ρ} {z n : Int} (w : (Term.mk (.bitVec z) (.bitVector n)).WT) :
    eval FS ρ (.mk (.bitVec z) (.bitVector n)) = some (.bv n.toNat (BitVec.ofInt _ z)) :=
  eval_bitVec' w (Or.inl rfl)

@[simp] theorem bv_zero_ty' {n : Int} : (bv_zero n).ty = .bitVector n := rfl

theorem bv_zero_WT' {n : Int} (hn : 0 < n) : (bv_zero n).WT :=
  lit_WT' hn (by omega) (two_pow_pos' _)

theorem eval_bv_zero'' {FS ρ} {n : Int} (hn : 0 < n) :
    eval FS ρ (bv_zero n) = some (.bv n.toNat 0) := by
  rw [bv_zero, eval_lit' (bv_zero_WT' hn)]; simp

/-- The width of the value of a bit-vector term. -/
theorem eval_bv_ty {FS ρ t n m x} (h : eval FS ρ t = some (.bv m x)) (ht : t.ty = .bitVector n) :
    m = n.toNat ∧ 0 < n := by
  obtain ⟨hn, x', hx⟩ := eval_bv_of_ty h (Or.inl ht)
  simp at hx; exact ⟨hx.1, hn⟩


theorem WT_concat {a b t} : (Term.mk (.binop .bvConcat a b) t).WT ↔
    ∃ n m : Int, 0 < n ∧ 0 < m ∧ a.ty = .bitVector n ∧ b.ty = .bitVector m ∧
      t = .bitVector (n + m) ∧ a.WT ∧ b.WT := by
  simp [Term.WT, Binop.WT]; grind

theorem eval_concat_some {FS ρ a b t v} (w : (Term.mk (.binop .bvConcat a b) t).WT)
    (h : eval FS ρ (.mk (.binop .bvConcat a b) t) = some v) :
    ∃ n m x y, eval FS ρ a = some (.bv n x) ∧ eval FS ρ b = some (.bv m y) ∧
      v = .bv (n + m) (x ++ y) := by
  rw [eval_binop w] at h
  cases ha : eval FS ρ a with
  | none => rw [ha] at h; simp [evBinop] at h
  | some va =>
    cases hb : eval FS ρ b with
    | none => rw [ha, hb] at h; rcases va with _ | _ | _ | _ | _ | _ <;> simp [evBinop] at h
    | some vb =>
      rw [ha, hb] at h
      rcases va with _ | ⟨n, x⟩ | _ | _ | _ | _ <;> rcases vb with _ | ⟨m, y⟩ | _ | _ | _ | _ <;>
        simp [evBinop] at h
      exact ⟨n, m, x, y, rfl, rfl, h.symm⟩


theorem Val_bv_extract_congr {W k k' : Nat} (h : k = k') (c : BitVec W) (i : Nat) :
    Val.bv k (c.extractLsb' i k) = Val.bv k' (c.extractLsb' i k') := by subst h; rfl

theorem val_concat_iff {W A B : Nat} (c : BitVec W) (x : BitVec A) (y : BitVec B)
    (h : W = A + B) :
    Val.bv W c = Val.bv (A + B) (x ++ y) ↔
      (Val.bv A (c.extractLsb' B A) = Val.bv A x ∧ Val.bv B (c.extractLsb' 0 B) = Val.bv B y) := by
  subst h
  simp only [Val.bv.injEq, heq_eq_eq, true_and]
  constructor
  · rintro rfl
    exact ⟨BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right⟩
  · rintro ⟨rfl, rfl⟩
    exact BitVec.extractLsb'_append_extractLsb'.symm

theorem WT_extract_spec {Z : Term} {i j N : Int} (wZ : Z.WT) (hZ : Z.ty = .bitVector N)
    (h0 : 0 ≤ i) (h1 : i ≤ j) (h2 : j < N) : (bv_extract.spec i j Z).WT :=
  WT_unop.2 ⟨⟨N, by simpa using hZ, h0, h1, h2, rfl⟩, wZ⟩

theorem eval_extract_spec {FS ρ} {Z : Term} {i j : Int} {W : Nat} {c : BitVec W}
    (w : (bv_extract.spec i j Z).WT) (h : eval FS ρ Z = some (.bv W c)) :
    eval FS ρ (bv_extract.spec i j Z) = some (.bv (j - i + 1).toNat (c.extractLsb' i.toNat _)) := by
  rw [bv_extract.spec, eval_unop w, h]; rfl

/-- The high part of a bit-vector of width [n + m]. -/
theorem extract_hi {FS ρ} {Z : Term} {n m : Int} (hn : 0 < n) (hm : 0 < m) (wZ : Z.WT)
    (hZ : Z.ty = .bitVector (n + m)) :
    (bv_extract.spec m (m + n - 1) Z).WT ∧ (bv_extract.spec m (m + n - 1) Z).ty = .bitVector n ∧
      ∀ W (c : BitVec W), eval FS ρ Z = some (.bv W c) →
        eval FS ρ (bv_extract.spec m (m + n - 1) Z) =
          some (.bv n.toNat (c.extractLsb' m.toNat n.toNat)) := by
  have w := WT_extract_spec (i := m) (j := m + n - 1) wZ hZ (by omega) (by omega) (by omega)
  refine ⟨w, by simp [bv_extract.spec]; omega, fun W c h => ?_⟩
  rw [eval_extract_spec w h, Val_bv_extract_congr (k' := n.toNat) (by omega)]

/-- The low part of a bit-vector of width [n + m]. -/
theorem extract_lo {FS ρ} {Z : Term} {n m : Int} (hn : 0 < n) (hm : 0 < m) (wZ : Z.WT)
    (hZ : Z.ty = .bitVector (n + m)) :
    (bv_extract.spec 0 (m - 1) Z).WT ∧ (bv_extract.spec 0 (m - 1) Z).ty = .bitVector m ∧
      ∀ W (c : BitVec W), eval FS ρ Z = some (.bv W c) →
        eval FS ρ (bv_extract.spec 0 (m - 1) Z) =
          some (.bv m.toNat (c.extractLsb' 0 m.toNat)) := by
  have w := WT_extract_spec (i := 0) (j := m - 1) wZ hZ (by omega) (by omega) (by omega)
  refine ⟨w, by simp [bv_extract.spec], fun W c h => ?_⟩
  rw [eval_extract_spec w h, Val_bv_extract_congr (k' := m.toNat) (by omega)]; rfl

/-- An equality with a concatenation, split into its two parts. -/
theorem Refines.eq_concat {FS : FloatSem} {Z l r EL ER : Term} {T : Ty}
    (sL : ∀ n m : Int, 0 < n → 0 < m → l.ty = .bitVector n → r.ty = .bitVector m → Z.WT →
      Z.ty = .bitVector (n + m) →
      EL.WT ∧ EL.ty = .bitVector n ∧ ER.WT ∧ ER.ty = .bitVector m)
    (eL : ∀ n m : Int, 0 < n → 0 < m → l.ty = .bitVector n → r.ty = .bitVector m → Z.WT →
      Z.ty = .bitVector (n + m) → ∀ ρ W (c : BitVec W), eval FS ρ Z = some (.bv W c) →
      eval FS ρ EL = some (.bv n.toNat (c.extractLsb' m.toNat n.toNat)) ∧
      eval FS ρ ER = some (.bv m.toNat (c.extractLsb' 0 m.toNat))) :
    Refines FS (sem_eq.spec Z (.mk (.binop .bvConcat l r) T))
      (b_and.spec (sem_eq.spec EL l) (sem_eq.spec ER r)) := by
  refine Refines.eq_and (fun hT w1 w2 => ?_) (fun ρ x y hT w1 w2 hx hy => ?_)
  · obtain ⟨n, m, hn, hm, hl, hr, hT2, wl, wr⟩ := WT_concat.1 w2
    simp only [Term.ty_mk] at hT
    obtain ⟨k1, k2, k3, k4⟩ := sL n m hn hm hl hr w1 (by rw [hT, hT2])
    exact ⟨by rw [k2, hl], k1, wl, by rw [k4, hr], k3, wr⟩
  · obtain ⟨n, m, hn, hm, hl, hr, hT2, wl, wr⟩ := WT_concat.1 w2
    simp only [Term.ty_mk] at hT
    have hZ : Z.ty = .bitVector (n + m) := by rw [hT, hT2]
    obtain ⟨_, c, rfl⟩ := eval_bv_of_ty hx (Or.inl hZ)
    obtain ⟨a, b, x1, y1, e1, e2, rfl⟩ := eval_concat_some w2 hy
    obtain ⟨rfl, _⟩ := eval_bv_ty e1 hl
    obtain ⟨rfl, _⟩ := eval_bv_ty e2 hr
    obtain ⟨k1, k2⟩ := eL n m hn hm hl hr w1 hZ ρ _ c hx
    exact ⟨_, _, _, _, k1, e1, k2, e2, val_concat_iff c x1 y1 (by omega)⟩

theorem Refines.and_eq_symm {FS : FloatSem} {a b c d : Term} :
    Refines FS (b_and.spec (sem_eq.spec a b) (sem_eq.spec c d))
      (b_and.spec (sem_eq.spec b a) (sem_eq.spec d c)) :=
  Refines.binop Refines.eq_symm Refines.eq_symm (fun _ => rfl)


theorem Refines.eq_retype {FS : FloatSem} {a b : Term} :
    Refines FS (sem_eq.spec a b) (sem_eq.spec (.mk a.kind b.ty) b) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · have ⟨h1, _, _⟩ := WT_sem_eq.1 w
    cases a; simp only [Term.ty_mk, Term.kind_mk] at h1 ⊢; subst h1; exact ⟨w, rfl⟩
  · have ⟨h1, _, _⟩ := WT_sem_eq.1 w
    cases a; simp only [Term.ty_mk, Term.kind_mk] at h1 ⊢; subst h1; exact e


theorem nat_and_mask_eq_zero_iff {z N K : Nat} (hz : z < 2^(N+K)) :
    z &&& ((2^K - 1) * 2^N) = 0 ↔ z < 2^N := by
  rw [← Nat.shiftLeft_eq]
  constructor
  · intro h
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    cases hb : z.testBit i
    · rfl
    have hik : i < N + K := by
      have := Nat.ge_two_pow_of_testBit hb
      refine Nat.lt_of_not_le fun hc => ?_
      have : 2^(N+K) ≤ 2^i := Nat.pow_le_pow_right (by omega) hc
      omega
    have := congrArg (fun x => x.testBit i) h
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit, hb,
      Nat.testBit_two_pow_sub_one] at this
    simp at this
    omega
  · intro h
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit]
    by_cases hi : i < N
    · simp; omega
    · have : z.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [this]

theorem zland_mask_eq_zero_iff {z n k : Int} (hn : 0 ≤ n) (hk : 0 ≤ k) (h0 : 0 ≤ z)
    (h1 : z < 2 ^ (n + k).toNat) :
    zland z (zshiftl (zshiftl 1 k - 1) n) = 0 ↔ z < 2 ^ n.toNat := by
  obtain ⟨Z, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  have hm : zshiftl (zshiftl 1 k - 1) n = (((2 ^ k.toNat - 1) * 2 ^ n.toNat : Nat) : Int) := by
    have := Nat.one_le_two_pow (n := k.toNat)
    simp only [zshiftl, Int.one_mul]
    rw [Int.natCast_mul, Int.natCast_sub this]
    simp
  rw [hm]
  show Int.ofNat (Z &&& _) = 0 ↔ _
  have h1' : Z < 2 ^ (n.toNat + k.toNat) := by
    have : (n + k).toNat = n.toNat + k.toNat := by omega
    rw [this] at h1; exact_mod_cast h1
  rw [Int.ofNat_eq_natCast, Int.natCast_eq_zero, nat_and_mask_eq_zero_iff h1']
  constructor <;> intro h <;> exact_mod_cast h

theorem val_bv_eq_iff {A B : Nat} (x : BitVec A) (y : BitVec B) (h : A = B) :
    Val.bv A x = Val.bv B y ↔ x.toNat = y.toNat := by
  subst h; simp [BitVec.toNat_inj]

theorem toNat_of_val_bv_eq {A B : Nat} {x : BitVec A} {y : BitVec B} (h : Val.bv A x = Val.bv B y) :
    x.toNat = y.toNat := by cases h; rfl

theorem toNat_ofInt_of_range {w : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ w) :
    ((BitVec.ofInt w z).toNat : Int) = z := by
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt h0 (by exact_mod_cast h1)]
  omega


theorem zland_notmask_zero {zn mask F : Int} {c : Nat} (h0 : 0 ≤ zn) (hm : 0 ≤ mask)
    (hF : 0 ≤ F) (h : zn.toNat = mask.toNat &&& c) :
    zland zn (zland (zlognot mask) F) = 0 := by
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  obtain ⟨Mk, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  obtain ⟨Fn, rfl⟩ := Int.eq_ofNat_of_zero_le hF
  have hl : zlognot (Mk : Int) = Int.negSucc Mk := by
    rw [zlognot, Int.negSucc_eq]; omega
  rw [hl]
  show Int.ofNat (N &&& Nat.bitwise (fun a b => !a && b) Mk Fn) = 0
  simp only [Int.toNat_natCast] at h
  subst h
  rw [Int.ofNat_eq_natCast, Int.natCast_eq_zero]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_bitwise rfl]
  cases Mk.testBit i <;> simp

theorem Refines.eq_and_mask {FS : FloatSem} {zn mask sz : Int} {Tn Tm T : Ty} {A B : Term}
    (hmask : Term.mk (.bitVec mask) Tm = A ∨ Term.mk (.bitVec mask) Tm = B)
    (hsz : sz = size_of_ty Tn ∨ sz = size_of_ty T)
    (hc : (!decide (zland zn (zland (zlognot mask) (zshiftl 1 sz - 1)) = 0)) = true) :
    Refines FS (sem_eq.spec (.mk (.bitVec zn) Tn) (.mk (.binop .bitAnd A B) T)) v_false := by
  refine Refines.eq_const (fun _ _ _ => by simp) (fun ρ x y hT w1 w2 hx hy => ?_)
  simp only [Term.ty_mk] at hT; subst hT
  obtain ⟨⟨W', hW, hA⟩, hB, hT2, wA, wB⟩ := (WT_bvbin (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).1 w2
  have hs : sz = W' := by rcases hsz with rfl | rfl <;> rw [hT2, hA] <;> rfl
  subst hs
  rw [eval_binop w2] at hy; simp only [evBinop] at hy
  obtain ⟨m, a, b, ha, hb, hab⟩ := bvBin_eq_some.1 hy
  simp only [Option.some.injEq] at hab; subst hab
  obtain ⟨W, _, hTn, zn0, zn1, e⟩ := eval_bitVec_range (FS := FS) (ρ := ρ) w1
  rw [e] at hx; cases hx
  simp only [eval_v_false, Option.some.injEq, Val.bool.injEq, Bool.false_eq,
    decide_eq_false_iff_not]
  intro heq
  have ht := toNat_of_val_bv_eq heq
  rw [BitVec.toNat_and] at ht
  have hzn : (BitVec.ofInt W zn).toNat = zn.toNat := by
    have := toNat_ofInt_of_range (w := W) zn0 zn1; omega
  rw [hzn] at ht
  have hF : 0 ≤ zshiftl 1 sz - 1 := by
    simp only [zshiftl, Int.one_mul]
    have := two_pow_pos' sz.toNat; omega
  have hz : zland zn (zland (zlognot mask) (zshiftl 1 sz - 1)) = 0 := by
    rcases hmask with rfl | rfl
    · obtain ⟨rfl, m0, m1, _⟩ := eval_lit_bv wA ha
      have := toNat_ofInt_of_range (w := m) m0 m1
      exact zland_notmask_zero zn0 m0 hF (c := b.toNat) (by rw [ht]; congr 1; omega)
    · obtain ⟨rfl, m0, m1, _⟩ := eval_lit_bv wB hb
      have := toNat_ofInt_of_range (w := m) m0 m1
      exact zland_notmask_zero zn0 m0 hF (c := a.toNat)
        (by rw [ht, Nat.and_comm]; congr 1; omega)
  simp [hz] at hc


/-- The integer that a bit-vector stands for, in a signedness. -/
def iv (s : Bool) {w : Nat} (x : BitVec w) : Int := if s then x.toInt else (x.toNat : Int)

theorem iv_inj {s : Bool} {w : Nat} {a b : BitVec w} : iv s a = iv s b ↔ a = b := by
  cases s
  · simp only [iv, Bool.false_eq_true, ite_false]
    exact ⟨fun h => BitVec.eq_of_toNat_eq (by omega), fun h => by rw [h]⟩
  · simp [iv, BitVec.toInt_inj]

theorem iv_zero {s : Bool} {w : Nat} : iv s (0 : BitVec w) = 0 := by
  cases s <;> simp [iv, BitVec.toInt_zero]

theorem two_pow_pred {w : Nat} (hw : 0 < w) : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := by
  have : w = (w - 1) + 1 := by omega
  conv => lhs; rw [this]
  rw [Int.pow_succ]; omega

theorem iv_range {s : Bool} {w : Nat} (x : BitVec w) :
    (if s then -2 ^ (w - 1) ≤ iv s x ∧ iv s x < 2 ^ (w - 1)
      else 0 ≤ iv s x ∧ iv s x < 2 ^ w) := by
  cases s
  · simp only [iv, Bool.false_eq_true, ite_false]
    have := x.isLt
    exact ⟨by omega, by exact_mod_cast this⟩
  · simp only [iv, ite_true]
    exact ⟨BitVec.le_toInt x, BitVec.toInt_lt⟩

theorem iv_ofInt {s : Bool} {w : Nat} (hw : 0 < w) {q : Int}
    (h : if s then -2 ^ (w - 1) ≤ q ∧ q < 2 ^ (w - 1) else 0 ≤ q ∧ q < 2 ^ w) :
    iv s (BitVec.ofInt w q) = q := by
  cases s
  · simp only [Bool.false_eq_true, ite_false] at h
    simp only [iv, Bool.false_eq_true, ite_false]
    exact toNat_ofInt_of_range h.1 h.2
  · simp only [ite_true] at h
    simp only [iv, ite_true, BitVec.toInt_ofInt]
    have := two_pow_pred hw
    apply Int.bmod_eq_of_le_mul_two <;> push_cast <;> omega

theorem bv_to_z_lit {s : Bool} {W z : Int} (hW : 0 < W) (h0 : 0 ≤ z) (h1 : z < 2 ^ W.toNat) :
    bv_to_z s W z = iv s (BitVec.ofInt W.toNat z) := by
  have hr := toNat_ofInt_of_range (w := W.toNat) h0 h1
  cases s
  · simp only [bv_to_z, iv, Bool.false_eq_true, ite_false]; omega
  · simp only [bv_to_z, signed_extract, zasr, iv, ite_true, Int.toNat_zero, Int.pow_zero,
      Int.ediv_one]
    rw [Int.emod_eq_of_lt h0 (by exact_mod_cast h1), BitVec.toInt_eq_toNat_cond]
    have := two_pow_pred (w := W.toNat) (by omega)
    have h2 : (((2 ^ W.toNat : Nat)) : Int) = 2 * 2 ^ (W.toNat - 1) := by push_cast; exact this
    have h3 : ((2 : Nat) : Int) ^ W.toNat = 2 * 2 ^ (W.toNat - 1) := by push_cast; exact this
    split <;> split <;> omega

theorem iv_mul {ck : Checked} (hck : is_checked ck = true) {w : Nat} {a b : BitVec w}
    (hf : ((ck.signed && a.smulOverflow b) || (ck.unsigned && a.umulOverflow b)) = false) :
    iv (!ck.unsigned) (a * b) = iv (!ck.unsigned) a * iv (!ck.unsigned) b := by
  obtain ⟨cs, cu⟩ := ck
  simp only [is_checked] at hck
  cases cu
  · simp only [Bool.or_false, Bool.false_and] at hck hf
    subst hck
    simp only [Bool.true_and] at hf
    simp only [iv, Bool.not_false, ite_true]
    exact BitVec.toInt_mul_of_not_smulOverflow (by simp [hf])
  · simp only [Bool.true_and, Bool.or_eq_false_iff] at hf
    simp only [iv, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [BitVec.toNat_mul_of_not_umulOverflow (by simp [hf.2])]; push_cast; rfl


/-- Whether a quotient fits in the signedness of the [mul_const] rule of [sem_eq]. -/
def mulFits (signed : Bool) (sz q : Int) : Bool :=
  (if signed
  then (let h := (zshiftl (1 : Int) (sz - (1 : Int)));
       ((decide ((- h) ≤ q)) && (decide (q < h))))
  else ((decide ((0 : Int) ≤ q)) && (decide (q < (zshiftl (1 : Int) sz)))))

/-- The result of the [mul_const] rule of [sem_eq]. -/
def mulConstRes (O : Ops) (signed : Bool) (sz m n : Int) (x : Term) : Term :=
  (if (decide (m = (0 : Int)))
  then (of_bool (decide (n = (0 : Int))))
  else (if (decide (n = (0 : Int)))
       then (O.sem_eq x (bv_zero sz))
       else (if (divisible n m)
            then (if mulFits signed sz (tdiv n m)
                 then (O.sem_eq x (mk_masked sz (tdiv n m)))
                 else v_false)
            else v_false)))

theorem mul_const_key {FS : FloatSem} {zn zm : Int} {ck : Checked} {x L R : Term} {Tn Tm T : Ty}
    (hLR : (L = .mk (.bitVec zm) Tm ∧ R = x) ∨ (L = x ∧ R = .mk (.bitVec zm) Tm))
    (hck : is_checked ck = true)
    (hT : (Term.mk (.bitVec zn) Tn).ty = (Term.mk (.binop (.mul ck) L R) T).ty)
    (w1 : (Term.mk (.bitVec zn) Tn).WT) (w2 : (Term.mk (.binop (.mul ck) L R) T).WT) :
    ∃ W : Int, 0 < W ∧ x.ty = .bitVector W ∧ x.WT ∧ size x = W ∧ 0 ≤ zn ∧ zn < 2 ^ W.toNat ∧
      0 ≤ zm ∧ zm < 2 ^ W.toNat ∧ ∀ ρ xv yv, eval FS ρ (.mk (.bitVec zn) Tn) = some xv →
        eval FS ρ (.mk (.binop (.mul ck) L R) T) = some yv →
        ∃ a, eval FS ρ x = some (.bv W.toNat a) ∧
          (xv = yv ↔ iv (!ck.unsigned) (BitVec.ofInt W.toNat zn) =
            iv (!ck.unsigned) (BitVec.ofInt W.toNat zm) * iv (!ck.unsigned) a) := by
  obtain ⟨⟨W, hW, hL⟩, hR, hT2, wL, wR⟩ :=
    (WT_bvbin (Or.inr (Or.inr (Or.inl ⟨ck, rfl⟩)))).1 w2
  simp only [Term.ty_mk] at hT
  have htn : Tn = .bitVector W := by rw [hT, hT2, hL]
  subst htn
  have hlit : ∀ {z : Int} {T' : Ty}, T' = .bitVector W → (Term.mk (.bitVec z) T').WT →
      0 ≤ z ∧ z < 2 ^ W.toNat := by
    intro z T' h w
    obtain ⟨k, _, hk, z0, z1⟩ := WT_bitVec.1 w
    have : k = W.toNat := by rcases hk with hk | hk <;> rw [hk] at h <;> simp at h; omega
    subst this; exact ⟨z0, z1⟩
  obtain ⟨n0, n1⟩ := hlit rfl w1
  have hx : x.ty = .bitVector W := by
    rcases hLR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hR, hL]
    · exact hL
  have wx : x.WT := by rcases hLR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hm : Term.WT (.mk (.bitVec zm) (.bitVector W)) ∧ 0 ≤ zm ∧ zm < 2 ^ W.toNat := by
    rcases hLR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [Term.ty_mk] at hL; subst hL; exact ⟨wL, hlit rfl wL⟩
    · simp only [Term.ty_mk] at hR; rw [hR, hL] at wR; exact ⟨wR, hlit rfl wR⟩
  obtain ⟨wm, m0, m1⟩ := hm
  refine ⟨W, hW, hx, wx, by simp [size, hx], n0, n1, m0, m1, fun ρ xv yv ex ey => ?_⟩
  rw [eval_lit' w1] at ex; cases ex
  rw [eval_binop w2] at ey; simp only [evBinop] at ey
  obtain ⟨k, a, b, ea, eb, hf, rfl⟩ := checkedOp_eq_some.1 ey
  rcases hLR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [Term.ty_mk] at hL; subst hL
    rw [eval_lit' wm] at ea; simp only [Option.some.injEq, Val.bv.injEq] at ea
    obtain ⟨rfl, ea⟩ := ea; cases ea
    refine ⟨b, eb, ?_⟩
    rw [← iv_mul hck hf, iv_inj]; simp
  · obtain ⟨rfl, _⟩ := eval_bv_ty ea hL
    simp only [Term.ty_mk] at hR; rw [hR, hL] at eb
    rw [eval_lit' wm] at eb; simp only [Option.some.injEq, Val.bv.injEq, heq_eq_eq, true_and] at eb
    subst eb
    refine ⟨a, ea, ?_⟩
    rw [Int.mul_comm, ← iv_mul hck hf, iv_inj]; simp

theorem Refines.eq_mul_const {FS : FloatSem} {O : Ops} (hO : O.Sound FS) {zn zm : Int}
    {ck : Checked} {x L R : Term} {Tn Tm T : Ty}
    (hLR : (L = .mk (.bitVec zm) Tm ∧ R = x) ∨ (L = x ∧ R = .mk (.bitVec zm) Tm))
    (hck : is_checked ck = true) :
    Refines FS (sem_eq.spec (.mk (.bitVec zn) Tn) (.mk (.binop (.mul ck) L R) T))
      (mulConstRes O (!ck.unsigned) (size x) (bv_to_z (!ck.unsigned) (size x) zm)
        (bv_to_z (!ck.unsigned) (size x) zn) x) := by
  have conv : ∀ {W : Int}, 0 < W → size x = W → 0 ≤ zn → zn < 2 ^ W.toNat → 0 ≤ zm →
      zm < 2 ^ W.toNat →
      bv_to_z (!ck.unsigned) (size x) zm = iv (!ck.unsigned) (BitVec.ofInt W.toNat zm) ∧
      bv_to_z (!ck.unsigned) (size x) zn = iv (!ck.unsigned) (BitVec.ofInt W.toNat zn) := by
    intro W hW hs n0 n1 m0 m1
    rw [hs]; exact ⟨bv_to_z_lit hW m0 m1, bv_to_z_lit hW n0 n1⟩
  unfold mulConstRes
  split
  · rename_i hM
    refine Refines.eq_const (fun _ _ _ => by simp) (fun ρ xv yv hT w1 w2 hx hy => ?_)
    obtain ⟨W, hW, _, _, hs, n0, n1, m0, m1, sem⟩ := mul_const_key (FS := FS) hLR hck hT w1 w2
    obtain ⟨a, _, hiff⟩ := sem ρ xv yv hx hy
    obtain ⟨cM, cN⟩ := conv hW hs n0 n1 m0 m1
    simp only [decide_eq_true_eq, cM] at hM
    rw [eval_of_bool, cN, hiff, hM, Int.zero_mul]
    simp only [Option.some.injEq, Val.bool.injEq]; exact decide_eq_decide.2 Iff.rfl
  split
  · rename_i hM hN
    refine Refines.trans ?_ (hO.sem_eq x _)
    refine Refines.eq_eq (fun hT w1 w2 => ?_) (fun ρ xv yv hT w1 w2 hx hy => ?_)
    · obtain ⟨W, hW, hx, wx, hs, -⟩ := mul_const_key (FS := FS) hLR hck hT w1 w2
      rw [hs]; exact ⟨by simp [hx], wx, bv_zero_WT' hW⟩
    · obtain ⟨W, hW, _, _, hs, n0, n1, m0, m1, sem⟩ := mul_const_key (FS := FS) hLR hck hT w1 w2
      obtain ⟨a, ea, hiff⟩ := sem ρ xv yv hx hy
      obtain ⟨cM, cN⟩ := conv hW hs n0 n1 m0 m1
      simp only [decide_eq_true_eq, cM, cN] at hM hN
      refine ⟨_, _, ea, by rw [hs]; exact eval_bv_zero'' hW, ?_⟩
      rw [hiff, hN]
      simp only [Val.bv.injEq, heq_eq_eq, true_and]
      rw [← iv_inj (s := !ck.unsigned), iv_zero]
      constructor
      · intro h; exact (Int.mul_eq_zero.1 h.symm).resolve_left hM
      · intro h; rw [h, Int.mul_zero]
  split
  · rename_i hM hN hd
    simp only [decide_eq_true_eq] at hM hN
    split
    · rename_i hfit
      refine Refines.trans ?_ (hO.sem_eq x _)
      refine Refines.eq_eq (fun hT w1 w2 => ?_) (fun ρ xv yv hT w1 w2 hx hy => ?_)
      · obtain ⟨W, hW, hx, wx, hs, -⟩ := mul_const_key (FS := FS) hLR hck hT w1 w2
        rw [hs]; exact ⟨by simp [hx], wx, mk_masked_WT hW⟩
      · obtain ⟨W, hW, _, _, hs, n0, n1, m0, m1, sem⟩ := mul_const_key (FS := FS) hLR hck hT w1 w2
        obtain ⟨a, ea, hiff⟩ := sem ρ xv yv hx hy
        obtain ⟨cM, cN⟩ := conv hW hs n0 n1 m0 m1
        rw [cM] at hM; rw [cN] at hN; rw [cM, cN] at hd hfit ⊢
        rw [hs] at hfit ⊢
        refine ⟨_, _, ea, eval_mk_masked hW, ?_⟩
        have hdvd : iv (!ck.unsigned) (BitVec.ofInt W.toNat zm) ∣
            iv (!ck.unsigned) (BitVec.ofInt W.toNat zn) := by simpa [divisible] using hd
        have hq := Int.mul_tdiv_cancel' hdvd
        have hrange : iv (!ck.unsigned) (BitVec.ofInt W.toNat
            (tdiv (iv (!ck.unsigned) (BitVec.ofInt W.toNat zn))
              (iv (!ck.unsigned) (BitVec.ofInt W.toNat zm)))) =
            tdiv (iv (!ck.unsigned) (BitVec.ofInt W.toNat zn))
              (iv (!ck.unsigned) (BitVec.ofInt W.toNat zm)) := by
          apply iv_ofInt (by omega)
          simp only [mulFits, zshiftl, Int.one_mul] at hfit
          have e1 : (W - 1).toNat = W.toNat - 1 := by omega
          rw [e1] at hfit
          revert hfit; generalize (!ck.unsigned) = sg; cases sg <;> intro hfit <;> simpa using hfit
        rw [hiff]
        simp only [Val.bv.injEq, heq_eq_eq, true_and]
        rw [← iv_inj (s := !ck.unsigned), hrange]
        simp only [tdiv] at hq ⊢
        constructor
        · intro h; rw [h, Int.mul_tdiv_cancel_left _ hM]
        · intro h; rw [h]; exact hq.symm
    · rename_i hfit
      refine Refines.eq_const (fun _ _ _ => by simp) (fun ρ xv yv hT w1 w2 hx hy => ?_)
      obtain ⟨W, hW, _, _, hs, n0, n1, m0, m1, sem⟩ := mul_const_key (FS := FS) hLR hck hT w1 w2
      obtain ⟨a, ea, hiff⟩ := sem ρ xv yv hx hy
      obtain ⟨cM, cN⟩ := conv hW hs n0 n1 m0 m1
      rw [cM] at hM; rw [cN] at hN; rw [cM, cN] at hd hfit
      rw [hs] at hfit
      simp only [eval_v_false, Option.some.injEq, Val.bool.injEq, Bool.false_eq,
        decide_eq_false_iff_not, hiff]
      intro h
      apply hfit
      rw [h]; simp only [mulFits, tdiv, Int.mul_tdiv_cancel_left _ hM, zshiftl, Int.one_mul]
      have e1 : (W - 1).toNat = W.toNat - 1 := by omega
      rw [e1]
      have := iv_range (s := !ck.unsigned) a
      revert this; generalize (!ck.unsigned) = sg; cases sg <;> intro this <;> simpa using this
  · rename_i hM hN hd
    refine Refines.eq_const (fun _ _ _ => by simp) (fun ρ xv yv hT w1 w2 hx hy => ?_)
    obtain ⟨W, hW, _, _, hs, n0, n1, m0, m1, sem⟩ := mul_const_key (FS := FS) hLR hck hT w1 w2
    obtain ⟨a, ea, hiff⟩ := sem ρ xv yv hx hy
    obtain ⟨cM, cN⟩ := conv hW hs n0 n1 m0 m1
    rw [cM, cN] at hd
    simp only [eval_v_false, Option.some.injEq, Val.bool.injEq, Bool.false_eq,
      decide_eq_false_iff_not, hiff]
    intro h
    apply hd
    rw [h]; simp [divisible]

end EqL
end Bvr
