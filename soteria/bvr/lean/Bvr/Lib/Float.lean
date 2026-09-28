import Bvr.Lib.Lit

/-! Floats, pointers and equalities, by evaluation. -/

namespace Bvr.Lib

open Classical


/-! ## Equality -/

theorem WT_eq {a b t} : (Term.mk (.binop .eq a b) t).WT ↔
    a.ty = b.ty ∧ t = .bool ∧ a.WT ∧ b.WT := by
  simp [Term.WT, Binop.WT, and_assoc]

theorem eval_eq_of {FS ρ a b t x y} (w : (Term.mk (.binop .eq a b) t).WT)
    (ha : eval FS ρ a = some x) (hb : eval FS ρ b = some y) :
    eval FS ρ (.mk (.binop .eq a b) t) = some (.bool (decide (x = y))) := by
  rw [eval_binop w, ha, hb]; simp [evBinop]

theorem WT_sem_eq {a b} : (sem_eq.spec a b).WT ↔ a.ty = b.ty ∧ a.WT ∧ b.WT := by
  simp [sem_eq.spec, WT_eq]

@[simp] theorem sem_eq_ty {a b} : (sem_eq.spec a b).ty = .bool := rfl

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


theorem WT_float {f t} : (Term.mk (.float f) t).WT ↔ t = .float f.prec ∧ f.bits < 2 ^ f.prec.size := by
  simp [Term.WT]

theorem eval_float {FS ρ f t} (h : (Term.mk (.float f) t).WT) :
    eval FS ρ (.mk (.float f) t) = some f.sem := by
  rw [eval_eq_ev h, ev]

theorem FloatLit.WF_of_WT {f t} (h : (Term.mk (.float f) t).WT) : f.WF := (WT_float.1 h).2

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

/-! ## Floats -/

end Bvr.Lib

namespace Bvr.FBits

variable {p : Prec}

@[simp] theorem eq_self' (x : FBits p) : x.eq x = !x.isNaN := by
  unfold eq; cases x.isNaN <;> simp

theorem not_isNaN_of_isZero {x : FBits p} (h : x.isZero = true) : x.isNaN = false := by
  simp only [isZero, isNaN, Bool.and_eq_true, beq_iff_eq] at h ⊢
  simp [h.2]

theorem eq_of_isNaN_left {x : FBits p} (y : FBits p) (h : x.isNaN = true) : x.eq y = false := by
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

end Bvr.FBits

namespace Bvr.Lib

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

/-! ## Bit-vector operations -/

/-! ## If-then-else -/

theorem WT_ite {g a b t} : (Term.mk (.triop .ite g a b) t).WT ↔
    g.ty = .bool ∧ b.ty = a.ty ∧ t = a.ty ∧ g.WT ∧ a.WT ∧ b.WT := by
  simp [Term.WT, Triop.WT, and_assoc]

section
open Classical
variable {FS : FloatSem}

/-! ## Equalities at any type -/

theorem eval_eq {ρ a b t} (w : (Term.mk (.binop .eq a b) t).WT) :
    eval FS ρ (.mk (.binop .eq a b) t) =
      match eval FS ρ a, eval FS ρ b with
      | some x, some y => some (.bool (decide (x = y)))
      | _, _ => none := by
  rw [eval_binop w]; cases eval FS ρ a <;> cases eval FS ρ b <;> rfl

theorem eval_ite_eq {ρ g a b t} (w : (Term.mk (.triop .ite g a b) t).WT) :
    eval FS ρ (.mk (.triop .ite g a b) t) =
      match evalB FS ρ g with
      | some true => eval FS ρ a
      | some false => eval FS ρ b
      | none => none := by
  rw [eval_ite w, eval_bool' (WT_ite.1 w).1]
  rcases evalB FS ρ g with _ | _ | _ <;> rfl

theorem Refines.eq_same {v : Term} {t : Ty} :
    Refines FS (.mk (.binop .eq v v) t) v_true := by
  refine Refines.intro (fun w => ?_) (fun ρ x w _ e => ?_)
  · simp [(WT_eq.1 w).2.1]
  · rw [eval_eq w] at e
    cases h : eval FS ρ v <;> simp_all

theorem Refines.eq_ite_ite {g l r l' r' : Term} {T T' t : Ty} :
    Refines FS (.mk (.binop .eq (.mk (.triop .ite g l r) T) (.mk (.triop .ite g l' r') T')) t)
      (.mk (.triop .ite g (.mk (.binop .eq l l') .bool) (.mk (.binop .eq r r') .bool)) .bool) := by
  refine Refines.intro (fun w => ?_) (fun ρ x w w' e => ?_)
  · simp only [WT_eq, WT_ite, Term.ty_mk, Ty.sort_eq] at *
    grind
  · have ⟨_, _, w1, w2⟩ := WT_eq.1 w
    have ⟨_, _, _, _, wa, wb⟩ := WT_ite.1 w'
    rw [eval_eq w, eval_ite_eq w1, eval_ite_eq w2] at e
    rw [eval_ite_eq w', eval_eq wa, eval_eq wb]
    generalize evalB FS ρ g = o at e ⊢
    rcases o with _ | _ | _ <;> simp only at e ⊢ <;> first | exact e | simp at e

theorem Refines.eq_ite_l {g l r c : Term} {T t : Ty} :
    Refines FS (.mk (.binop .eq (.mk (.triop .ite g l r) T) c) t)
      (.mk (.triop .ite g (.mk (.binop .eq l c) .bool) (.mk (.binop .eq r c) .bool)) .bool) := by
  refine Refines.intro (fun w => ?_) (fun ρ x w w' e => ?_)
  · simp only [WT_eq, WT_ite, Term.ty_mk, Ty.sort_eq] at *
    grind
  · have ⟨_, _, w1, w2⟩ := WT_eq.1 w
    have ⟨_, _, _, _, wa, wb⟩ := WT_ite.1 w'
    rw [eval_eq w, eval_ite_eq w1] at e
    rw [eval_ite_eq w', eval_eq wa, eval_eq wb]
    generalize evalB FS ρ g = o at e ⊢
    rcases o with _ | _ | _ <;> simp only at e ⊢ <;> first | exact e | simp at e

theorem Refines.eq_ite_r {g l r c : Term} {T t : Ty} :
    Refines FS (.mk (.binop .eq c (.mk (.triop .ite g l r) T)) t)
      (.mk (.triop .ite g (.mk (.binop .eq c l) .bool) (.mk (.binop .eq c r) .bool)) .bool) := by
  refine Refines.intro (fun w => ?_) (fun ρ x w w' e => ?_)
  · simp only [WT_eq, WT_ite, Term.ty_mk, Ty.sort_eq] at *
    grind
  · have ⟨_, _, w1, w2⟩ := WT_eq.1 w
    have ⟨_, _, _, _, wa, wb⟩ := WT_ite.1 w'
    rw [eval_eq w, eval_ite_eq w2] at e
    rw [eval_ite_eq w', eval_eq wa, eval_eq wb]
    generalize evalB FS ρ g = o at e ⊢
    rcases o with _ | _ | _ <;> simp only at e ⊢ <;> first | exact e | simp at e



theorem Refines.eq_lits {z1 z2 : Int} {T1 T2 t : Ty} :
    Refines FS (.mk (.binop .eq (.mk (.bitVec z1) T1) (.mk (.bitVec z2) T2)) t)
      (of_bool (decide (to_z false (bv_of_lit (.mk (.bitVec z1) T1)) =
        to_z false (bv_of_lit (.mk (.bitVec z2) T2))))) := by
  refine Refines.intro (fun w => ?_) (fun ρ x w _ e => ?_)
  · simp [(WT_eq.1 w).2.1]
  · have ⟨hT, _, w1, w2⟩ := WT_eq.1 w
    simp only [Term.ty_mk] at hT; subst hT
    obtain ⟨n, hn, hT, h1, h2⟩ := WT_bitVec.1 w1
    obtain ⟨m, _, hT', h3, h4⟩ := WT_bitVec.1 w2
    obtain rfl : m = n := by
      have := size_of_ty_of_bits hT'; rw [size_of_ty_of_bits hT] at this; omega
    rw [eval_eq w, eval_bitVec' w1 hT, eval_bitVec' w2 hT] at e
    simp only [Int.toNat_natCast, Option.some.injEq] at e; subst e
    have e1 := toNat_ofInt_of_lt h1 h2
    have e2 := toNat_ofInt_of_lt h3 h4
    rcases hT with rfl | rfl <;>
      simp [bv_of_lit, size_of_ty, to_z, ← BitVec.toNat_inj, e1, e2] <;> omega

theorem Refines.eq_floats {f1 f2 : FloatLit} {T1 T2 t : Ty} :
    Refines FS (.mk (.binop .eq (.mk (.float f1) T1) (.mk (.float f2) T2)) t)
      (of_bool (f_bits_equal f1 f2)) := by
  refine Refines.intro (fun w => ?_) (fun ρ x w _ e => ?_)
  · simp [(WT_eq.1 w).2.1]
  · have ⟨hT, _, w1, w2⟩ := WT_eq.1 w
    rw [eval_eq w, eval_eq_ev w1, eval_eq_ev w2] at e
    simp only [Term.WT] at w1 w2
    simp only [ev, Option.some.injEq] at e; subst e
    simp only [Term.ty_mk, w1.1, w2.1, Ty.float.injEq] at hT
    obtain ⟨p1, b1⟩ := f1; obtain ⟨p2, b2⟩ := f2
    simp only at hT w1 w2; subst hT
    simp only [eval_of_bool, f_bits_equal, FloatLit.sem, FloatLit.val, Val.float.injEq, heq_eq_eq,
      true_and, FloatLit.mk.injEq, Option.some.injEq, Val.bool.injEq, decide_eq_decide]
    rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt w1.2,
      Nat.mod_eq_of_lt w2.2]

theorem eval_ptr_some {ρ l o t v} (h : (Term.mk (.ptr l o) t).WT)
    (e : eval FS ρ (.mk (.ptr l o) t) = some v) :
    ∃ n x y, eval FS ρ l = some (.bv n x) ∧ eval FS ρ o = some (.bv n y) ∧ v = .ptr n x y := by
  obtain ⟨_, _, _, _, _, wl, wo⟩ := id h
  rw [eval_eq_ev h] at e; simp only [ev] at e
  rw [← eval_eq_ev wl, ← eval_eq_ev wo] at e
  split at e
  · rename_i n x m y hl ho
    split at e
    · rename_i hmn; subst hmn; simp only [Option.some.injEq] at e; exact ⟨_, _, _, hl, ho, e.symm⟩
    · simp at e
  · simp at e

theorem Refines.eq_ptrs {l1 o1 l2 o2 : Term} {T T' t : Ty} :
    Refines FS (.mk (.binop .eq (.mk (.ptr l1 o1) T) (.mk (.ptr l2 o2) T')) t)
      (.mk (.binop .and_ (.mk (.binop .eq l1 l2) .bool) (.mk (.binop .eq o1 o2) .bool)) .bool) := by
  refine Refines.intro (fun w => ?_) (fun ρ x w w' e => ?_)
  · have ⟨hT, ht, w1, w2⟩ := WT_eq.1 w
    obtain ⟨n, hn, rfl, hl, ho, wl, wo⟩ := id w1
    obtain ⟨m, hm, rfl, hl', ho', wl', wo'⟩ := id w2
    simp only [Term.ty_mk, Ty.pointer.injEq] at hT; subst hT
    simp_all [WT_binop, Binop.WT]
  · have ⟨hT, _, w1, w2⟩ := WT_eq.1 w
    have ⟨_, wa, wb⟩ := WT_binop.1 w'
    rw [eval_eq w] at e
    cases h1 : eval FS ρ (.mk (.ptr l1 o1) T) <;> cases h2 : eval FS ρ (.mk (.ptr l2 o2) T') <;>
      rw [h1, h2] at e <;> simp only [reduceCtorEq, Option.some.injEq] at e
    obtain ⟨n, x1, y1, a1, b1, rfl⟩ := eval_ptr_some w1 h1
    obtain ⟨m, x2, y2, a2, b2, rfl⟩ := eval_ptr_some w2 h2
    have s1 := eval_hasSort h1; have s2 := eval_hasSort h2
    simp only [Term.ty_mk] at hT s1 s2; subst hT e
    obtain rfl : m = n := by cases T <;> simp_all [Val.hasSort]; omega
    rw [eval_binop w', eval_eq wa, eval_eq wb, a1, a2, b1, b2]
    by_cases hx : x1 = x2 <;> by_cases hy : y1 = y2 <;> simp [evBinop, pand, hx, hy]

end

end Bvr.Lib
