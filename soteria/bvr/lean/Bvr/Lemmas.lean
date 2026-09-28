import Bvr.Statements

/-! Basic facts about evaluation, used by the rule proofs. -/

namespace Bvr

open Classical

theorem eval_WT {FS ρ t v} (h : eval FS ρ t = some v) : t.WT := by
  unfold eval at h; split at h <;> simp_all

theorem eval_eq_ev {FS ρ t} (h : t.WT) : eval FS ρ t = ev FS ρ t := by
  simp [eval, h]

/-- Types are matched exactly: [Ty.sort] is the identity. -/
@[simp] theorem Ty.sort_eq (t : Ty) : t.sort = t := rfl

theorem size_of_ty_of_bits {t : Ty} {n : Int} (h : t = .bitVector n ∨ t = .loc n) :
    size_of_ty t = n := by
  rcases h with rfl | rfl <;> rfl

@[simp] theorem size_of_ty_bitVector (n : Int) : size_of_ty (.bitVector n) = n := rfl
@[simp] theorem ty_eq (v : Term) : ty v = v.ty := rfl
@[simp] theorem kind_eq (v : Term) : kind v = v.kind := rfl
@[simp] theorem size_eq (v : Term) : size v = size_of_ty v.ty := rfl

end Bvr

namespace Bvr

open Classical

/-! ## Refinement of optional values -/

/-- [a] is poison or equal to [b]. -/
def OLe (a b : Option Val) : Prop := ∀ v, a = some v → b = some v

@[simp] theorem OLe.refl (a : Option Val) : OLe a a := fun _ h => h
@[simp] theorem OLe.none (a : Option Val) : OLe none a := fun _ h => by cases h

theorem Refines.trans {FS : FloatSem} {a b c : Term} (h1 : Refines FS a b)
    (h2 : Refines FS b c) : Refines FS a c := by
  refine ⟨fun w => ?_, fun ρ v e => h2.2 ρ v (h1.2 ρ v e)⟩
  obtain ⟨wb, sb⟩ := h1.1 w
  obtain ⟨wc, sc⟩ := h2.1 wb
  exact ⟨wc, sc.trans sb⟩

theorem Refines.syn {FS : FloatSem} {a b : Term} (h : Refines FS a b) (w : a.WT) :
    b.WT ∧ b.ty.sort = a.ty.sort := h.1 w

theorem Refines.sem {FS : FloatSem} {a b : Term} (h : Refines FS a b) (ρ : Env) :
    OLe (eval FS ρ a) (eval FS ρ b) := h.2 ρ

/-! ## Evaluation of well-typed nodes -/

theorem WT_unop {op a t} : (Term.mk (.unop op a) t).WT ↔ op.WT a.ty.sort t.sort ∧ a.WT := by
  simp [Term.WT]

theorem WT_binop {op a b t} :
    (Term.mk (.binop op a b) t).WT ↔ op.WT a.ty.sort b.ty.sort t.sort ∧ a.WT ∧ b.WT := by
  simp [Term.WT]

theorem WT_triop {op a b c t} :
    (Term.mk (.triop op a b c) t).WT ↔
      op.WT a.ty.sort b.ty.sort c.ty.sort t.sort ∧ a.WT ∧ b.WT ∧ c.WT := by
  simp [Term.WT]

theorem eval_unop {FS ρ op a t} (h : (Term.mk (.unop op a) t).WT) :
    eval FS ρ (.mk (.unop op a) t) = evUnop FS op (eval FS ρ a) := by
  rw [eval_eq_ev h, eval_eq_ev (WT_unop.1 h).2, ev]

theorem eval_binop {FS ρ op a b t} (h : (Term.mk (.binop op a b) t).WT) :
    eval FS ρ (.mk (.binop op a b) t) = evBinop FS op (eval FS ρ a) (eval FS ρ b) := by
  have := WT_binop.1 h
  rw [eval_eq_ev h, eval_eq_ev this.2.1, eval_eq_ev this.2.2, ev]

theorem eval_ite {FS ρ g a b t} (h : (Term.mk (.triop .ite g a b) t).WT) :
    eval FS ρ (.mk (.triop .ite g a b) t) =
      match eval FS ρ g with
      | some (.bool true) => eval FS ρ a
      | some (.bool false) => eval FS ρ b
      | _ => none := by
  have := WT_triop.1 h
  rw [eval_eq_ev h, eval_eq_ev this.2.1, eval_eq_ev this.2.2.1, eval_eq_ev this.2.2.2]
  simp only [ev]
  split <;> simp_all

theorem eval_fma {FS ρ a b c t} (h : (Term.mk (.triop .fma a b c) t).WT) :
    eval FS ρ (.mk (.triop .fma a b c) t) =
      evFma FS (eval FS ρ a) (eval FS ρ b) (eval FS ρ c) := by
  have := WT_triop.1 h
  rw [eval_eq_ev h, eval_eq_ev this.2.1, eval_eq_ev this.2.2.1, eval_eq_ev this.2.2.2, ev]

/-! ## Monotonicity of the operators in poison -/

@[simp] theorem evUnop_none {FS op} : evUnop FS op none = none := by cases op <;> rfl

theorem evUnop_mono {FS op a a'} (h : OLe a a') : OLe (evUnop FS op a) (evUnop FS op a') := by
  intro v e
  cases a with
  | none => cases op <;> simp [evUnop] at e
  | some x => rw [h x rfl]; exact e

theorem pand_eq_some {a b : Option Val} {v : Val} :
    pand a b = some v ↔
      (a = some (.bool false) ∧ v = .bool false) ∨ (b = some (.bool false) ∧ v = .bool false) ∨
        (a = some (.bool true) ∧ b = some (.bool true) ∧ v = .bool true) := by
  unfold pand; split <;> grind

theorem por_eq_some {a b : Option Val} {v : Val} :
    por a b = some v ↔
      (a = some (.bool true) ∧ v = .bool true) ∨ (b = some (.bool true) ∧ v = .bool true) ∨
        (a = some (.bool false) ∧ b = some (.bool false) ∧ v = .bool false) := by
  unfold por; split <;> grind

theorem pand_mono {a a' b b'} (ha : OLe a a') (hb : OLe b b') : OLe (pand a b) (pand a' b') := by
  intro v e
  rw [pand_eq_some] at *
  rcases e with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h1, h2, rfl⟩
  · exact Or.inl ⟨ha _ h, rfl⟩
  · exact Or.inr (Or.inl ⟨hb _ h, rfl⟩)
  · exact Or.inr (Or.inr ⟨ha _ h1, hb _ h2, rfl⟩)

theorem por_mono {a a' b b'} (ha : OLe a a') (hb : OLe b b') : OLe (por a b) (por a' b') := by
  intro v e
  rw [por_eq_some] at *
  rcases e with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h1, h2, rfl⟩
  · exact Or.inl ⟨ha _ h, rfl⟩
  · exact Or.inr (Or.inl ⟨hb _ h, rfl⟩)
  · exact Or.inr (Or.inr ⟨ha _ h1, hb _ h2, rfl⟩)


@[simp] theorem bvBin_none_l {f b} : bvBin f none b = none := by cases b <;> rfl
@[simp] theorem bvBin_none_r {f a} : bvBin f a none = none := by
  rcases a with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl
@[simp] theorem fBin_none_l {f b} : fBin f none b = none := by cases b <;> rfl
@[simp] theorem fBin_none_r {f a} : fBin f a none = none := by
  rcases a with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl

theorem evBinop_mono {FS op a a' b b'} (ha : OLe a a') (hb : OLe b b') :
    OLe (evBinop FS op a b) (evBinop FS op a' b') := by
  cases op
  case and_ => exact pand_mono ha hb
  case or_ => exact por_mono ha hb
  all_goals
    intro v e
    rcases a with _ | x
    · simp [evBinop, fArith, checkedOp] at e
    rcases b with _ | y
    · rcases x with _ | _ | _ | _ | _ | _ <;> simp [evBinop, fArith, checkedOp] at e
    rw [ha x rfl, hb y rfl]; exact e

theorem evFma_mono {FS a a' b b' c c'} (ha : OLe a a') (hb : OLe b b') (hc : OLe c c') :
    OLe (evFma FS a b c) (evFma FS a' b' c') := by
  intro v e
  rcases a with _ | x; · simp [evFma] at e
  rcases b with _ | y; · rcases x with _ | _ | _ | _ | _ | _ <;> simp [evFma] at e
  rcases c with _ | z
  · rcases x with _ | _ | _ | _ | _ | _ <;> rcases y with _ | _ | _ | _ | _ | _ <;>
      simp [evFma] at e
  rw [ha x rfl, hb y rfl, hc z rfl]; exact e

/-! ## Congruence: refining the children of a node refines the node -/

/-- To prove a refinement, one may use the syntactic part in the semantic one. -/
theorem Refines.intro {FS : FloatSem} {a b : Term} (syn : a.WT → b.WT ∧ b.ty.sort = a.ty.sort)
    (sem : ∀ ρ v, a.WT → b.WT → eval FS ρ a = some v → eval FS ρ b = some v) :
    Refines FS a b :=
  ⟨syn, fun ρ v e => sem ρ v (eval_WT e) (syn (eval_WT e)).1 e⟩

theorem Refines.unop {FS op a a' t t'} (ha : Refines FS a a')
    (ht : (Term.mk (.unop op a) t).WT → t'.sort = t.sort) :
    Refines FS (.mk (.unop op a) t) (.mk (.unop op a') t') := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · have ⟨w1, w2⟩ := WT_unop.1 w
    have ⟨w3, s3⟩ := ha.syn w2
    refine ⟨WT_unop.2 ⟨?_, w3⟩, ht w⟩
    rw [s3, ht w]; exact w1
  · rw [eval_unop w] at e; rw [eval_unop w']
    exact evUnop_mono (ha.sem ρ) v e

theorem Refines.binop {FS op a a' b b' t t'} (ha : Refines FS a a') (hb : Refines FS b b')
    (ht : (Term.mk (.binop op a b) t).WT → t'.sort = t.sort) :
    Refines FS (.mk (.binop op a b) t) (.mk (.binop op a' b') t') := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · have ⟨w1, wa, wb⟩ := WT_binop.1 w
    have ⟨wa', sa⟩ := ha.syn wa
    have ⟨wb', sb⟩ := hb.syn wb
    refine ⟨WT_binop.2 ⟨?_, wa', wb'⟩, ht w⟩
    rw [sa, sb, ht w]; exact w1
  · rw [eval_binop w] at e; rw [eval_binop w']
    exact evBinop_mono (ha.sem ρ) (hb.sem ρ) v e

theorem Refines.ite {FS g g' a a' b b' t t'} (hg : Refines FS g g') (ha : Refines FS a a')
    (hb : Refines FS b b') (ht : (Term.mk (.triop .ite g a b) t).WT → t'.sort = t.sort) :
    Refines FS (.mk (.triop .ite g a b) t) (.mk (.triop .ite g' a' b') t') := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · have ⟨w1, wg, wa, wb⟩ := WT_triop.1 w
    have ⟨wg', sg⟩ := hg.syn wg
    have ⟨wa', sa⟩ := ha.syn wa
    have ⟨wb', sb⟩ := hb.syn wb
    refine ⟨WT_triop.2 ⟨?_, wg', wa', wb'⟩, ht w⟩
    rw [sg, sa, sb, ht w]; exact w1
  · rw [eval_ite w] at e; rw [eval_ite w']
    have := hg.sem ρ
    split at e
    · rename_i h; rw [this _ h]; exact ha.sem ρ v e
    · rename_i h; rw [this _ h]; exact hb.sem ρ v e
    · simp at e

theorem Refines.fma {FS a a' b b' c c' t t'} (ha : Refines FS a a') (hb : Refines FS b b')
    (hc : Refines FS c c') (ht : (Term.mk (.triop .fma a b c) t).WT → t'.sort = t.sort) :
    Refines FS (.mk (.triop .fma a b c) t) (.mk (.triop .fma a' b' c') t') := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · have ⟨w1, wa, wb, wc⟩ := WT_triop.1 w
    have ⟨wa', sa⟩ := ha.syn wa
    have ⟨wb', sb⟩ := hb.syn wb
    have ⟨wc', sc⟩ := hc.syn wc
    refine ⟨WT_triop.2 ⟨?_, wa', wb', wc'⟩, ht w⟩
    rw [sa, sb, sc, ht w]; exact w1
  · rw [eval_fma w] at e; rw [eval_fma w']
    exact evFma_mono (ha.sem ρ) (hb.sem ρ) (hc.sem ρ) v e

end Bvr

namespace Bvr

end Bvr

namespace Bvr

open Classical

/-! ## Literals -/

theorem WT_bitVec {z t} :
    (Term.mk (.bitVec z) t).WT ↔
      ∃ n : Nat, 0 < n ∧ (t = .bitVector n ∨ t = .loc n) ∧ 0 ≤ z ∧ z < 2 ^ n := by
  simp [Term.WT]

theorem Ty.width_of_sort {t : Ty} {n : Nat} (h : t = .bitVector n ∨ t = .loc n) :
    t.width = n := by
  simp [Ty.width, size_of_ty_of_bits h]

theorem eval_bitVec {FS ρ z t} (h : (Term.mk (.bitVec z) t).WT) :
    eval FS ρ (.mk (.bitVec z) t) = some (.bv t.width (BitVec.ofInt _ z)) := by
  rw [eval_eq_ev h, ev]

theorem eval_bitVec' {FS ρ z t n} (h : (Term.mk (.bitVec z) t).WT)
    (hn : t = .bitVector n ∨ t = .loc n) :
    eval FS ρ (.mk (.bitVec z) t) = some (.bv n.toNat (BitVec.ofInt _ z)) := by
  rw [eval_bitVec h, Ty.width, size_of_ty_of_bits hn]

theorem WT_bool {b t} : (Term.mk (.bool b) t).WT ↔ t = .bool := by simp [Term.WT]

theorem eval_bool {FS ρ b t} (h : t = .bool) :
    eval FS ρ (.mk (.bool b) t) = some (.bool b) := by
  subst h; rw [eval_eq_ev (WT_bool.2 rfl), ev]

@[simp] theorem v_true_WT : v_true.WT := by simp [v_true, Term.WT]
@[simp] theorem v_false_WT : v_false.WT := by simp [v_false, Term.WT]
@[simp] theorem v_true_ty : v_true.ty = .bool := rfl
@[simp] theorem v_false_ty : v_false.ty = .bool := rfl
@[simp] theorem eval_v_true {FS ρ} : eval FS ρ v_true = some (.bool true) := eval_bool rfl
@[simp] theorem eval_v_false {FS ρ} : eval FS ρ v_false = some (.bool false) := eval_bool rfl

theorem two_pow_pos' (n : Nat) : (0 : Int) < 2 ^ n := by exact_mod_cast Nat.two_pow_pos n

theorem emod_two_pow_nonneg (z : Int) (n : Nat) : 0 ≤ z % 2 ^ n :=
  Int.emod_nonneg _ (by have := two_pow_pos' n; omega)

theorem emod_two_pow_lt (z : Int) (n : Nat) : z % 2 ^ n < 2 ^ n :=
  Int.emod_lt_of_pos _ (two_pow_pos' n)

theorem mk_masked_WT {n z : Int} (hn : 0 < n) : (mk_masked n z).WT := by
  refine WT_bitVec.2 ⟨n.toNat, by omega, Or.inl (by simp [Int.toNat_of_nonneg (Int.le_of_lt hn)]), ?_, ?_⟩
  · exact emod_two_pow_nonneg _ _
  · exact emod_two_pow_lt _ _

@[simp] theorem mk_masked_ty {n z : Int} : (mk_masked n z).ty = .bitVector n := rfl

theorem BitVec.ofInt_emod_two_pow {w : Nat} (z : Int) :
    BitVec.ofInt w (z % 2 ^ w) = BitVec.ofInt w z := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt]
  congr 1
  exact Int.emod_emod_of_dvd _ (Int.dvd_refl _)

@[simp] theorem BitVec.ofInt_emod_two_pow' {w : Nat} (z : Int) :
    BitVec.ofInt w (z % ((2 ^ w : Nat) : Int)) = BitVec.ofInt w z := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt]
  congr 1
  exact Int.emod_emod_of_dvd _ (Int.dvd_refl _)

theorem eval_mk_masked {FS ρ} {n z : Int} (hn : 0 < n) :
    eval FS ρ (mk_masked n z) = some (.bv n.toNat (BitVec.ofInt _ z)) := by
  rw [mk_masked, eval_bitVec' (n := n.toNat) (mk_masked_WT hn)
    (Or.inl (by simp [Int.toNat_of_nonneg (Int.le_of_lt hn)]))]
  simp only [Int.toNat_natCast, BitVec.ofInt_emod_two_pow]

/-! ## Integers and bit-vectors -/

theorem BitVec.ofInt_sub {w : Nat} (x y : Int) :
    BitVec.ofInt w (x - y) = BitVec.ofInt w x - BitVec.ofInt w y := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

theorem BitVec.not_eq_neg_sub_one {w : Nat} (x : BitVec w) : ~~~x = -x - 1 := by
  rw [BitVec.neg_eq_not_add]; exact (BitVec.add_sub_cancel _ _).symm

theorem BitVec.ofInt_zlognot {w : Nat} (z : Int) :
    BitVec.ofInt w (zlognot z) = ~~~ BitVec.ofInt w z := by
  rw [BitVec.not_eq_neg_sub_one, zlognot, BitVec.ofInt_sub, BitVec.ofInt_neg]; simp

end Bvr

namespace Bvr

end Bvr
