import Bvr.Lemmas

/-! Lemmas for the proofs of the comparison rules (`bv_lt`, `bv_leq`). -/

namespace Bvr
namespace CompareL

open Classical

/-! ## Integer readings of bit-vectors -/

/-- A bit-vector read as a signed or unsigned integer. -/
def bvz {n : Nat} (s : Bool) (x : BitVec n) : Int := if s then x.toInt else x.toNat

theorem two_pow_succ_pred {N : Nat} (hN : 0 < N) : (2 : Int) ^ N = 2 * 2 ^ (N - 1) := by
  have : N = (N - 1) + 1 := by omega
  conv => lhs; rw [this]
  rw [Int.pow_succ]; omega

theorem toInt_cases {N : Nat} (x : BitVec N) :
    (2 * (x.toNat : Int) < 2 ^ N ∧ x.toInt = x.toNat) ∨
      (2 ^ N ≤ 2 * (x.toNat : Int) ∧ x.toInt = x.toNat - 2 ^ N) := by
  rw [BitVec.toInt_eq_toNat_cond]
  split
  · left; refine ⟨by exact_mod_cast ‹_›, rfl⟩
  · right; refine ⟨?_, by simp⟩
    have : ¬ 2 * x.toNat < 2 ^ N := ‹_›
    have : 2 ^ N ≤ 2 * x.toNat := by omega
    exact_mod_cast this

theorem toNat_lt' {N : Nat} (x : BitVec N) : (x.toNat : Int) < 2 ^ N := by
  have := x.isLt; exact_mod_cast this

theorem min_for_eq {N : Nat} (s : Bool) :
    min_for s N = if s then -2 ^ (N - 1) else 0 := by
  cases s <;> simp [min_for, zshiftl]

theorem max_for_eq {N : Nat} (s : Bool) :
    max_for s N = if s then 2 ^ (N - 1) - 1 else 2 ^ N - 1 := by
  cases s <;> simp [max_for, zshiftl]

theorem bvz_range {N : Nat} (hN : 0 < N) (s : Bool) (x : BitVec N) :
    min_for s N ≤ bvz s x ∧ bvz s x ≤ max_for s N := by
  have h2 := two_pow_succ_pred (N := N) hN
  have := toNat_lt' x
  rw [min_for_eq, max_for_eq]
  cases s <;> simp [bvz]
  · omega
  · rcases toInt_cases x with ⟨h, e⟩ | ⟨h, e⟩ <;> rw [e] <;> omega

theorem bvz_inj {N : Nat} {s : Bool} {x y : BitVec N} : bvz s x = bvz s y ↔ x = y := by
  cases s <;> simp [bvz, BitVec.toInt_inj]
  exact ⟨fun h => BitVec.toNat_inj.1 (by exact_mod_cast h), fun h => by rw [h]⟩

theorem bvz_ofInt {N : Nat} (hN : 0 < N) (s : Bool) {i : Int}
    (h1 : min_for s N ≤ i) (h2 : i ≤ max_for s N) : bvz s (BitVec.ofInt N i) = i := by
  rw [min_for_eq] at h1; rw [max_for_eq] at h2
  cases s <;> simp at h1 h2 <;> simp only [bvz, Bool.false_eq_true, ite_false, ite_true]
  · simp only [BitVec.toNat_ofInt, Int.natCast_pow, Int.cast_ofNat_Int]
    rw [Int.toNat_of_nonneg (emod_two_pow_nonneg _ _), Int.emod_eq_of_lt h1 (by omega)]
  · exact BitVec.toInt_ofInt_eq_self hN h1 (by omega)

theorem bv_to_z_lit {N : Nat} (hN : 0 < N) (s : Bool) {z : Int} (h1 : 0 ≤ z) (h2 : z < 2 ^ N) :
    bv_to_z s N z = bvz s (BitVec.ofInt N z) := by
  have e : (BitVec.ofInt N z).toNat = z.toNat := by
    simp only [BitVec.toNat_ofInt]; rw [Int.emod_eq_of_lt h1 (by exact_mod_cast h2)]
  have h2' := two_pow_succ_pred (N := N) hN
  cases s <;> simp only [bv_to_z, bvz, Bool.false_eq_true, ite_false, ite_true]
  · rw [e]; omega
  · rw [BitVec.toInt_eq_toNat_cond, e]
    simp only [signed_extract, zasr, Int.toNat_zero, Int.pow_zero, Int.ediv_one,
      Int.toNat_natCast]
    rw [Int.emod_eq_of_lt h1 h2]
    have e2 : (((2 : Nat) : Int) ^ N) = ((2 : Int) ^ N) := by simp
    simp only [Int.natCast_pow, e2, Int.toNat_of_nonneg h1]
    have key : (2 * z.toNat < 2 ^ N) ↔ (2 * z < (2 : Int) ^ N) := by
      rw [← Int.ofNat_lt]; push_cast; rw [Int.toNat_of_nonneg h1]
    simp only [key]
    split <;> split <;> omega

theorem cmp_lt_bvz {N : Nat} (s : Bool) (x y : BitVec N) :
    (if s then x.slt y else x.ult y) = decide (bvz s x < bvz s y) := by
  cases s <;> simp [bvz, BitVec.slt, BitVec.ult]

theorem cmp_le_bvz {N : Nat} (s : Bool) (x y : BitVec N) :
    (if s then x.sle y else x.ule y) = decide (bvz s x ≤ bvz s y) := by
  cases s <;> simp [bvz, BitVec.sle, BitVec.ule]

/-! ## Evaluation of binary bit-vector nodes -/

theorem bvBin_eq_some {f : ∀ {n : Nat}, BitVec n → BitVec n → Option Val} {a b : Option Val}
    {v : Val} :
    bvBin f a b = some v ↔ ∃ n x y, a = some (.bv n x) ∧ b = some (.bv n y) ∧ f x y = some v := by
  constructor
  · intro h
    unfold bvBin at h
    split at h
    · split at h
      · rename_i e; subst e; exact ⟨_, _, _, rfl, rfl, h⟩
      · simp at h
    · simp at h
  · rintro ⟨n, x, y, rfl, rfl, h⟩; simp [bvBin, h]

theorem bvBin_bv {f : ∀ {n : Nat}, BitVec n → BitVec n → Option Val} {n : Nat} (x y : BitVec n) :
    bvBin f (some (.bv n x)) (some (.bv n y)) = f x y := by simp [bvBin]

/-- [t] is a well-typed term of sort [bitVector N]. -/
def TB (t : Term) (N : Int) : Prop := t.WT ∧ t.ty = .bitVector N

/-- [t] is a well-typed boolean term. -/
def TBool (t : Term) : Prop := t.WT ∧ t.ty = .bool

/-- The binary operators whose operands and result have the same bit-vector sort. -/
def IsArith : Binop → Prop
  | .add _ | .sub _ | .mul _ | .div _ | .rem _ | .mod_ | .bitAnd | .bitOr | .bitXor
  | .shl | .lShr | .aShr => True
  | _ => False

theorem WT_arith {op a b t} (hop : IsArith op) :
    (Term.mk (.binop op a b) t).WT ↔
      ∃ n : Int, 0 < n ∧ TB a n ∧ TB b n ∧ t.sort = .bitVector n := by
  unfold TB
  cases op <;> simp [IsArith] at hop <;> simp [Term.WT, Binop.WT] <;>
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> grind

theorem WT_cmp {op a b t} (hop : ∃ s, op = .lt s ∨ op = .leq s) :
    (Term.mk (.binop op a b) t).WT ↔
      ∃ n : Int, 0 < n ∧ TB a n ∧ TB b n ∧ t.sort = .bool := by
  unfold TB
  obtain ⟨s, rfl | rfl⟩ := hop <;> simp [Term.WT, Binop.WT] <;>
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> grind

theorem eval_lit {FS ρ z t} {N : Nat} (w : (Term.mk (.bitVec z) t).WT)
    (hN : t = .bitVector N) :
    eval FS ρ (.mk (.bitVec z) t) = some (.bv N (BitVec.ofInt N z)) := by
  rw [eval_bitVec' w (Or.inl hN)]; simp

/-! ### Well-typedness of the results of the rule functions -/

theorem TB.wt {t N} (h : TB t N) : t.WT := h.1
theorem TB.sort {t N} (h : TB t N) : t.ty = .bitVector N := h.2

theorem TB_zero {N : Int} (h : 0 < N) : TB (bv_zero N) N := by
  refine ⟨WT_bitVec.2 ⟨N.toNat, by omega, ?_, Int.le_refl _, two_pow_pos' _⟩, rfl⟩
  simp; omega

theorem TB_masked {N z : Int} (h : 0 < N) : TB (mk_masked N z) N := ⟨mk_masked_WT h, rfl⟩

theorem TB_of_refines {FS s r N} (h : Refines FS s r) (w : TB s N) : TB r N := by
  have := h.syn w.1; exact ⟨this.1, this.2.trans w.2⟩

theorem TBool_of_refines {FS s r} (h : Refines FS s r) (w : TBool s) : TBool r := by
  have := h.syn w.1; exact ⟨this.1, this.2.trans w.2⟩

theorem TB_arith {op a b t N} (hop : IsArith op) (hN : 0 < N) (ha : TB a N) (hb : TB b N)
    (ht : t.sort = .bitVector N) : TB (.mk (.binop op a b) t) N :=
  ⟨(WT_arith hop).2 ⟨N, hN, ha, hb, ht⟩, ht⟩

theorem TBool_cmp {op a b t N} (hop : ∃ s, op = .lt s ∨ op = .leq s) (hN : 0 < N) (ha : TB a N)
    (hb : TB b N) (ht : t = .bool) : TBool (.mk (.binop op a b) t) :=
  ⟨(WT_cmp hop).2 ⟨N, hN, ha, hb, by simp [ht]⟩, by simp [ht]⟩

theorem TBool_true : TBool v_true := ⟨v_true_WT, rfl⟩
theorem TBool_false : TBool v_false := ⟨v_false_WT, rfl⟩

section O
variable {FS : FloatSem} {O : Ops} (hO : O.Sound FS)
include hO

theorem TB_O_add {c a b N} (hN : 0 < N) (ha : TB a N) (hb : TB b N) : TB (O.bv_add c a b) N :=
  TB_of_refines (hO.bv_add c a b) (TB_arith trivial hN ha hb ha.2)
theorem TB_O_sub {c a b N} (hN : 0 < N) (ha : TB a N) (hb : TB b N) : TB (O.bv_sub c a b) N :=
  TB_of_refines (hO.bv_sub c a b) (TB_arith trivial hN ha hb ha.2)
theorem TB_O_mul {c a b N} (hN : 0 < N) (ha : TB a N) (hb : TB b N) : TB (O.bv_mul c a b) N :=
  TB_of_refines (hO.bv_mul c a b) (TB_arith trivial hN ha hb ha.2)
theorem TB_O_div {s a b N} (hN : 0 < N) (ha : TB a N) (hb : TB b N) : TB (O.bv_div s a b) N :=
  TB_of_refines (hO.bv_div s a b) (TB_arith trivial hN ha hb ha.2)
theorem TB_O_neg {c a N} (hN : 0 < N) (ha : TB a N) : TB (O.bv_neg c a) N := by
  refine TB_of_refines (hO.bv_neg c a) ⟨WT_unop.2 ⟨?_, ha.1⟩, ha.2⟩
  simp [Unop.WT, ha.2]; exact hN
theorem TBool_O_lt {s a b N} (hN : 0 < N) (ha : TB a N) (hb : TB b N) :
    TBool (O.bv_lt s a b) :=
  TBool_of_refines (hO.bv_lt s a b) (TBool_cmp ⟨s, .inl rfl⟩ hN ha hb rfl)
theorem TBool_O_leq {s a b N} (hN : 0 < N) (ha : TB a N) (hb : TB b N) :
    TBool (O.bv_leq s a b) :=
  TBool_of_refines (hO.bv_leq s a b) (TBool_cmp ⟨s, .inr rfl⟩ hN ha hb rfl)
theorem TBool_O_eq {a b N} (ha : TB a N) (hb : TB b N) : TBool (O.sem_eq a b) := by
  refine TBool_of_refines (hO.sem_eq a b) ⟨?_, rfl⟩
  simp [sem_eq.spec, Term.WT, Binop.WT, ha.1, hb.1, ha.2, hb.2]
theorem TBool_O_not {a} (ha : TBool a) : TBool (O.b_not a) := by
  refine TBool_of_refines (hO.b_not a) ⟨?_, rfl⟩
  simp [b_not.spec, Term.WT, Unop.WT, ha.1, ha.2]
theorem TBool_O_and {a b} (ha : TBool a) (hb : TBool b) : TBool (O.b_and a b) := by
  refine TBool_of_refines (hO.b_and a b) ⟨?_, rfl⟩
  simp [b_and.spec, Term.WT, Binop.WT, ha.1, hb.1, ha.2, hb.2]
theorem TBool_O_or {a b} (ha : TBool a) (hb : TBool b) : TBool (O.b_or a b) := by
  refine TBool_of_refines (hO.b_or a b) ⟨?_, rfl⟩
  simp [b_or.spec, Term.WT, Binop.WT, ha.1, hb.1, ha.2, hb.2]
theorem TBool_O_ite {g a b} (hg : TBool g) (ha : TBool a) (hb : TBool b) :
    TBool (O.b_ite g a b) := by
  refine TBool_of_refines (hO.b_ite g a b) ⟨?_, ha.2⟩
  simp [b_ite.spec, Term.WT, Triop.WT, hg.1, ha.1, hb.1, ha.2, hb.2, hg.2]

end O

/-! ### Evaluation of raw nodes -/

/-- The no-overflow condition of a checked operation. -/
def ovf (c : Checked) (so uo : Bool) : Bool := (c.signed && so) || (c.unsigned && uo)

theorem eval_lt_eq_some {FS ρ s a b t v} (h : eval FS ρ (.mk (.binop (.lt s) a b) t) = some v) :
    ∃ n x y, eval FS ρ a = some (.bv n x) ∧ eval FS ρ b = some (.bv n y) ∧
      v = .bool (decide (bvz s x < bvz s y)) := by
  rw [eval_binop (eval_WT h)] at h; simp only [evBinop, checkedOp] at h
  obtain ⟨n, x, y, ha, hb, e⟩ := bvBin_eq_some.1 h
  refine ⟨n, x, y, ha, hb, ?_⟩
  simp at e; rw [← e, cmp_lt_bvz]

theorem eval_leq_eq_some {FS ρ s a b t v} (h : eval FS ρ (.mk (.binop (.leq s) a b) t) = some v) :
    ∃ n x y, eval FS ρ a = some (.bv n x) ∧ eval FS ρ b = some (.bv n y) ∧
      v = .bool (decide (bvz s x ≤ bvz s y)) := by
  rw [eval_binop (eval_WT h)] at h; simp only [evBinop, checkedOp] at h
  obtain ⟨n, x, y, ha, hb, e⟩ := bvBin_eq_some.1 h
  refine ⟨n, x, y, ha, hb, ?_⟩
  simp at e; rw [← e, cmp_le_bvz]

theorem eval_lt_of {FS ρ s a b t n} {x y : BitVec n} (w : (Term.mk (.binop (.lt s) a b) t).WT)
    (ha : eval FS ρ a = some (.bv n x)) (hb : eval FS ρ b = some (.bv n y)) :
    eval FS ρ (.mk (.binop (.lt s) a b) t) = some (.bool (decide (bvz s x < bvz s y))) := by
  rw [eval_binop w, ha, hb]; simp [evBinop, bvBin, cmp_lt_bvz]

theorem eval_leq_of {FS ρ s a b t n} {x y : BitVec n} (w : (Term.mk (.binop (.leq s) a b) t).WT)
    (ha : eval FS ρ a = some (.bv n x)) (hb : eval FS ρ b = some (.bv n y)) :
    eval FS ρ (.mk (.binop (.leq s) a b) t) = some (.bool (decide (bvz s x ≤ bvz s y))) := by
  rw [eval_binop w, ha, hb]; simp [evBinop, bvBin, cmp_le_bvz]

theorem eval_add_eq_some {FS ρ c a b t v} (h : eval FS ρ (.mk (.binop (.add c) a b) t) = some v) :
    ∃ n x y, eval FS ρ a = some (.bv n x) ∧ eval FS ρ b = some (.bv n y) ∧
      ovf c (x.saddOverflow y) (x.uaddOverflow y) = false ∧ v = .bv n (x + y) := by
  rw [eval_binop (eval_WT h)] at h; simp only [evBinop, checkedOp] at h
  obtain ⟨n, x, y, ha, hb, e⟩ := bvBin_eq_some.1 h
  refine ⟨n, x, y, ha, hb, ?_⟩
  simp only [ovf]; split at e <;> simp_all

theorem eval_sub_eq_some {FS ρ c a b t v} (h : eval FS ρ (.mk (.binop (.sub c) a b) t) = some v) :
    ∃ n x y, eval FS ρ a = some (.bv n x) ∧ eval FS ρ b = some (.bv n y) ∧
      ovf c (x.ssubOverflow y) (x.usubOverflow y) = false ∧ v = .bv n (x - y) := by
  rw [eval_binop (eval_WT h)] at h; simp only [evBinop, checkedOp] at h
  obtain ⟨n, x, y, ha, hb, e⟩ := bvBin_eq_some.1 h
  refine ⟨n, x, y, ha, hb, ?_⟩
  simp only [ovf]; split at e <;> simp_all

theorem eval_mul_eq_some {FS ρ c a b t v} (h : eval FS ρ (.mk (.binop (.mul c) a b) t) = some v) :
    ∃ n x y, eval FS ρ a = some (.bv n x) ∧ eval FS ρ b = some (.bv n y) ∧
      ovf c (x.smulOverflow y) (x.umulOverflow y) = false ∧ v = .bv n (x * y) := by
  rw [eval_binop (eval_WT h)] at h; simp only [evBinop, checkedOp] at h
  obtain ⟨n, x, y, ha, hb, e⟩ := bvBin_eq_some.1 h
  refine ⟨n, x, y, ha, hb, ?_⟩
  simp only [ovf]; split at e <;> simp_all

theorem eval_add_of {FS ρ c a b t n} {x y : BitVec n} (w : (Term.mk (.binop (.add c) a b) t).WT)
    (ha : eval FS ρ a = some (.bv n x)) (hb : eval FS ρ b = some (.bv n y))
    (hf : ovf c (x.saddOverflow y) (x.uaddOverflow y) = false) :
    eval FS ρ (.mk (.binop (.add c) a b) t) = some (.bv n (x + y)) := by
  rw [eval_binop w, ha, hb]; simp only [ovf] at hf; simp [evBinop, checkedOp, bvBin, hf]

theorem eval_sub_of {FS ρ c a b t n} {x y : BitVec n} (w : (Term.mk (.binop (.sub c) a b) t).WT)
    (ha : eval FS ρ a = some (.bv n x)) (hb : eval FS ρ b = some (.bv n y))
    (hf : ovf c (x.ssubOverflow y) (x.usubOverflow y) = false) :
    eval FS ρ (.mk (.binop (.sub c) a b) t) = some (.bv n (x - y)) := by
  rw [eval_binop w, ha, hb]; simp only [ovf] at hf; simp [evBinop, checkedOp, bvBin, hf]

theorem eval_mul_of {FS ρ c a b t n} {x y : BitVec n} (w : (Term.mk (.binop (.mul c) a b) t).WT)
    (ha : eval FS ρ a = some (.bv n x)) (hb : eval FS ρ b = some (.bv n y))
    (hf : ovf c (x.smulOverflow y) (x.umulOverflow y) = false) :
    eval FS ρ (.mk (.binop (.mul c) a b) t) = some (.bv n (x * y)) := by
  rw [eval_binop w, ha, hb]; simp only [ovf] at hf; simp [evBinop, checkedOp, bvBin, hf]

theorem eval_div_eq_some {FS ρ s a b t v} (h : eval FS ρ (.mk (.binop (.div s) a b) t) = some v) :
    ∃ n x y, eval FS ρ a = some (.bv n x) ∧ eval FS ρ b = some (.bv n y) ∧
      v = .bv n (if s then x.smtSDiv y else x.smtUDiv y) := by
  rw [eval_binop (eval_WT h)] at h; simp only [evBinop, checkedOp] at h
  obtain ⟨n, x, y, ha, hb, e⟩ := bvBin_eq_some.1 h
  refine ⟨n, x, y, ha, hb, ?_⟩
  simp at e; exact e.symm

theorem eval_div_of {FS ρ s a b t n} {x y : BitVec n} (w : (Term.mk (.binop (.div s) a b) t).WT)
    (ha : eval FS ρ a = some (.bv n x)) (hb : eval FS ρ b = some (.bv n y)) :
    eval FS ρ (.mk (.binop (.div s) a b) t) =
      some (.bv n (if s then x.smtSDiv y else x.smtUDiv y)) := by
  rw [eval_binop w, ha, hb]; simp [evBinop, bvBin]

theorem eval_neg_eq_some {FS ρ c a t v} (h : eval FS ρ (.mk (.unop (.neg c) a) t) = some v) :
    ∃ n x, eval FS ρ a = some (.bv n x) ∧ (c = true → x ≠ BitVec.intMin n) ∧ v = .bv n (-x) := by
  rw [eval_unop (eval_WT h)] at h
  revert h
  rcases eval FS ρ a with _ | ⟨_ | ⟨n, x⟩ | _ | _ | _ | _⟩ <;> simp [evUnop]
  intro h1 h2; exact ⟨_, _, ⟨rfl, .rfl⟩, h1, h2.symm⟩

theorem eval_neg_of {FS ρ c a t n} {x : BitVec n} (w : (Term.mk (.unop (.neg c) a) t).WT)
    (ha : eval FS ρ a = some (.bv n x)) (hc : c = true → x ≠ BitVec.intMin n) :
    eval FS ρ (.mk (.unop (.neg c) a) t) = some (.bv n (-x)) := by
  rw [eval_unop w, ha]; cases c <;> simp_all [evUnop]

section O
variable {FS : FloatSem} {O : Ops} (hO : O.Sound FS) {ρ : Env}
include hO

theorem eval_O_lt {s a b N n} {x y : BitVec n} (hN : 0 < N) (ha : TB a N) (hb : TB b N)
    (ea : eval FS ρ a = some (.bv n x)) (eb : eval FS ρ b = some (.bv n y)) :
    eval FS ρ (O.bv_lt s a b) = some (.bool (decide (bvz s x < bvz s y))) :=
  (hO.bv_lt s a b).2 ρ _ (eval_lt_of (TBool_cmp ⟨s, .inl rfl⟩ hN ha hb rfl).1 ea eb)

theorem eval_O_leq {s a b N n} {x y : BitVec n} (hN : 0 < N) (ha : TB a N) (hb : TB b N)
    (ea : eval FS ρ a = some (.bv n x)) (eb : eval FS ρ b = some (.bv n y)) :
    eval FS ρ (O.bv_leq s a b) = some (.bool (decide (bvz s x ≤ bvz s y))) :=
  (hO.bv_leq s a b).2 ρ _ (eval_leq_of (TBool_cmp ⟨s, .inr rfl⟩ hN ha hb rfl).1 ea eb)

theorem eval_O_add {c a b N n} {x y : BitVec n} (hN : 0 < N) (ha : TB a N) (hb : TB b N)
    (ea : eval FS ρ a = some (.bv n x)) (eb : eval FS ρ b = some (.bv n y))
    (hf : ovf c (x.saddOverflow y) (x.uaddOverflow y) = false) :
    eval FS ρ (O.bv_add c a b) = some (.bv n (x + y)) :=
  (hO.bv_add c a b).2 ρ _ (eval_add_of (TB_arith (op := .add c) trivial hN ha hb ha.2).1 ea eb hf)

theorem eval_O_sub {c a b N n} {x y : BitVec n} (hN : 0 < N) (ha : TB a N) (hb : TB b N)
    (ea : eval FS ρ a = some (.bv n x)) (eb : eval FS ρ b = some (.bv n y))
    (hf : ovf c (x.ssubOverflow y) (x.usubOverflow y) = false) :
    eval FS ρ (O.bv_sub c a b) = some (.bv n (x - y)) :=
  (hO.bv_sub c a b).2 ρ _ (eval_sub_of (TB_arith (op := .sub c) trivial hN ha hb ha.2).1 ea eb hf)

theorem eval_O_div {s a b N n} {x y : BitVec n} (hN : 0 < N) (ha : TB a N) (hb : TB b N)
    (ea : eval FS ρ a = some (.bv n x)) (eb : eval FS ρ b = some (.bv n y)) :
    eval FS ρ (O.bv_div s a b) = some (.bv n (if s then x.smtSDiv y else x.smtUDiv y)) :=
  (hO.bv_div s a b).2 ρ _ (eval_div_of (TB_arith (op := .div s) trivial hN ha hb ha.2).1 ea eb)

theorem eval_O_neg {c a N n} {x : BitVec n} (hN : 0 < N) (ha : TB a N)
    (ea : eval FS ρ a = some (.bv n x)) (hc : c = true → x ≠ BitVec.intMin n) :
    eval FS ρ (O.bv_neg c a) = some (.bv n (-x)) := by
  refine (hO.bv_neg c a).2 ρ _ (eval_neg_of ?_ ea hc)
  exact WT_unop.2 ⟨by simp [Unop.WT, ha.2]; exact hN, ha.1⟩

theorem eval_O_eq {a b va vb} (ha : a.WT) (hb : b.WT) (hs : a.ty = b.ty)
    (ea : eval FS ρ a = some va) (eb : eval FS ρ b = some vb) :
    eval FS ρ (O.sem_eq a b) = some (.bool (decide (va = vb))) := by
  refine (hO.sem_eq a b).2 ρ _ ?_
  have w : (sem_eq.spec a b).WT := by simp [sem_eq.spec, Term.WT, Binop.WT, ha, hb, hs]
  rw [sem_eq.spec, eval_binop w, ea, eb]; simp [evBinop]

theorem eval_O_not {a b} (ha : TBool a) (ea : eval FS ρ a = some (.bool b)) :
    eval FS ρ (O.b_not a) = some (.bool !b) := by
  refine (hO.b_not a).2 ρ _ ?_
  have w : (b_not.spec a).WT := by simp [b_not.spec, Term.WT, Unop.WT, ha.1, ha.2]
  rw [b_not.spec, eval_unop w, ea]; simp [evUnop]

theorem eval_O_and {a b} (ha : TBool a) (hb : TBool b) :
    OLe (pand (eval FS ρ a) (eval FS ρ b)) (eval FS ρ (O.b_and a b)) := by
  intro v e
  refine (hO.b_and a b).2 ρ _ ?_
  have w : (b_and.spec a b).WT := by simp [b_and.spec, Term.WT, Binop.WT, ha.1, ha.2, hb.1, hb.2]
  rw [b_and.spec, eval_binop w]; exact e

theorem eval_O_or {a b} (ha : TBool a) (hb : TBool b) :
    OLe (por (eval FS ρ a) (eval FS ρ b)) (eval FS ρ (O.b_or a b)) := by
  intro v e
  refine (hO.b_or a b).2 ρ _ ?_
  have w : (b_or.spec a b).WT := by simp [b_or.spec, Term.WT, Binop.WT, ha.1, ha.2, hb.1, hb.2]
  rw [b_or.spec, eval_binop w]; exact e

theorem eval_O_ite {g a b} (hg : TBool g) (ha : TBool a) (hb : TBool b) :
    OLe (match eval FS ρ g with
      | some (.bool true) => eval FS ρ a
      | some (.bool false) => eval FS ρ b
      | _ => none) (eval FS ρ (O.b_ite g a b)) := by
  intro v e
  refine (hO.b_ite g a b).2 ρ _ ?_
  have w : (b_ite.spec g a b).WT := by
    simp [b_ite.spec, Term.WT, Triop.WT, hg.1, ha.1, hb.1, ha.2, hb.2, hg.2]
  rw [b_ite.spec, eval_ite w]; exact e

end O

/-! ## Overflow conditions -/

theorem natCast_two_pow (N : Nat) : ((2 ^ N : Nat) : Int) = (2 : Int) ^ N := by norm_cast

theorem sadd_ovf_false {N : Nat} {x y : BitVec N} :
    x.saddOverflow y = false ↔
      -2 ^ (N - 1) ≤ x.toInt + y.toInt ∧ x.toInt + y.toInt < 2 ^ (N - 1) := by
  simp [BitVec.saddOverflow]; omega
theorem ssub_ovf_false {N : Nat} {x y : BitVec N} :
    x.ssubOverflow y = false ↔
      -2 ^ (N - 1) ≤ x.toInt - y.toInt ∧ x.toInt - y.toInt < 2 ^ (N - 1) := by
  simp [BitVec.ssubOverflow]; omega
theorem smul_ovf_false {N : Nat} {x y : BitVec N} :
    x.smulOverflow y = false ↔
      -2 ^ (N - 1) ≤ x.toInt * y.toInt ∧ x.toInt * y.toInt < 2 ^ (N - 1) := by
  simp [BitVec.smulOverflow]; omega
theorem uadd_ovf_false {N : Nat} {x y : BitVec N} :
    x.uaddOverflow y = false ↔ (x.toNat : Int) + y.toNat < 2 ^ N := by
  simp only [BitVec.uaddOverflow, decide_eq_false_iff_not, Nat.not_le, ge_iff_le]
  rw [← natCast_two_pow]; omega
theorem usub_ovf_false {N : Nat} {x y : BitVec N} :
    x.usubOverflow y = false ↔ (y.toNat : Int) ≤ x.toNat := by
  simp [BitVec.usubOverflow]
theorem umul_ovf_false {N : Nat} {x y : BitVec N} :
    x.umulOverflow y = false ↔ (x.toNat : Int) * y.toNat < 2 ^ N := by
  simp only [BitVec.umulOverflow, decide_eq_false_iff_not, Nat.not_le, ge_iff_le]
  rw [← natCast_two_pow]; exact_mod_cast Iff.rfl

theorem bvz_add_of_ovf {N : Nat} {s : Bool} {c : Checked} (hc : checked_has s c = true)
    {x y : BitVec N} (hf : ovf c (x.saddOverflow y) (x.uaddOverflow y) = false) :
    bvz s (x + y) = bvz s x + bvz s y ∧ min_for s N ≤ bvz s x + bvz s y ∧
      bvz s x + bvz s y ≤ max_for s N := by
  rw [min_for_eq, max_for_eq]
  cases s <;> simp [checked_has] at hc <;> simp [ovf, hc] at hf <;>
    simp only [bvz, Bool.false_eq_true, ite_false, ite_true]
  · rw [BitVec.toNat_add_of_not_uaddOverflow (by simp [hf.2])]
    have := uadd_ovf_false.1 hf.2; push_cast; omega
  · rw [BitVec.toInt_add_of_not_saddOverflow (by simp [hf.1])]
    have := sadd_ovf_false.1 hf.1; omega

theorem bvz_sub_of_ovf {N : Nat} {s : Bool} {c : Checked} (hc : checked_has s c = true)
    {x y : BitVec N} (hf : ovf c (x.ssubOverflow y) (x.usubOverflow y) = false) :
    bvz s (x - y) = bvz s x - bvz s y ∧ min_for s N ≤ bvz s x - bvz s y ∧
      bvz s x - bvz s y ≤ max_for s N := by
  rw [min_for_eq, max_for_eq]
  have := toNat_lt' x
  cases s <;> simp [checked_has] at hc <;> simp [ovf, hc] at hf <;>
    simp only [bvz, Bool.false_eq_true, ite_false, ite_true]
  · rw [BitVec.toNat_sub_of_not_usubOverflow (by simp [hf.2])]
    have := usub_ovf_false.1 hf.2; omega
  · rw [BitVec.toInt_sub_of_not_ssubOverflow (by simp [hf.1])]
    have := ssub_ovf_false.1 hf.1; omega

theorem bvz_mul_of_ovf {N : Nat} {s : Bool} {c : Checked} (hc : checked_has s c = true)
    {x y : BitVec N} (hf : ovf c (x.smulOverflow y) (x.umulOverflow y) = false) :
    bvz s (x * y) = bvz s x * bvz s y ∧ min_for s N ≤ bvz s x * bvz s y ∧
      bvz s x * bvz s y ≤ max_for s N := by
  rw [min_for_eq, max_for_eq]
  cases s <;> simp [checked_has] at hc <;> simp [ovf, hc] at hf <;>
    simp only [bvz, Bool.false_eq_true, ite_false, ite_true]
  · rw [BitVec.toNat_mul_of_not_umulOverflow (by simp [hf.2])]
    have := umul_ovf_false.1 hf.2; push_cast
    exact ⟨rfl, Int.mul_nonneg (by omega) (by omega), by omega⟩
  · rw [BitVec.toInt_mul_of_not_smulOverflow (by simp [hf.1])]
    have := smul_ovf_false.1 hf.1; omega

theorem ovf_add_of_range {N : Nat} (s : Bool) {x y : BitVec N}
    (h1 : min_for s N ≤ bvz s x + bvz s y) (h2 : bvz s x + bvz s y ≤ max_for s N) :
    ovf (checked_of_signed s) (x.saddOverflow y) (x.uaddOverflow y) = false := by
  rw [min_for_eq] at h1; rw [max_for_eq] at h2
  cases s <;> simp [bvz] at h1 h2 <;>
    simp [ovf, checked_of_signed, checked_signed, checked_unsigned]
  · exact uadd_ovf_false.2 (by omega)
  · exact sadd_ovf_false.2 (by omega)

theorem ovf_sub_of_range {N : Nat} (s : Bool) {x y : BitVec N}
    (h1 : min_for s N ≤ bvz s x - bvz s y) (h2 : bvz s x - bvz s y ≤ max_for s N) :
    ovf (checked_of_signed s) (x.ssubOverflow y) (x.usubOverflow y) = false := by
  rw [min_for_eq] at h1; rw [max_for_eq] at h2
  cases s <;> simp [bvz] at h1 h2 <;>
    simp [ovf, checked_of_signed, checked_signed, checked_unsigned]
  · exact usub_ovf_false.2 (by omega)
  · exact ssub_ovf_false.2 (by omega)

theorem overflows_add_false {s : Bool} {N : Int} {l r : Int} :
    overflows_add s N l r = false ↔
      min_for s N ≤ bv_to_z s N l + bv_to_z s N r ∧
        bv_to_z s N l + bv_to_z s N r ≤ max_for s N := by
  simp [overflows_add]

theorem overflows_sub_false {s : Bool} {N : Int} {l r : Int} :
    overflows_sub s N l r = false ↔
      min_for s N ≤ bv_to_z s N l - bv_to_z s N r ∧
        bv_to_z s N l - bv_to_z s N r ≤ max_for s N := by
  simp [overflows_sub]

/-! ### Literals -/

theorem TB_size {t n} (h : TB t n) : size t = n := by
  simp [h.2]

theorem TB_lit {z t} {n : Int} (h : TB (.mk (.bitVec z) t) n) :
    ∃ N : Nat, n = N ∧ 0 < N ∧ 0 ≤ z ∧ z < 2 ^ N ∧
      ∀ FS ρ, eval FS ρ (.mk (.bitVec z) t) = some (.bv N (BitVec.ofInt N z)) := by
  obtain ⟨N, hN, hT, h0, h1⟩ := WT_bitVec.1 h.1
  have h2 := h.2; simp only [Term.ty_mk] at h2; subst h2
  have e : n = N := by rcases hT with h | h <;> simp at h; omega
  subst e
  exact ⟨N, rfl, hN, h0, h1, fun FS ρ => eval_lit h.1 rfl⟩

/-- Two equal bit-vector values. -/
theorem bv_val_eq {n m : Nat} {x : BitVec n} {y : BitVec m}
    (h : some (Val.bv n x) = some (.bv m y)) : n = m ∧ HEq x y := by
  simp at h; exact h

/-! ### Inversion of typing -/

theorem TB_neg_inv {c a t n} (h : TB (.mk (.unop (.neg c) a) t) n) : 0 < n ∧ TB a n := by
  have ⟨w1, w2⟩ := WT_unop.1 h.1
  simp only [Unop.WT] at w1
  obtain ⟨n', hn', ha, ht⟩ := w1
  have := h.2; simp only [Term.ty_mk] at this
  rw [this] at ht; rw [ha] at ht; cases ht
  exact ⟨hn', w2, ha⟩

theorem TB_arith_inv {op a b t n} (hop : IsArith op) (h : TB (.mk (.binop op a b) t) n) :
    0 < n ∧ TB a n ∧ TB b n := by
  obtain ⟨n', hn', ha, hb, ht⟩ := (WT_arith hop).1 h.1
  have := h.2; simp only [Term.ty_mk] at this
  rw [this] at ht; cases ht
  exact ⟨hn', ha, hb⟩

theorem TB_ite_inv {g a b t n} (h : TB (.mk (.triop .ite g a b) t) n) :
    TBool g ∧ TB a n ∧ TB b n := by
  have ⟨w1, wg, wa, wb⟩ := WT_triop.1 h.1
  simp only [Triop.WT] at w1
  obtain ⟨h1, h2, h3⟩ := w1
  have := h.2; simp only [Term.ty_mk] at this
  refine ⟨⟨wg, h1⟩, ⟨wa, ?_⟩, ⟨wb, ?_⟩⟩
  · simp at h3; rw [← h3]; exact this
  · simp at h2 h3; rw [h2, ← h3]; exact this

/-! ### Negation -/

theorem eq_intMin_iff {N : Nat} (hN : 0 < N) {x : BitVec N} :
    x = BitVec.intMin N ↔ x.toInt = -2 ^ (N - 1) := by
  rw [← BitVec.toInt_inj, BitVec.toInt_intMin_of_pos hN]

theorem toInt_neg' {N : Nat} (hN : 0 < N) {x : BitVec N} (h : x.toInt ≠ -2 ^ (N - 1)) :
    (-x).toInt = -x.toInt :=
  BitVec.toInt_neg_of_ne_intMin (fun e => h ((eq_intMin_iff hN).1 e))

theorem val_bv_eq {n : Nat} {x y : BitVec n} : (Val.bv n x = Val.bv n y) ↔ x = y := by simp

theorem TB_mk_size {k t n} (h : TB (.mk k t) n) : size_of_ty t = n := by
  have := TB_size h; simpa using this

theorem pos_of_ne_intMin {m : Nat} {x : BitVec m} (h : x ≠ BitVec.intMin m) : 0 < m := by
  rcases m with _ | m
  · exact absurd (Subsingleton.elim _ _) h
  · omega

theorem toInt_ne_of_ne_intMin {m : Nat} {x : BitVec m} (h : x ≠ BitVec.intMin m) :
    x.toInt ≠ -2 ^ (m - 1) := fun e => h ((eq_intMin_iff (pos_of_ne_intMin h)).2 e)

theorem bvz_lit {N : Nat} (hN : 0 < N) (s : Bool) {z : Int} (h1 : 0 ≤ z) (h2 : z < 2 ^ N) :
    bvz s (BitVec.ofInt N z) = bv_to_z s N z := (bv_to_z_lit hN s h1 h2).symm

theorem bv_to_z_false (N z : Int) : bv_to_z false N z = z := rfl

theorem TB_ofBool_inv {k b t n} (h : TB (.mk (.unop (.bvOfBool k) b) t) n) :
    k = n ∧ 0 < n ∧ TBool b := by
  have ⟨w1, w2⟩ := WT_unop.1 h.1
  simp only [Unop.WT] at w1
  obtain ⟨hk, hb, ht⟩ := w1
  have := h.2; simp only [Term.ty_mk] at this
  rw [this] at ht; cases ht
  exact ⟨rfl, hk, w2, hb⟩

theorem eval_ofBool_eq_some {FS ρ k b t v}
    (h : eval FS ρ (.mk (.unop (.bvOfBool k) b) t) = some v) :
    ∃ bb, eval FS ρ b = some (.bool bb) ∧ v = .bv k.toNat (if bb then 1 else 0) := by
  rw [eval_unop (eval_WT h)] at h
  revert h
  rcases eval FS ρ b with _ | ⟨bb | _ | _ | _ | _ | _⟩ <;> simp [evUnop]
  intro h; exact h.symm

theorem eval_zero {FS ρ} {N : Nat} (hN : 0 < N) :
    eval FS ρ (bv_zero N) = some (.bv N 0) := by
  rw [bv_zero, eval_lit (TB_zero (by omega)).1 rfl]; simp

theorem TB_sz {t n} (h : TB t n) : size_of_ty t.ty = n := TB_size h

/-! ### Checked arithmetic, read as integers -/

theorem checked_has_of_signed (s : Bool) : checked_has s (checked_of_signed s) = true := by
  cases s <;> rfl

theorem eval_add_inv {FS ρ c a b t m} {y : BitVec m} (s : Bool) (hc : checked_has s c = true)
    (h : eval FS ρ (.mk (.binop (.add c) a b) t) = some (.bv m y)) :
    ∃ xa xb, eval FS ρ a = some (.bv m xa) ∧ eval FS ρ b = some (.bv m xb) ∧
      bvz s y = bvz s xa + bvz s xb ∧ min_for s m ≤ bvz s xa + bvz s xb ∧
      bvz s xa + bvz s xb ≤ max_for s m := by
  obtain ⟨n, xa, xb, ea, eb, hf, hv⟩ := eval_add_eq_some h
  obtain ⟨rfl, ⟨⟩⟩ := bv_val_eq (congrArg some hv)
  exact ⟨xa, xb, ea, eb, bvz_add_of_ovf hc hf⟩

theorem eval_sub_inv {FS ρ c a b t m} {y : BitVec m} (s : Bool) (hc : checked_has s c = true)
    (h : eval FS ρ (.mk (.binop (.sub c) a b) t) = some (.bv m y)) :
    ∃ xa xb, eval FS ρ a = some (.bv m xa) ∧ eval FS ρ b = some (.bv m xb) ∧
      bvz s y = bvz s xa - bvz s xb ∧ min_for s m ≤ bvz s xa - bvz s xb ∧
      bvz s xa - bvz s xb ≤ max_for s m := by
  obtain ⟨n, xa, xb, ea, eb, hf, hv⟩ := eval_sub_eq_some h
  obtain ⟨rfl, ⟨⟩⟩ := bv_val_eq (congrArg some hv)
  exact ⟨xa, xb, ea, eb, bvz_sub_of_ovf hc hf⟩

theorem eval_mul_inv {FS ρ c a b t m} {y : BitVec m} (s : Bool) (hc : checked_has s c = true)
    (h : eval FS ρ (.mk (.binop (.mul c) a b) t) = some (.bv m y)) :
    ∃ xa xb, eval FS ρ a = some (.bv m xa) ∧ eval FS ρ b = some (.bv m xb) ∧
      bvz s y = bvz s xa * bvz s xb ∧ min_for s m ≤ bvz s xa * bvz s xb ∧
      bvz s xa * bvz s xb ≤ max_for s m := by
  obtain ⟨n, xa, xb, ea, eb, hf, hv⟩ := eval_mul_eq_some h
  obtain ⟨rfl, ⟨⟩⟩ := bv_val_eq (congrArg some hv)
  exact ⟨xa, xb, ea, eb, bvz_mul_of_ovf hc hf⟩

section O
variable {FS : FloatSem} {O : Ops} (hO : O.Sound FS) {ρ : Env}
include hO

theorem eval_O_sub_rng {s a b N m} {xa xb : BitVec m} (hN : 0 < N) (ha : TB a N) (hb : TB b N)
    (ea : eval FS ρ a = some (.bv m xa)) (eb : eval FS ρ b = some (.bv m xb))
    (h1 : min_for s m ≤ bvz s xa - bvz s xb) (h2 : bvz s xa - bvz s xb ≤ max_for s m) :
    ∃ r, eval FS ρ (O.bv_sub (checked_of_signed s) a b) = some (.bv m r) ∧
      bvz s r = bvz s xa - bvz s xb := by
  have hf := ovf_sub_of_range s h1 h2
  exact ⟨_, eval_O_sub hO hN ha hb ea eb hf, (bvz_sub_of_ovf (checked_has_of_signed s) hf).1⟩

theorem eval_O_add_rng {s a b N m} {xa xb : BitVec m} (hN : 0 < N) (ha : TB a N) (hb : TB b N)
    (ea : eval FS ρ a = some (.bv m xa)) (eb : eval FS ρ b = some (.bv m xb))
    (h1 : min_for s m ≤ bvz s xa + bvz s xb) (h2 : bvz s xa + bvz s xb ≤ max_for s m) :
    ∃ r, eval FS ρ (O.bv_add (checked_of_signed s) a b) = some (.bv m r) ∧
      bvz s r = bvz s xa + bvz s xb := by
  have hf := ovf_add_of_range s h1 h2
  exact ⟨_, eval_O_add hO hN ha hb ea eb hf, (bvz_add_of_ovf (checked_has_of_signed s) hf).1⟩

end O

/-! ### Booleans -/

theorem pand_bool (a b : Bool) : pand (some (.bool a)) (some (.bool b)) = some (.bool (a && b)) := by
  cases a <;> cases b <;> rfl

theorem por_bool (a b : Bool) : por (some (.bool a)) (some (.bool b)) = some (.bool (a || b)) := by
  cases a <;> cases b <;> rfl

/-! ### The sign bit -/

theorem zshiftl_one {N : Nat} (hN : 0 < N) : zshiftl 1 ((N : Int) - 1) = 2 ^ (N - 1) := by
  simp only [zshiftl, Int.one_mul]
  congr 1; omega

theorem eval_sign_bit {FS ρ} {N : Nat} (hN : 0 < N) :
    eval FS ρ (mk_masked N (zshiftl 1 ((N : Int) - 1))) =
      some (.bv N (BitVec.ofInt N (2 ^ (N - 1)))) := by
  rw [eval_mk_masked (by omega), zshiftl_one hN]; simp

theorem bvz_sign_bit {N : Nat} (hN : 0 < N) :
    bvz false (BitVec.ofInt N (2 ^ (N - 1))) = 2 ^ (N - 1) := by
  have := two_pow_succ_pred (N := N) hN
  have : (0 : Int) < 2 ^ (N - 1) := two_pow_pos' _
  apply bvz_ofInt hN <;> simp only [min_for_eq, max_for_eq]
  all_goals simp; omega

/-- The signed reading of a bit-vector, from the unsigned one. -/
theorem bvz_true_cases {N : Nat} (hN : 0 < N) (x : BitVec N) :
    (bvz false x < 2 ^ (N - 1) ∧ bvz true x = bvz false x) ∨
      (2 ^ (N - 1) ≤ bvz false x ∧ bvz true x = bvz false x - 2 ^ N) := by
  have := two_pow_succ_pred (N := N) hN
  simp only [bvz, ite_true, Bool.false_eq_true, ite_false]
  rcases toInt_cases x with ⟨h, e⟩ | ⟨h, e⟩ <;> rw [e] <;> omega

theorem bvz_false_range {N : Nat} (x : BitVec N) : 0 ≤ bvz false x ∧ bvz false x < 2 ^ N := by
  simp only [bvz, Bool.false_eq_true, ite_false]; exact ⟨by omega, toNat_lt' x⟩

theorem const_keeps_iff {b d : Int} :
    const_keeps_in_range b d = true ↔ (0 ≤ b → 0 ≤ d ∧ d ≤ b) ∧ (b < 0 → b ≤ d ∧ d ≤ 0) := by
  simp only [const_keeps_in_range, zmin, zmax, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩; split at h1 <;> split at h2 <;> omega
  · rintro ⟨h1, h2⟩; constructor <;> split <;> omega

theorem min_for_nonpos {N : Nat} (s : Bool) : min_for s N ≤ 0 := by
  have := two_pow_pos' (N - 1)
  rw [min_for_eq]; split <;> omega

theorem max_for_nonneg {N : Nat} (hN : 0 < N) (s : Bool) : 0 ≤ max_for s N := by
  have := two_pow_pos' (N - 1)
  have := two_pow_succ_pred (N := N) hN
  rw [max_for_eq]; split <;> omega

end CompareL
end Bvr
