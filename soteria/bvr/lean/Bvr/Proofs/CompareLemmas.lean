import Bvr.Lemmas

/-! Lemmas for the proofs of the comparison rules (`bv_lt`, `bv_leq`). -/

namespace Bvr
namespace CompareL

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

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

/-! ### Evaluation preserves sorts -/

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

/-- The value of a bit-vector term has its width. -/
theorem eval_bv_width {FS ρ t n x} {N : Int} (hT : t.ty = .bitVector N)
    (h : eval FS ρ t = some (.bv n x)) : (n : Int) = N ∧ 0 < n := by
  have := eval_hasSort h; rw [hT] at this; simpa [Val.hasSort] using this

theorem eval_bool_val {FS ρ t v} (hT : t.ty = .bool) (h : eval FS ρ t = some v) :
    ∃ b, v = .bool b := by
  have := eval_hasSort h; rw [hT] at this
  rcases v with _ | _ | _ | _ | _ | _ <;> simp [Val.hasSort] at this; exact ⟨_, rfl⟩

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

/-! ## Refinement of a comparison -/

@[simp] theorem of_bool_WT {b} : (of_bool b).WT := by cases b <;> simp [of_bool]
@[simp] theorem of_bool_ty {b} : (of_bool b).ty = .bool := by cases b <;> simp [of_bool]
@[simp] theorem eval_of_bool {FS ρ b} : eval FS ρ (of_bool b) = some (.bool b) := by
  cases b <;> simp [of_bool]

/-- A comparison of bit-vectors, read as integers. -/
def cmpv (le s : Bool) {n : Nat} (x y : BitVec n) : Bool :=
  if le then decide (bvz s x ≤ bvz s y) else decide (bvz s x < bvz s y)

/-- The comparison operator. -/
def cmpOp (le s : Bool) : Binop := if le then .leq s else .lt s

theorem cmpOp_is (le s : Bool) : ∃ s', cmpOp le s = .lt s' ∨ cmpOp le s = .leq s' := by
  cases le <;> simp [cmpOp]

theorem cmp_spec_eq_lt (s : Bool) (v1 v2 : Term) :
    bv_lt.spec s v1 v2 = .mk (.binop (cmpOp false s) v1 v2) .bool := rfl
theorem cmp_spec_eq_leq (s : Bool) (v1 v2 : Term) :
    bv_leq.spec s v1 v2 = .mk (.binop (cmpOp true s) v1 v2) .bool := rfl

theorem eval_cmp_eq_some {FS ρ le s a b t v}
    (h : eval FS ρ (.mk (.binop (cmpOp le s) a b) t) = some v) :
    ∃ n x y, eval FS ρ a = some (.bv n x) ∧ eval FS ρ b = some (.bv n y) ∧
      v = .bool (cmpv le s x y) := by
  cases le
  · obtain ⟨n, x, y, h1, h2, h3⟩ := eval_lt_eq_some h
    exact ⟨n, x, y, h1, h2, by simp [h3, cmpv]⟩
  · obtain ⟨n, x, y, h1, h2, h3⟩ := eval_leq_eq_some h
    exact ⟨n, x, y, h1, h2, by simp [h3, cmpv]⟩

theorem eval_cmp_of {FS ρ le s a b t n} {x y : BitVec n}
    (w : (Term.mk (.binop (cmpOp le s) a b) t).WT)
    (ha : eval FS ρ a = some (.bv n x)) (hb : eval FS ρ b = some (.bv n y)) :
    eval FS ρ (.mk (.binop (cmpOp le s) a b) t) = some (.bool (cmpv le s x y)) := by
  cases le <;> simp only [cmpOp, Bool.false_eq_true, ite_false, ite_true] at w ⊢
  · rw [eval_lt_of w ha hb]; simp [cmpv]
  · rw [eval_leq_of w ha hb]; simp [cmpv]

/-- The generic refinement lemma of the comparison rules. -/
theorem cmp_refines {FS le s v1 v2 r}
    (syn : ∀ N : Int, 0 < N → TB v1 N → TB v2 N → TBool r)
    (sem : ∀ ρ (N : Int) (n : Nat) (x y : BitVec n), 0 < N → TB v1 N → TB v2 N → (n : Int) = N → 0 < n →
      eval FS ρ v1 = some (.bv n x) → eval FS ρ v2 = some (.bv n y) →
      eval FS ρ r = some (.bool (cmpv le s x y))) :
    Refines FS (.mk (.binop (cmpOp le s) v1 v2) .bool) r := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · obtain ⟨N, hN, h1, h2, _⟩ := (WT_cmp (cmpOp_is le s)).1 w
    have := syn N hN h1 h2; exact ⟨this.1, by simp [this.2]⟩
  · obtain ⟨N, hN, h1, h2, _⟩ := (WT_cmp (cmpOp_is le s)).1 w
    obtain ⟨n, x, y, ea, eb, rfl⟩ := eval_cmp_eq_some e
    have := eval_bv_width h1.2 ea
    exact sem ρ N n x y hN h1 h2 this.1 this.2 ea eb

theorem cmp_refines_lt {FS s v1 v2 r}
    (syn : ∀ N : Int, 0 < N → TB v1 N → TB v2 N → TBool r)
    (sem : ∀ ρ (N : Int) (n : Nat) (x y : BitVec n), 0 < N → TB v1 N → TB v2 N → (n : Int) = N → 0 < n →
      eval FS ρ v1 = some (.bv n x) → eval FS ρ v2 = some (.bv n y) →
      eval FS ρ r = some (.bool (decide (bvz s x < bvz s y)))) :
    Refines FS (bv_lt.spec s v1 v2) r :=
  cmp_refines (le := false) syn (fun ρ N n x y a b c d e f g => by
    simpa [cmpv] using sem ρ N n x y a b c d e f g)

theorem cmp_refines_leq {FS s v1 v2 r}
    (syn : ∀ N : Int, 0 < N → TB v1 N → TB v2 N → TBool r)
    (sem : ∀ ρ (N : Int) (n : Nat) (x y : BitVec n), 0 < N → TB v1 N → TB v2 N → (n : Int) = N → 0 < n →
      eval FS ρ v1 = some (.bv n x) → eval FS ρ v2 = some (.bv n y) →
      eval FS ρ r = some (.bool (decide (bvz s x ≤ bvz s y)))) :
    Refines FS (bv_leq.spec s v1 v2) r :=
  cmp_refines (le := true) syn (fun ρ N n x y a b c d e f g => by
    simpa [cmpv] using sem ρ N n x y a b c d e f g)

/-- The value of a literal of a width [N]. -/
theorem lit_val {FS ρ z t N n} {x : BitVec n} (h : TB (.mk (.bitVec z) t) N)
    (e : eval FS ρ (.mk (.bitVec z) t) = some (.bv n x)) :
    N = n ∧ t = .bitVector n ∧ 0 < n ∧ 0 ≤ z ∧ z < 2 ^ n ∧ x = BitVec.ofInt n z ∧
      bv_to_z false N z = bvz false x ∧ bv_to_z true N z = bvz true x := by
  obtain ⟨M, rfl, hM, h0, h1, ev⟩ := TB_lit h
  rw [ev] at e; simp at e; obtain ⟨rfl, e⟩ := e; cases e
  have := h.2; simp only [Term.ty_mk] at this
  exact ⟨rfl, this, hM, h0, h1, rfl, bv_to_z_lit hM false h0 h1, bv_to_z_lit hM true h0 h1⟩

theorem lit_val' {FS ρ z t N n} {x : BitVec n} (s : Bool) (h : TB (.mk (.bitVec z) t) N)
    (e : eval FS ρ (.mk (.bitVec z) t) = some (.bv n x)) : bv_to_z s N z = bvz s x := by
  have := lit_val h e; cases s
  · exact this.2.2.2.2.2.2.1
  · exact this.2.2.2.2.2.2.2

theorem neg_inv {FS ρ c a t n} {x : BitVec n}
    (h : eval FS ρ (.mk (.unop (.neg c) a) t) = some (.bv n x)) :
    ∃ xa, eval FS ρ a = some (.bv n xa) ∧ (c = true → xa ≠ BitVec.intMin n) ∧ x = -xa := by
  obtain ⟨m, xa, ea, hc, hv⟩ := eval_neg_eq_some h
  simp at hv; obtain ⟨rfl, hv⟩ := hv; cases hv
  exact ⟨xa, ea, hc, rfl⟩

theorem bvz_neg {n : Nat} {x : BitVec n} (h : x ≠ BitVec.intMin n) :
    bvz true (-x) = - bvz true x := by
  simp only [bvz, ite_true]
  exact toInt_neg' (pos_of_ne_intMin h) (toInt_ne_of_ne_intMin h)

theorem ne_intMin_of_bvz {n : Nat} (hn : 0 < n) {x : BitVec n}
    (h : bvz true x ≠ min_for true n) : x ≠ BitVec.intMin n := by
  intro e; apply h; rw [min_for_eq]; simp only [bvz, ite_true]
  exact (eq_intMin_iff hn).1 e

theorem ite_inv {FS ρ g a b t v} (h : eval FS ρ (.mk (.triop .ite g a b) t) = some v) :
    (eval FS ρ g = some (.bool true) ∧ eval FS ρ a = some v) ∨
      (eval FS ρ g = some (.bool false) ∧ eval FS ρ b = some v) := by
  rw [eval_ite (eval_WT h)] at h
  split at h
  · exact Or.inl ⟨‹_›, h⟩
  · exact Or.inr ⟨‹_›, h⟩
  · simp at h

@[simp] theorem bvz_zero {n : Nat} (s : Bool) : bvz s (0 : BitVec n) = 0 := by
  cases s <;> simp [bvz]

theorem eval_val_inj {FS ρ t n m} {x : BitVec n} {y : BitVec m}
    (h1 : eval FS ρ t = some (.bv n x)) (h2 : eval FS ρ t = some (.bv m y)) :
    n = m ∧ HEq x y := by
  rw [h1] at h2; simpa using h2

theorem eval_val_eq {FS ρ t n} {x y : BitVec n}
    (h1 : eval FS ρ t = some (.bv n x)) (h2 : eval FS ρ t = some (.bv n y)) : x = y := by
  rw [h1] at h2; simpa using h2

theorem TB_add_inv {c a b t n} (h : TB (.mk (.binop (.add c) a b) t) n) : 0 < n ∧ TB a n ∧ TB b n :=
  TB_arith_inv (op := .add c) trivial h
theorem TB_sub_inv {c a b t n} (h : TB (.mk (.binop (.sub c) a b) t) n) : 0 < n ∧ TB a n ∧ TB b n :=
  TB_arith_inv (op := .sub c) trivial h
theorem TB_mul_inv {c a b t n} (h : TB (.mk (.binop (.mul c) a b) t) n) : 0 < n ∧ TB a n ∧ TB b n :=
  TB_arith_inv (op := .mul c) trivial h
theorem TB_div_inv {s a b t n} (h : TB (.mk (.binop (.div s) a b) t) n) : 0 < n ∧ TB a n ∧ TB b n :=
  TB_arith_inv (op := .div s) trivial h

/-- Rewrites the size of a term of known width. -/
macro "rsz " h:term:max loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| (try rw [TB_size $h] $(loc)?) <;> (try rw [TB_mk_size $h] $(loc)?) <;>
    (try rw [TB_sz $h] $(loc)?))

@[simp] theorem bvz_zero' {n : Nat} (s : Bool) : bvz s (0#n) = 0 := by
  cases s <;> simp [bvz]

theorem bvz_false_one {n : Nat} (hn : 0 < n) : bvz false (1#n) = 1 := by
  simp only [bvz, Bool.false_eq_true, ite_false, BitVec.toNat_ofNat]
  have : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  rw [Nat.mod_eq_of_lt this]; rfl

theorem Refines.ite_split {FS : FloatSem} {spec a b : Term} {c : Prop} [Decidable c]
    (h1 : c → Refines FS spec a) (h2 : ¬c → Refines FS spec b) :
    Refines FS spec (if c then a else b) := by
  split
  · exact h1 ‹_›
  · exact h2 ‹_›

theorem max_for_false (n : Nat) : max_for false n = 2 ^ n - 1 := by rw [max_for_eq]; simp
theorem min_for_false (n : Nat) : min_for false n = 0 := by simp [min_for]

/-! ## Signed comparisons with an unsigned-checked operand -/

theorem TBool_O_cmp {FS : FloatSem} {O : Ops} (hO : O.Sound FS) (le s : Bool) {a b N} (hN : 0 < N) (ha : TB a N)
    (hb : TB b N) : TBool (if le then O.bv_leq s a b else O.bv_lt s a b) := by
  cases le
  · exact TBool_O_lt hO hN ha hb
  · exact TBool_O_leq hO hN ha hb

theorem eval_O_cmp {FS : FloatSem} {O : Ops} {ρ : Env} (hO : O.Sound FS) (le s : Bool) {a b N n} {x y : BitVec n}
    (hN : 0 < N) (ha : TB a N) (hb : TB b N)
    (ea : eval FS ρ a = some (.bv n x)) (eb : eval FS ρ b = some (.bv n y)) :
    eval FS ρ (if le then O.bv_leq s a b else O.bv_lt s a b) = some (.bool (cmpv le s x y)) := by
  cases le
  · simp only [Bool.false_eq_true, ite_false, cmpv]; exact eval_O_lt hO hN ha hb ea eb
  · simp only [ite_true, cmpv]; exact eval_O_leq hO hN ha hb ea eb

theorem TB_sign_bit {N : Int} (hN : 0 < N) : TB (mk_bv N (zshiftl 1 (N - 1))) N := TB_masked hN

theorem signed_to_unsigned_left {FS : FloatSem} {O : Ops} (hO : O.Sound FS) (le : Bool) (c : Int) (T : Ty)
    (v2 : Term) :
    Refines FS (.mk (.binop (cmpOp le true) (.mk (.bitVec c) T) v2) .bool)
      (signed_to_unsigned_cmp O le true c (.mk (.bitVec c) T) v2) := by
  refine cmp_refines (fun N hN h1 h2 => ?_) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  · simp only [signed_to_unsigned_cmp, TB_size h1, ite_true]
    have hc := TBool_O_cmp hO le false hN h1 h2
    split
    · exact TBool_O_and hO hc (TBool_O_lt hO hN h2 (TB_sign_bit hN))
    · exact TBool_O_or hO (TBool_O_lt hO hN h2 (TB_sign_bit hN)) hc
  · subst hn
    simp only [signed_to_unsigned_cmp, TB_size h1, ite_true]
    have hsb := TB_sign_bit hN
    have esb : eval FS ρ (mk_bv (↑n) (zshiftl 1 (↑n - 1))) =
        some (.bv n (BitVec.ofInt n (2 ^ (n - 1)))) := eval_sign_bit hn0
    have ein := eval_O_lt (s := false) hO hN h2 hsb e2 esb
    rw [bvz_sign_bit hn0] at ein
    have ecmp := eval_O_cmp hO le false hN h1 h2 e1 e2
    have hcv := lit_val' true h1 e1
    have hx := bvz_true_cases hn0 x; have hy := bvz_true_cases hn0 y
    have := two_pow_succ_pred (N := n) hn0
    have := bvz_false_range x; have := bvz_false_range y
    by_cases hnn : bv_to_z true ↑n c ≥ 0
    · simp only [hnn, decide_true, ite_true]
      refine eval_O_and hO (TBool_O_cmp hO le false hN h1 h2) (TBool_O_lt hO hN h2 hsb) _ ?_
      rw [ecmp, ein, pand_bool]
      cases le <;> simp only [cmpv, Bool.false_eq_true, ite_false, ite_true, Option.some.injEq,
        Val.bool.injEq] <;> rw [Bool.eq_iff_iff] <;>
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] <;> omega
    · simp only [hnn, decide_false, Bool.false_eq_true, ite_false]
      refine eval_O_or hO (TBool_O_lt hO hN h2 hsb) (TBool_O_cmp hO le false hN h1 h2) _ ?_
      rw [ecmp, ein, por_bool]
      cases le <;> simp only [cmpv, Bool.false_eq_true, ite_false, ite_true, Option.some.injEq,
        Val.bool.injEq] <;> rw [Bool.eq_iff_iff] <;>
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] <;> omega

theorem signed_to_unsigned_right {FS : FloatSem} {O : Ops} (hO : O.Sound FS) (le : Bool) (c : Int) (T : Ty)
    (v2 : Term) :
    Refines FS (.mk (.binop (cmpOp le true) v2 (.mk (.bitVec c) T)) .bool)
      (signed_to_unsigned_cmp O le false c v2 (.mk (.bitVec c) T)) := by
  refine cmp_refines (fun N hN h1 h2 => ?_) (fun ρ N n x y hN h1 h2 hn hn0 e1 e2 => ?_)
  · simp only [signed_to_unsigned_cmp, TB_size h1, Bool.false_eq_true, ite_false]
    have hc := TBool_O_cmp hO le false hN h1 h2
    split
    · exact TBool_O_or hO hc (TBool_O_leq hO hN (TB_sign_bit hN) h1)
    · exact TBool_O_and hO (TBool_O_leq hO hN (TB_sign_bit hN) h1) hc
  · subst hn
    simp only [signed_to_unsigned_cmp, TB_size h1, Bool.false_eq_true, ite_false]
    have hsb := TB_sign_bit hN
    have esb : eval FS ρ (mk_bv (↑n) (zshiftl 1 (↑n - 1))) =
        some (.bv n (BitVec.ofInt n (2 ^ (n - 1)))) := eval_sign_bit hn0
    have ein := eval_O_leq (s := false) hO hN hsb h1 esb e1
    rw [bvz_sign_bit hn0] at ein
    have ecmp := eval_O_cmp hO le false hN h1 h2 e1 e2
    have hcv := lit_val' true h2 e2
    have hx := bvz_true_cases hn0 x; have hy := bvz_true_cases hn0 y
    have := two_pow_succ_pred (N := n) hn0
    have := bvz_false_range x; have := bvz_false_range y
    by_cases hnn : bv_to_z true ↑n c ≥ 0
    · simp only [hnn, decide_true, ite_true]
      refine eval_O_or hO (TBool_O_cmp hO le false hN h1 h2) (TBool_O_leq hO hN hsb h1) _ ?_
      rw [ecmp, ein, por_bool]
      cases le <;> simp only [cmpv, Bool.false_eq_true, ite_false, ite_true, Option.some.injEq,
        Val.bool.injEq] <;> rw [Bool.eq_iff_iff] <;>
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] <;> omega
    · simp only [hnn, decide_false, Bool.false_eq_true, ite_false]
      refine eval_O_and hO (TBool_O_leq hO hN hsb h1) (TBool_O_cmp hO le false hN h1 h2) _ ?_
      rw [ein, ecmp, pand_bool]
      cases le <;> simp only [cmpv, Bool.false_eq_true, ite_false, ite_true, Option.some.injEq,
        Val.bool.injEq] <;> rw [Bool.eq_iff_iff] <;>
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] <;> omega

/-! ## Upper bounds of unsigned values -/

@[simp] theorem none_orElse' {α} (b : Option α) : (none <|> b) = b := rfl
@[simp] theorem some_orElse' {α} (a : α) (b : Option α) : (some a <|> b) = some a := rfl

theorem two_pow_mono {a b : Nat} (h : a ≤ b) : (2 : Int) ^ a ≤ 2 ^ b := by
  exact_mod_cast Nat.pow_le_pow_right (by omega) h

theorem toNat_lt_pow_of {n : Nat} {x : BitVec n} {k : Int} (h : (n : Int) ≤ k) :
    (x.toNat : Int) < 2 ^ k.toNat := by
  have := toNat_lt' x
  have : (2 : Int) ^ n ≤ 2 ^ k.toNat := two_pow_mono (by omega)
  omega

theorem eval_bitAnd_inv {FS ρ a b t n} {x : BitVec n}
    (h : eval FS ρ (.mk (.binop .bitAnd a b) t) = some (.bv n x)) :
    ∃ xa xb, eval FS ρ a = some (.bv n xa) ∧ eval FS ρ b = some (.bv n xb) ∧ x = xa &&& xb := by
  rw [eval_binop (eval_WT h)] at h; simp only [evBinop] at h
  obtain ⟨m, xa, xb, ea, eb, e⟩ := bvBin_eq_some.1 h
  simp at e; obtain ⟨rfl, e⟩ := e; cases e
  exact ⟨xa, xb, ea, eb, rfl⟩

theorem eval_zext_inv {FS ρ k a t n} {x : BitVec n}
    (h : eval FS ρ (.mk (.unop (.bvExtend false k) a) t) = some (.bv n x)) :
    ∃ m xa, eval FS ρ a = some (.bv m xa) ∧ x.toNat = xa.toNat := by
  rw [eval_unop (eval_WT h)] at h
  revert h
  rcases eval FS ρ a with _ | ⟨_ | ⟨m, xa⟩ | _ | _ | _ | _⟩ <;> simp [evUnop]
  intro h1 h2; subst h1
  refine ⟨m, xa, by simp, ?_⟩
  cases eq_of_heq h2
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le xa.isLt (Nat.pow_le_pow_right (by omega) (by omega)))

theorem TB_zext_inv {k a t n} (h : TB (.mk (.unop (.bvExtend false k) a) t) n) :
    ∃ m, TB a m := by
  have ⟨w1, w2⟩ := WT_unop.1 h.1
  simp only [Unop.WT] at w1
  obtain ⟨m, _, ha, _⟩ := w1
  exact ⟨m, w2, ha⟩

theorem msb_bound_aux {FS : FloatSem} {ρ : Env} (K : Nat) : ∀ (v : Term), sizeOf v < K →
    ∀ {n : Nat} {x : BitVec n} {N : Int}, TB v N → eval FS ρ v = some (.bv n x) →
    (x.toNat : Int) < 2 ^ (msb_of v + 1).toNat := by
  induction K with
  | zero => intro v h; omega
  | succ K ih =>
  intro v hK n x N hv ev
  have hw := eval_bv_width hv.2 ev
  have hdef : (x.toNat : Int) < 2 ^ (size v - 1 + 1).toNat := by
    rw [TB_size hv]; exact toNat_lt_pow_of (by omega)
  rw [msb_of.eq_def]
  rcases v with ⟨k, T⟩
  cases k
  all_goals try (simp only [firstSome]; exact hdef)
  case bitVec z =>
    obtain ⟨-, -, -, h0, h1, rfl, -⟩ := lit_val hv ev
    by_cases hz : z > 0
    · simp only [firstSome, hz, decide_true, ite_true, some_orElse', Option.getD_some]
      have : (log2 z + 1).toNat = Nat.log2 z.toNat + 1 := by simp [log2] <;> omega
      rw [this]
      have := Nat.lt_log2_self (n := z.toNat)
      simp only [BitVec.toNat_ofInt]
      have e : z % ((2 ^ n : Nat) : Int) = z := Int.emod_eq_of_lt h0 (by push_cast; exact h1)
      rw [e]
      have : ((z.toNat : Nat) : Int) = z := by omega
      rw [Int.toNat_of_nonneg h0]; rw [← this]; exact_mod_cast Nat.lt_log2_self
    · simp only [firstSome, hz, decide_false, Bool.false_eq_true, ite_false]
      by_cases hz0 : z = 0
      · simp only [hz0, decide_true, ite_true, none_orElse', some_orElse',
          Option.getD_some]
        subst hz0; exact hdef
      · simp only [hz0, decide_false, Bool.false_eq_true, ite_false, none_orElse']
        exact hdef
  case unop op a =>
    cases op
    all_goals try (simp only [firstSome]; exact hdef)
    case bvExtend s k =>
      cases s
      · simp only [firstSome, none_orElse', some_orElse', Option.getD_some]
        obtain ⟨m, xa, ea, hx⟩ := eval_zext_inv ev
        obtain ⟨M, hM⟩ := TB_zext_inv hv
        rw [hx]; exact ih a (by simp at hK ⊢; omega) hM ea
      · simp only [firstSome]; exact hdef
  case binop op a b =>
    cases op
    all_goals try (simp only [firstSome]; exact hdef)
    case bitAnd =>
      simp only [firstSome, none_orElse', some_orElse', Option.getD_some]
      obtain ⟨xa, xb, ea, eb, rfl⟩ := eval_bitAnd_inv ev
      obtain ⟨-, ha, hb⟩ := TB_arith_inv (op := .bitAnd) trivial hv
      have b1 := ih a (by simp at hK ⊢; omega) ha ea
      have b2 := ih b (by simp at hK ⊢; omega) hb eb
      have l1 : (xa &&& xb).toNat ≤ xa.toNat := by rw [BitVec.toNat_and]; exact Nat.and_le_left
      have l2 : (xa &&& xb).toNat ≤ xb.toNat := by rw [BitVec.toNat_and]; exact Nat.and_le_right
      by_cases hm : msb_of a ≤ msb_of b <;> simp only [zmin, hm, decide_true, decide_false,
        ite_true, Bool.false_eq_true, ite_false] <;> omega
  case triop op a b c =>
    cases op
    all_goals try (simp only [firstSome]; exact hdef)
    case ite =>
      simp only [firstSome, none_orElse', some_orElse', Option.getD_some]
      obtain ⟨-, hb, hc⟩ := TB_ite_inv hv
      have m1 := two_pow_mono (a := (msb_of c + 1).toNat) (b := (msb_of b + 1).toNat)
      have m2 := two_pow_mono (a := (msb_of b + 1).toNat) (b := (msb_of c + 1).toNat)
      rcases ite_inv ev with ⟨-, e⟩ | ⟨-, e⟩
      · have := ih b (by simp at hK ⊢; omega) hb e
        by_cases hm : msb_of b ≥ msb_of c <;> simp only [zmax, hm, decide_true, decide_false,
          ite_true, Bool.false_eq_true, ite_false]
        · exact this
        · have := m2 (by omega); omega
      · have := ih c (by simp at hK ⊢; omega) hc e
        by_cases hm : msb_of b ≥ msb_of c <;> simp only [zmax, hm, decide_true, decide_false,
          ite_true, Bool.false_eq_true, ite_false]
        · have := m1 (by omega); omega
        · exact this

theorem msb_bound {FS : FloatSem} {ρ : Env} {v : Term} {n : Nat} {x : BitVec n} {N : Int}
    (hv : TB v N) (ev : eval FS ρ v = some (.bv n x)) :
    (x.toNat : Int) < 2 ^ (msb_of v + 1).toNat :=
  msb_bound_aux (sizeOf v + 1) v (by omega) hv ev

theorem le_unsigned_ub {FS : FloatSem} {ρ : Env} {v : Term} {n : Nat} {x : BitVec n} {N : Int}
    (hv : TB v N) (ev : eval FS ρ v = some (.bv n x)) : bvz false x ≤ unsigned_ub v := by
  have := msb_bound hv ev
  simp only [bvz, Bool.false_eq_true, ite_false, unsigned_ub, zshiftl, Int.one_mul]
  omega

/-! ## Sign tests (`lt_zero_aux`) -/

theorem TB_ext_inv {s k a t n} (h : TB (.mk (.unop (.bvExtend s k) a) t) n) :
    ∃ m, 0 < m ∧ TB a m ∧ 0 ≤ k ∧ n = m + k := by
  have ⟨w1, w2⟩ := WT_unop.1 h.1
  simp only [Unop.WT] at w1
  obtain ⟨m, hm, ha, hk, ht⟩ := w1
  have := h.2; simp only [Term.ty_mk] at this
  rw [this] at ht; simp at ht
  exact ⟨m, hm, ⟨w2, ha⟩, hk, ht⟩

theorem eval_sext_inv {FS ρ k a t n} {x : BitVec n}
    (h : eval FS ρ (.mk (.unop (.bvExtend true k) a) t) = some (.bv n x)) :
    ∃ m xa, eval FS ρ a = some (.bv m xa) ∧ x.msb = xa.msb := by
  rw [eval_unop (eval_WT h)] at h
  revert h
  rcases eval FS ρ a with _ | ⟨_ | ⟨m, xa⟩ | _ | _ | _ | _⟩ <;> simp [evUnop]
  intro h1 h2; subst h1
  refine ⟨m, xa, by simp, ?_⟩
  cases eq_of_heq h2
  rw [BitVec.msb_eq_toInt, BitVec.msb_eq_toInt, BitVec.toInt_signExtend_of_le (by omega)]

theorem eval_zext_inv' {FS ρ k a t n} {x : BitVec n}
    (h : eval FS ρ (.mk (.unop (.bvExtend false k) a) t) = some (.bv n x)) :
    ∃ m xa, eval FS ρ a = some (.bv m xa) ∧ n = m + k.toNat ∧ x.toNat = xa.toNat := by
  rw [eval_unop (eval_WT h)] at h
  revert h
  rcases eval FS ρ a with _ | ⟨_ | ⟨m, xa⟩ | _ | _ | _ | _⟩ <;> simp [evUnop]
  intro h1 h2; subst h1
  refine ⟨m, xa, by simp, rfl, ?_⟩
  cases eq_of_heq h2
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le xa.isLt (Nat.pow_le_pow_right (by omega) (by omega)))

theorem eval_rem_inv {FS ρ s a b t n} {x : BitVec n}
    (h : eval FS ρ (.mk (.binop (.rem s) a b) t) = some (.bv n x)) :
    ∃ xa xb, eval FS ρ a = some (.bv n xa) ∧ eval FS ρ b = some (.bv n xb) ∧
      x = if s then xa.srem xb else xa.umod xb := by
  rw [eval_binop (eval_WT h)] at h; simp only [evBinop] at h
  obtain ⟨m, xa, xb, ea, eb, e⟩ := bvBin_eq_some.1 h
  simp at e; obtain ⟨rfl, e⟩ := e; cases e
  exact ⟨xa, xb, ea, eb, rfl⟩

theorem eval_concat_inv {FS ρ a b t n} {x : BitVec n}
    (h : eval FS ρ (.mk (.binop .bvConcat a b) t) = some (.bv n x)) :
    ∃ m xa, eval FS ρ a = some (.bv m xa) ∧ ∃ k, ∃ xb : BitVec k, eval FS ρ b = some (.bv k xb) ∧
      x.msb = (if m = 0 then xb.msb else xa.msb) := by
  rw [eval_binop (eval_WT h)] at h
  generalize ea : eval FS ρ a = oa at h
  generalize eb : eval FS ρ b = ob at h
  rcases oa with _ | ⟨_ | ⟨m, xa⟩ | _ | _ | _ | _⟩ <;>
    rcases ob with _ | ⟨_ | ⟨k, xb⟩ | _ | _ | _ | _⟩ <;> simp [evBinop] at h
  obtain ⟨rfl, h2⟩ := h
  cases eq_of_heq h2
  exact ⟨m, xa, rfl, k, xb, rfl, BitVec.msb_append⟩

theorem TB_concat_inv {a b t n} (h : TB (.mk (.binop .bvConcat a b) t) n) :
    ∃ m, 0 < m ∧ TB a m := by
  have ⟨w1, wa, wb⟩ := WT_binop.1 h.1
  simp only [Binop.WT] at w1
  obtain ⟨m, k, hm, hk, ha, hb, ht⟩ := w1
  exact ⟨m, hm, wa, ha⟩

theorem TB_not_inv {a t n} (h : TB (.mk (.unop .bvNot a) t) n) : 0 < n ∧ TB a n := by
  have ⟨w1, w2⟩ := WT_unop.1 h.1
  simp only [Unop.WT] at w1
  obtain ⟨n', hn', ha, ht⟩ := w1
  have := h.2; simp only [Term.ty_mk] at this
  rw [this, ha] at ht; cases ht
  exact ⟨hn', w2, ha⟩

theorem eval_not_inv {FS ρ a t n} {x : BitVec n}
    (h : eval FS ρ (.mk (.unop .bvNot a) t) = some (.bv n x)) :
    ∃ xa, eval FS ρ a = some (.bv n xa) ∧ x = ~~~xa := by
  rw [eval_unop (eval_WT h)] at h
  revert h
  rcases eval FS ρ a with _ | ⟨_ | ⟨m, xa⟩ | _ | _ | _ | _⟩ <;> simp [evUnop]
  intro h1 h2; subst h1
  exact ⟨xa, by simp, (eq_of_heq h2).symm⟩

section O
variable {FS : FloatSem} {O : Ops} (hO : O.Sound FS)
include hO

omit hO in
/-- The default case of `lt_zero_aux`. -/
theorem lt_zero_default {v : Term} {N : Int} (hN : 0 < N) (hv : TB v N) :
    TBool (Term.mk (.binop (.lt true) v (bv_zero (size v))) .bool) ∧
      ∀ ρ n (x : BitVec n), eval FS ρ v = some (.bv n x) →
        eval FS ρ (Term.mk (.binop (.lt true) v (bv_zero (size v))) .bool) =
          some (.bool x.msb) := by
  rw [TB_size hv]
  have hT := TBool_cmp (op := .lt true) ⟨true, .inl rfl⟩ hN hv (TB_zero hN) rfl
  refine ⟨hT, fun ρ n x e => ?_⟩
  have hw := eval_bv_width hv.2 e
  obtain ⟨rfl, hn0⟩ := hw
  rw [eval_lt_of hT.1 e (eval_zero hn0), BitVec.msb_eq_toInt]
  simp [bvz]

theorem TBool_not_eq_0 {v : Term} {N : Int} (hN : 0 < N) (hv : TB v N) :
    TBool (O.b_not (O.sem_eq v (bv_zero (size v)))) := by
  rw [TB_size hv]; exact TBool_O_not hO (TBool_O_eq hO hv (TB_zero hN))

theorem eval_not_eq_0 {v : Term} {N : Int} (hN : 0 < N) (hv : TB v N) {ρ n} {x : BitVec n}
    (e : eval FS ρ v = some (.bv n x)) :
    eval FS ρ (O.b_not (O.sem_eq v (bv_zero (size v)))) = some (.bool (decide (x ≠ 0#n))) := by
  obtain ⟨rfl, hn0⟩ := eval_bv_width hv.2 e
  rw [TB_size hv]
  rw [eval_O_not hO (TBool_O_eq hO hv (TB_zero hN))
    (eval_O_eq hO hv.1 (TB_zero hN).1 (hv.2.trans (TB_zero hN).2.symm) e (eval_zero hn0))]
  simp

theorem lt_zero_aux_sound (K : Nat) : ∀ (v : Term), sizeOf v < K → ∀ {N : Int}, 0 < N → TB v N →
    TBool (lt_zero_aux O v) ∧ ∀ ρ n (x : BitVec n), eval FS ρ v = some (.bv n x) →
      eval FS ρ (lt_zero_aux O v) = some (.bool x.msb) := by
  induction K with
  | zero => intro v h; omega
  | succ K ih =>
  intro v hK N hN hv
  have hdef := lt_zero_default (FS := FS) hN hv
  rw [lt_zero_aux.eq_def]
  rcases v with ⟨k, T⟩
  cases k
  all_goals dsimp only
  all_goals try (simp only [firstSome]; exact hdef)
  case unop op a =>
    cases op
    all_goals try (simp only [firstSome]; exact hdef)
    case bvExtend s k =>
      obtain ⟨m, hm, ha, hk0, rfl⟩ := TB_ext_inv hv
      cases s
      · by_cases hk : k > 0
        · simp only [firstSome, hk, decide_true, ite_true, none_orElse', some_orElse',
            Option.getD_some]
          refine ⟨TBool_false, fun ρ n x e => ?_⟩
          obtain ⟨m', xa, ea, rfl, hx⟩ := eval_zext_inv' e
          obtain ⟨hm', -⟩ := eval_bv_width ha.2 ea
          rw [eval_v_false, BitVec.msb_eq_decide, hx]
          have := xa.isLt
          have : 2 ^ m' ≤ 2 ^ (m' + k.toNat - 1) := Nat.pow_le_pow_right (by omega) (by omega)
          simp; omega
        · simp only [firstSome, hk, decide_false, Bool.false_eq_true, ite_false, none_orElse']
          exact hdef
      · simp only [firstSome, some_orElse', Option.getD_some]
        have := ih a (by simp at hK ⊢; omega) hm ha
        refine ⟨this.1, fun ρ n x e => ?_⟩
        obtain ⟨m', xa, ea, hx⟩ := eval_sext_inv e
        rw [hx]; exact this.2 ρ m' xa ea
    case bvNot =>
      simp only [firstSome, none_orElse', some_orElse', Option.getD_some]
      obtain ⟨-, ha⟩ := TB_not_inv hv
      have := ih a (by simp at hK ⊢; omega) hN ha
      refine ⟨TBool_O_not hO this.1, fun ρ n x e => ?_⟩
      obtain ⟨xa, ea, rfl⟩ := eval_not_inv e
      obtain ⟨-, hn0⟩ := eval_bv_width ha.2 ea
      rw [eval_O_not hO this.1 (this.2 ρ n xa ea), BitVec.msb_not]
      simp [hn0]
    case bvOfBool k =>
      by_cases hk : k > 1
      · simp only [firstSome, hk, decide_true, ite_true, none_orElse', some_orElse',
          Option.getD_some]
        refine ⟨TBool_false, fun ρ n x e => ?_⟩
        obtain ⟨bb, -, hx⟩ := eval_ofBool_eq_some e
        simp at hx; obtain ⟨rfl, hx⟩ := hx
        rw [eval_v_false, BitVec.msb_eq_decide]
        have : 2 ≤ 2 ^ (k.toNat - 1) := by
          have := Nat.pow_le_pow_right (n := 2) (by omega) (show 1 ≤ k.toNat - 1 by omega)
          simpa using this
        cases bb <;> simp at hx <;> subst hx <;> simp
        have : 1 < 2 ^ k.toNat := Nat.one_lt_two_pow (by omega)
        rw [Nat.mod_eq_of_lt this]; omega
      · simp only [firstSome, hk, decide_false, Bool.false_eq_true, ite_false, none_orElse']
        exact hdef
  case binop op a b =>
    cases op
    all_goals try (simp only [firstSome]; exact hdef)
    case rem s =>
      cases s
      · simp only [firstSome]; exact hdef
      · simp only [firstSome, none_orElse', some_orElse', Option.getD_some]
        obtain ⟨-, ha, hb⟩ := TB_arith_inv (op := .rem true) trivial hv
        have := ih a (by simp at hK ⊢; omega) hN ha
        refine ⟨TBool_O_and hO this.1 (TBool_not_eq_0 hO hN hv), fun ρ n x e => ?_⟩
        refine eval_O_and hO this.1 (TBool_not_eq_0 hO hN hv) _ ?_
        obtain ⟨xa, xb, ea, eb, hx⟩ := eval_rem_inv e
        rw [this.2 ρ n xa ea, eval_not_eq_0 hO hN hv e, pand_bool]
        simp only [ite_true] at hx; subst hx
        rw [BitVec.msb_srem]; rfl
    case bvConcat =>
      simp only [firstSome, none_orElse', some_orElse', Option.getD_some]
      obtain ⟨m, hm, ha⟩ := TB_concat_inv hv
      have := ih a (by simp at hK ⊢; omega) hm ha
      refine ⟨this.1, fun ρ n x e => ?_⟩
      obtain ⟨m', xa, ea, k, xb, eb, hx⟩ := eval_concat_inv e
      obtain ⟨-, hm0⟩ := eval_bv_width ha.2 ea
      have hm0 : m' ≠ 0 := by omega
      simp only [hx, hm0, ite_false]; exact this.2 ρ m' xa ea
  case triop op g a b =>
    cases op
    all_goals try (simp only [firstSome]; exact hdef)
    case ite =>
      simp only [firstSome, none_orElse', some_orElse', Option.getD_some]
      obtain ⟨-, ha, hb⟩ := TB_ite_inv hv
      have h1 := ih a (by simp at hK ⊢; omega) hN ha
      have h2 := ih b (by simp at hK ⊢; omega) hN hb
      by_cases he : equal (lt_zero_aux O a) (lt_zero_aux O b) = true
      · simp only [he, ite_true]
        simp only [equal, decide_eq_true_eq] at he
        refine ⟨h1.1, fun ρ n x e => ?_⟩
        rcases ite_inv e with ⟨-, e'⟩ | ⟨-, e'⟩
        · exact h1.2 ρ n x e'
        · rw [he]; exact h2.2 ρ n x e'
      · simp only [he, Bool.false_eq_true, ite_false]
        exact hdef

end O

/-! ## Division by a constant -/

theorem tdiv_core (C2 C1 X : Int) (h : C1 ≠ 0) :
    C2 = C2.tdiv C1 * C1 + C2.tmod C1 ∧ (0 ≤ C2 → 0 ≤ C2.tmod C1) ∧
    (C2 ≤ 0 → C2.tmod C1 ≤ 0) ∧ (C2.tmod C1 = 0 ↔ C1 ∣ C2) ∧
    (0 < C1 → -C1 < C2.tmod C1 ∧ C2.tmod C1 < C1) ∧
    (C1 < 0 → C1 < C2.tmod C1 ∧ C2.tmod C1 < -C1) ∧
    (X ≤ C2.tdiv C1 - 1 → (0 < C1 → X * C1 ≤ C2.tdiv C1 * C1 - C1) ∧
      (C1 < 0 → C2.tdiv C1 * C1 - C1 ≤ X * C1)) ∧
    (C2.tdiv C1 + 1 ≤ X → (0 < C1 → C2.tdiv C1 * C1 + C1 ≤ X * C1) ∧
      (C1 < 0 → X * C1 ≤ C2.tdiv C1 * C1 + C1)) ∧
    (X = C2.tdiv C1 → X * C1 = C2.tdiv C1 * C1) := by
  have e := Int.tmod_add_tdiv_mul C2 C1
  refine ⟨by omega, fun h => Int.tmod_nonneg _ h, fun h => ?_, ?_, fun h => ?_, fun h => ?_,
    fun hx => ⟨fun hc => ?_, fun hc => ?_⟩, fun hx => ⟨fun hc => ?_, fun hc => ?_⟩,
    fun hx => by rw [hx]⟩
  · have := Int.tmod_nonneg C1 (show 0 ≤ -C2 by omega)
    rw [Int.neg_tmod] at this; omega
  · exact ⟨fun h => Int.dvd_of_tmod_eq_zero h, fun h => Int.tmod_eq_zero_of_dvd h⟩
  · exact ⟨Int.lt_tmod_of_pos _ h, Int.tmod_lt_of_pos _ h⟩
  · have h1 := Int.lt_tmod_of_pos C2 (show 0 < -C1 by omega)
    have h2 := Int.tmod_lt_of_pos C2 (show 0 < -C1 by omega)
    rw [Int.tmod_neg] at h1 h2; omega
  · have := Int.mul_le_mul_of_nonneg_right hx (Int.le_of_lt hc)
    rw [Int.sub_mul, Int.one_mul] at this; exact this
  · have := Int.mul_le_mul_of_nonpos_right hx (Int.le_of_lt hc)
    rw [Int.sub_mul, Int.one_mul] at this; exact this
  · have := Int.mul_le_mul_of_nonneg_right hx (Int.le_of_lt hc)
    rw [Int.add_mul, Int.one_mul] at this; exact this
  · have := Int.mul_le_mul_of_nonpos_right hx (Int.le_of_lt hc)
    rw [Int.add_mul, Int.one_mul] at this; exact this

/-- Solves a comparison of [X * C1] with [C2], given the quotient. -/
macro "tdiv_omega " C2:term:max C1:term:max X:term:max h:term:max : tactic =>
  `(tactic| (obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := tdiv_core $C2 $C1 $X $h
             generalize Int.tmod $C2 $C1 = r at *
             generalize Int.tdiv $C2 $C1 = D at *
             rcases Int.lt_or_gt_of_ne $h with hs | hs
             · have b := e6 hs; clear e5 e6
               rcases Int.lt_trichotomy $X D with hX | hX | hX
               · have := (e7 (by omega)).2 hs; clear e7 e8 e9; omega
               · have := e9 hX; clear e7 e8 e9; omega
               · have := (e8 (by omega)).2 hs; clear e7 e8 e9; omega
             · have b := e5 hs; clear e5 e6
               rcases Int.lt_trichotomy $X D with hX | hX | hX
               · have := (e7 (by omega)).1 hs; clear e7 e8 e9; omega
               · have := e9 hX; clear e7 e8 e9; omega
               · have := (e8 (by omega)).1 hs; clear e7 e8 e9; omega))

theorem smtSDiv_of_ne {n : Nat} {x y : BitVec n} (hy : y ≠ 0#n) : x.smtSDiv y = x.sdiv y := by
  have hy' : -y ≠ 0#n := fun h => hy (BitVec.neg_eq_zero_iff.1 h)
  rw [BitVec.smtSDiv_eq, BitVec.sdiv]
  rcases x.msb <;> rcases y.msb <;> simp [BitVec.smtUDiv_eq, hy, hy']

theorem bvz_div {n : Nat} (hn : 0 < n) (s : Bool) {x y : BitVec n} (hy : bvz s y ≠ 0)
    (hov : ¬ (s = true ∧ bvz s x = min_for s n ∧ bvz s y = -1)) :
    bvz s (if s then x.smtSDiv y else x.smtUDiv y) = (bvz s x).tdiv (bvz s y) := by
  have hy0 : y ≠ 0#n := by rintro rfl; simp at hy
  cases s
  · simp only [Bool.false_eq_true, ite_false, BitVec.smtUDiv_eq, hy0, bvz, BitVec.toNat_udiv]
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]; simp
  · simp only [ite_true, smtSDiv_of_ne hy0, bvz]
    apply BitVec.toInt_sdiv_of_ne_or_ne
    by_cases hx : x = BitVec.intMin n
    · right; rintro rfl
      apply hov
      refine ⟨rfl, ?_, ?_⟩
      · rw [min_for_eq]; simp only [bvz, ite_true]; exact (eq_intMin_iff hn).1 hx
      · simp only [bvz, ite_true, BitVec.neg_one_eq_allOnes, BitVec.toInt_allOnes, hn, ite_true]
    · exact Or.inl hx

theorem lit_bvz_ne_zero {FS ρ z t N n} {x : BitVec n} (s : Bool) (h : TB (.mk (.bitVec z) t) N)
    (e : eval FS ρ (.mk (.bitVec z) t) = some (.bv n x)) (hz : z ≠ 0) : bvz s x ≠ 0 := by
  obtain ⟨rfl, -, hn, h0, h1, -, hf, -⟩ := lit_val h e
  simp only [bv_to_z_false] at hf
  cases s
  · omega
  · rcases bvz_true_cases hn x with ⟨-, e'⟩ | ⟨-, e'⟩ <;> omega

/-- `decide`, whatever its instance (the model may use classical ones). -/
theorem dec_true_iff {p : Prop} {i : Decidable p} : (@decide p i = true) = p := by
  cases i <;> simp_all

theorem dec_false_iff {p : Prop} {i : Decidable p} : (@decide p i = false) = ¬p := by
  cases i <;> simp_all

/-- A cancellable factor is a literal, read as a positive integer. -/
theorem cancellable_inv {s a N} (h : cancellable s a = true) (ha : TB a N) :
    ∃ z t, a = .mk (.bitVec z) t ∧ 0 < bv_to_z s N z := by
  obtain ⟨k, t⟩ := a
  have hT := ha.2; simp only [Term.ty_mk] at hT; subst hT
  have hs : size (Term.mk k (.bitVector N)) = N := by simp [size, size_of_ty]
  cases s
  · simp only [cancellable, Bool.false_eq_true, ite_false, sure_neq, hs, bv_zero] at h
    cases k <;> unfold sure_neq at h <;> simp [firstSome, ty] at h
    rename_i z
    obtain ⟨M, hM, hMN, h0, h1, _⟩ := TB_lit ha
    exact ⟨z, _, rfl, by rw [bv_to_z_false]; omega⟩
  · simp only [cancellable, ite_true, hs] at h
    cases k <;> simp [firstSome] at h
    exact ⟨_, _, rfl, h⟩

/-- [v] is a multiplication of [x] by [a], on either side. -/
def IsMulBy (c : Checked) (a x v : Term) : Prop :=
  ∃ t, v = .mk (.binop (.mul c) a x) t ∨ v = .mk (.binop (.mul c) x a) t

theorem TB_mulBy {c a x v N} (h : IsMulBy c a x v) (hv : TB v N) : TB a N ∧ TB x N := by
  obtain ⟨t, rfl | rfl⟩ := h
  · exact (TB_mul_inv hv).2
  · exact ⟨(TB_mul_inv hv).2.2, (TB_mul_inv hv).2.1⟩

theorem eval_mulBy {FS ρ c a x v m} {y : BitVec m} (s : Bool) (hc : checked_has s c = true)
    (h : IsMulBy c a x v) (e : eval FS ρ v = some (.bv m y)) :
    ∃ xa xx, eval FS ρ a = some (.bv m xa) ∧ eval FS ρ x = some (.bv m xx) ∧
      bvz s y = bvz s xa * bvz s xx := by
  obtain ⟨t, rfl | rfl⟩ := h
  · obtain ⟨xa, xx, ea, ex, hy, -⟩ := eval_mul_inv s hc e
    exact ⟨xa, xx, ea, ex, hy⟩
  · obtain ⟨xx, xa, ex, ea, hy, -⟩ := eval_mul_inv s hc e
    exact ⟨xa, xx, ea, ex, by rw [hy, Int.mul_comm]⟩

/-- Cancelling a common positive factor of two checked multiplications. -/
theorem mul_mul_refines {FS : FloatSem} {O : Ops} (hO : O.Sound FS) (le s : Bool)
    {c1 c2 a x y v1 v2} (h1 : IsMulBy c1 a x v1) (h2 : IsMulBy c2 a y v2)
    (hc1 : checked_has s c1 = true) (hc2 : checked_has s c2 = true)
    (hca : cancellable s a = true) :
    Refines FS (.mk (.binop (cmpOp le s) v1 v2) .bool)
      (if le then O.bv_leq s x y else O.bv_lt s x y) := by
  refine cmp_refines (fun N hN t1 t2 => TBool_O_cmp hO le s hN (TB_mulBy h1 t1).2 (TB_mulBy h2 t2).2)
    (fun ρ N n vx vy hN t1 t2 hn hn0 e1 e2 => ?_)
  subst hn
  obtain ⟨xa, xx, ea, ex, hy1⟩ := eval_mulBy s hc1 h1 e1
  obtain ⟨xa', yy, ea', ey, hy2⟩ := eval_mulBy s hc2 h2 e2
  have := eval_val_eq ea ea'; subst this
  have ta := (TB_mulBy h1 t1).1
  obtain ⟨z, t, rfl, hz⟩ := cancellable_inv hca ta
  rw [lit_val' s ta ea] at hz
  rw [eval_O_cmp hO le s hN (TB_mulBy h1 t1).2 (TB_mulBy h2 t2).2 ex ey]
  simp only [cmpv, hy1, hy2]
  cases le <;> simp [Int.mul_lt_mul_left hz, Int.mul_le_mul_left hz]

end CompareL
end Bvr
