import Bvr.Lib.Tactic
import Bvr.Lib.Float

/-!
# Lemmas for the resizing, conversion, float and pointer rules
-/

namespace Bvr.Lib

open Classical

/-- The type of a literal whose width is its own size, as in `bv_zero (size v)`
compared to `v`. -/
@[simp] theorem eq_bitVector_size_self {T : Ty} :
    T = .bitVector (size_of_ty T) ↔ ∃ m, T = .bitVector m :=
  ⟨fun h => ⟨_, h⟩, fun ⟨m, h⟩ => by subst h; rfl⟩

@[simp] theorem of_bool_eq (b : Bool) : of_bool b = .mk (.bool b) .bool := by
  cases b <;> rfl

attribute [simp] WT_bool

/-- The existentials of the typing of the resizing nodes, at known widths. -/
@[simp] theorem exists_pos_eq {a : Int} {p : Int → Prop} :
    (∃ n, 0 < n ∧ a = n ∧ p n) ↔ 0 < a ∧ p a :=
  ⟨fun ⟨_, h1, h2, h3⟩ => by subst h2; exact ⟨h1, h3⟩, fun ⟨h1, h2⟩ => ⟨_, h1, rfl, h2⟩⟩

@[simp] theorem exists_pos_eq₂ {a b : Int} {p : Int → Int → Prop} :
    (∃ n, 0 < n ∧ ∃ m, 0 < m ∧ a = n ∧ b = m ∧ p n m) ↔ 0 < a ∧ 0 < b ∧ p a b :=
  ⟨fun ⟨_, h1, _, h2, h3, h4, h5⟩ => by subst h3 h4; exact ⟨h1, h2, h5⟩,
    fun ⟨h1, h2, h3⟩ => ⟨_, h1, _, h2, rfl, rfl, h3⟩⟩

/-- A literal in range, read as an unsigned integer. -/
theorem to_z_bv_of_lit {z : Int} {T : Ty} (w : (Term.mk (.bitVec z) T).WT) :
    to_z false (bv_of_lit (.mk (.bitVec z) T)) = z := by
  obtain ⟨k, hk, hT, h0, h1⟩ := WT_bitVec.1 w
  rcases hT with rfl | rfl <;> simp [bv_of_lit, to_z, size_of_ty, toNat_ofInt_of_lt h0 h1] <;> omega

theorem ofInt_eq_zero_of_lt {n : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ n) :
    BitVec.ofInt n z = 0#n ↔ z = 0 := by
  rw [BitVec.toNat_eq, toNat_ofInt_of_lt h0 h1]; simp; omega

/-! ## Powers of two and lowest set bits of literals -/

@[simp] theorem log2_two_pow (k : Nat) : log2 ((2 : Int) ^ k) = k := by
  rw [show (2 : Int) ^ k = ((2 ^ k : Nat) : Int) by push_cast; rfl, log2, Int.toNat_natCast,
    Nat.log2_two_pow]

theorem testBit_two_mul (y i : Nat) : (2 * y).testBit i = (decide (0 < i) && y.testBit (i - 1)) := by
  cases i with
  | zero => simp
  | succ i => simp [Nat.testBit_succ, Nat.mul_div_cancel_left y (by omega : 0 < 2)]

theorem lowbit_spec : ∀ m : Nat, 0 < m →
    ∃ t, Nat.bitwise (fun a b => a && !b) m (m - 1) = 2 ^ t ∧ 2 ^ t ∣ m
  | m, hm => by
    by_cases ho : m % 2 = 1
    · refine ⟨0, Nat.eq_of_testBit_eq (fun i => ?_), by simp⟩
      rw [Nat.testBit_bitwise rfl]
      cases i with
      | zero => simp [ho]; omega
      | succ i =>
        simp only [Nat.testBit_succ, Nat.pow_zero]
        rw [show (m - 1) / 2 = m / 2 by omega]
        simp
    · have h2 : m / 2 < m := by omega
      obtain ⟨t, ht, hd⟩ := lowbit_spec (m / 2) (by omega)
      refine ⟨t + 1, Nat.eq_of_testBit_eq (fun i => ?_), ?_⟩
      · rw [Nat.pow_succ, Nat.mul_comm, ← ht, testBit_two_mul, Nat.testBit_bitwise rfl]
        cases i with
        | zero => simp; omega
        | succ i =>
          simp only [Nat.testBit_succ, Nat.add_sub_cancel]
          rw [Nat.testBit_bitwise rfl, show (m - 1) / 2 = m / 2 - 1 by omega]
          simp
      · rw [Nat.pow_succ]
        have := Nat.mul_dvd_mul hd (Nat.dvd_refl 2)
        rwa [Nat.div_mul_cancel (by omega : 2 ∣ m)] at this
termination_by m => m

/-- The bits of a literal below its lowest set bit are zero. -/
theorem lsb_dvd {n : Int} (h0 : 0 ≤ n) {j : Int} (hj : j < lsb n) (hj0 : 0 ≤ j) :
    2 ^ (j.toNat + 1) ∣ n.toNat := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  simp only [Int.toNat_natCast]
  rcases m with _ | k
  · exact Nat.dvd_zero _
  obtain ⟨t, ht, hd⟩ := lowbit_spec (k + 1) (by omega)
  have : lsb ((k + 1 : Nat) : Int) = t := by
    have hne : ((k + 1 : Nat) : Int) ≠ 0 := by omega
    simp only [lsb, hne, decide_false, Bool.false_eq_true, ↓reduceIte]
    show log2 (zland (Int.ofNat (k + 1)) (Int.negSucc k)) = t
    simp only [Nat.add_sub_cancel] at ht
    simp only [zland, log2, Int.ofNat_eq_natCast, Int.toNat_natCast, ht, Nat.log2_two_pow]
  rw [this] at hj
  exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hd

/-! ## Extraction of arithmetic -/

theorem getLsbD_add_of_dvd {w : Nat} (a b : BitVec w) {q : Nat} (h : 2 ^ q ∣ a.toNat) {p : Nat}
    (hp : p < q) : (a + b).getLsbD p = b.getLsbD p := by
  by_cases hw : p < w
  · simp only [BitVec.getLsbD, BitVec.toNat_add]
    rw [Nat.testBit_mod_two_pow, decide_eq_true hw, Bool.true_and]
    have e1 : (a.toNat + b.toNat).testBit p = ((a.toNat + b.toNat) % 2 ^ q).testBit p := by
      rw [Nat.testBit_mod_two_pow]; simp [hp]
    have e2 : b.toNat.testBit p = (b.toNat % 2 ^ q).testBit p := by
      rw [Nat.testBit_mod_two_pow]; simp [hp]
    rw [e1, e2, Nat.add_mod, (Nat.dvd_iff_mod_eq_zero ..).1 h, Nat.zero_add, Nat.mod_mod]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega)]

/-- Adding a constant whose lowest set bit is above the extracted bits. -/
theorem extractLsb'_add_lsb {w n : Nat} {i j z : Int} (x : BitVec w) (h0 : 0 ≤ z)
    (h1 : z < 2 ^ w) (hi : 0 ≤ i) (hij : i ≤ j) (hj : j < lsb z) (hn : j - i + 1 = n) :
    (BitVec.ofInt w z + x).extractLsb' i.toNat n = x.extractLsb' i.toNat n := by
  have hd := lsb_dvd h0 hj (by omega)
  ext t ht
  simp only [BitVec.getElem_extractLsb']
  rw [getLsbD_add_of_dvd _ _ (q := j.toNat + 1) (by rw [toNat_ofInt_of_lt h0 h1]; exact hd)
    (by omega)]

/-- Multiplying by a power of two above the extracted bits. -/
theorem extractLsb'_mul_pow2 {w n k : Nat} {i j : Int} (x : BitVec w) (hk : j < k)
    (hn : j - i + 1 = n) (hi : 0 ≤ i) :
    (BitVec.ofInt w (2 ^ k) * x).extractLsb' i.toNat n = 0#n := by
  have : BitVec.ofInt w ((2 : Int) ^ k) = BitVec.twoPow w k := by
    rw [show (2 : Int) ^ k = ((2 ^ k : Nat) : Int) by push_cast; rfl, BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_twoPow]
  rw [this, BitVec.twoPow_mul_eq_shiftLeft]
  ext t ht
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getElem_zero]
  simp; omega

/-- The remainder by a power of two below the extracted bits. -/
theorem extractLsb'_umod_pow2 {w n m k : Nat} {j : Int} (x : BitVec w) (hk : k < j)
    (hn : j + 1 = n) (hj : j < w) (hm : m = n) :
    x.extractLsb' 0 n % BitVec.setWidth n (BitVec.extractLsb' 0 m (BitVec.ofInt w (2 ^ k))) =
      (x % BitVec.ofInt w (2 ^ k)).extractLsb' 0 n := by
  subst hm
  have e : BitVec.ofInt w ((2 : Int) ^ k) = BitVec.ofNat w (2 ^ k) := by
    rw [show (2 : Int) ^ k = ((2 ^ k : Nat) : Int) by push_cast; rfl, BitVec.ofInt_natCast]
  have hkn : 2 ^ k < 2 ^ m := Nat.pow_lt_pow_right (by omega) (by omega)
  have hkw : 2 ^ k < 2 ^ w := Nat.lt_of_lt_of_le hkn (Nat.pow_le_pow_right (by omega) (by omega))
  rw [e]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_umod, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_ofNat,
    BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt hkw, Nat.mod_eq_of_lt hkn, Nat.mod_eq_of_lt hkn,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : k ≤ m)),
    Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (Nat.two_pow_pos _)) hkn)]

/-! ## Float literals -/

section

variable {FS : FloatSem}

/-- A comparison of float literals. -/
theorem Refines.fcmp_lits {op : Binop} (hop : op = .fEq ∨ op = .fLt ∨ op = .fLeq)
    {f1 f2 : FloatLit} {T1 T2 T : Ty} {b : Bool}
    (hsem : f2.prec = f1.prec → evBinop FS op (some f1.sem) (some f2.sem) = some (.bool b)) :
    Refines FS (.mk (.binop op (.mk (.float f1) T1) (.mk (.float f2) T2)) T) (of_bool b) := by
  refine Refines.intro (fun w => ⟨by simp, by simp [((WT_fcmp hop).1 w).2.2.1]⟩)
    (fun ρ v w w' e => ?_)
  obtain ⟨_, h2, _, w1, w2⟩ := (WT_fcmp hop).1 w
  rw [(WT_float.1 w1).1, (WT_float.1 w2).1] at h2
  rw [eval_binop w, eval_float w1, eval_float w2, hsem (by simpa using h2)] at e
  rw [eval_of_bool]; exact e

/-- A unary operation on a float literal, of the precision of the literal. -/
theorem Refines.funop_lit {op : Unop} (hop : op = .fAbs ∨ op = .fNeg ∨ op = .fSqrt ∨ ∃ rm, op = .fRound rm)
    {f g : FloatLit} {T : Ty}
    (hg : f.WF → g.prec = f.prec ∧ g.WF ∧ evUnop FS op (some f.sem) = some g.sem) :
    Refines FS (.mk (.unop op (.mk (.float f) T)) T) (.mk (.float g) T) :=
  Refines.lit_of_unop (fun w => by
      obtain ⟨_, -, w1⟩ := (WT_funop hop).1 w
      have hf := FloatLit.WF_of_WT w1
      exact ⟨by rw [(WT_float.1 w1).1, (hg hf).1], (hg hf).2.1⟩)
    (fun hf => (hg hf).2.2)

/-- A unary operation on floats that only reads the bits of its operand. -/
theorem Refines.funop_bits {op : Unop} (hop : op = .fAbs ∨ op = .fNeg)
    {F : ∀ {p}, FBits p → FBits p} (hF : ∀ p (x : FBits p), evUnop FS op (some (.float p x)) = some (.float p (F x)))
    {f : FloatLit} {T : Ty} :
    Refines FS (.mk (.unop op (.mk (.float f) T)) T) (.mk (.float ⟨f.prec, (F f.val).toNat⟩) T) :=
  Refines.funop_lit (by rcases hop with h | h <;> simp [h]) fun _ =>
    ⟨rfl, BitVec.isLt _, by simp [FloatLit.sem, hF, FloatLit.val_ofNat_toNat]⟩

/-- An idempotent operation on floats. -/
theorem Refines.funop_idem {op : Unop}
    (hidem : ∀ v, evUnop FS op (evUnop FS op v) = evUnop FS op v) {a : Term} {T : Ty} :
    Refines FS (.mk (.unop op (.mk (.unop op a) T)) T) (.mk (.unop op a) T) := by
  refine Refines.intro (fun w => ⟨(WT_unop.1 w).2, rfl⟩) (fun ρ v w w' e => ?_)
  rw [eval_unop w, eval_unop w'] at e; rw [eval_unop w', ← e, hidem]

/-- An involutive operation on floats. -/
theorem Refines.funop_invol {op : Unop} (hop : op = .fAbs ∨ op = .fNeg ∨ op = .fSqrt ∨ ∃ rm, op = .fRound rm)
    (hinv : ∀ v r, evUnop FS op (evUnop FS op v) = some r → v = some r) {a : Term} {T T' : Ty} :
    Refines FS (.mk (.unop op (.mk (.unop op a) T)) T') a := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · have ⟨_, hT, w1⟩ := (WT_funop hop).1 w
    have ⟨_, hT', w2⟩ := (WT_funop hop).1 w1
    exact ⟨w2, by simp_all⟩
  · rw [eval_unop w, eval_unop (WT_unop.1 w).2] at e; exact hinv _ _ e

/-- `fp.eq` against a float literal, given how the general case is decided. -/
theorem Refines.feq_lit {FS : FloatSem} {O : Ops} (hO : O.Sound FS) {f : FloatLit} {T : Ty}
    {v2 E : Term} (hE : Refines FS (sem_eq.spec (.mk (.float f) T) v2) E) :
    Refines FS (float_eq.spec (.mk (.float f) T) v2)
      (if f_is_nan f then v_false
       else if f_is_zero f then O.float_is_floatclass .zero v2 else E) := by
  have ev1 : ∀ ρ v, eval FS ρ (float_eq.spec (.mk (.float f) T) v2) = some v →
      ∃ y, eval FS ρ v2 = some (.float f.prec y) ∧ v = .bool (f.val.eq y) := by
    intro ρ v e
    have w := eval_WT e
    have ⟨_, w1, _⟩ := WT_binop.1 w
    rw [float_eq.spec, eval_binop w, eval_float w1] at e
    simp only [evBinop, fBin_eq_some, FloatLit.sem] at e
    obtain ⟨p, x, y, h1, h2, h3⟩ := e
    simp at h1; obtain ⟨rfl, h1⟩ := h1; subst h1
    simp at h3
    exact ⟨y, h2, h3.symm⟩
  split
  · rename_i hn
    refine Refines.intro (fun w => ⟨by simp, by simp [float_eq.spec]⟩) (fun ρ v w w' e => ?_)
    obtain ⟨y, _, rfl⟩ := ev1 ρ v e
    simp [FBits.eq_of_isNaN_left y (by simpa [f_is_nan] using hn)]
  · rename_i hn
    split
    · rename_i hz
      refine Refines.trans ?_ (hO.float_is_floatclass .zero v2)
      refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
      · obtain ⟨hp, h2, _, w1, w2⟩ := (WT_fcmp (Or.inl rfl)).1 w
        refine ⟨WT_unop.2 ⟨by simpa [Unop.WT, h2] using hp, w2⟩, rfl⟩
      · obtain ⟨y, hy, rfl⟩ := ev1 ρ v e
        rw [float_is_floatclass.spec, eval_unop w', hy]
        simp [evUnop, FBits.isClass, FBits.eq_of_isZero_left y hz]
    · rename_i hz
      refine Refines.trans ?_ hE
      refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
      · obtain ⟨hp, h2, _, w1, w2⟩ := (WT_fcmp (Or.inl rfl)).1 w
        exact ⟨WT_sem_eq.2 ⟨h2.symm, w1, w2⟩, rfl⟩
      · obtain ⟨y, hy, rfl⟩ := ev1 ρ v e
        have ⟨_, w1, _⟩ := WT_binop.1 w'
        rw [sem_eq.spec, eval_eq_of w' (eval_float w1) hy]
        simp only [f_is_nan, f_is_zero, Bool.not_eq_true] at hn hz
        simp [FloatLit.sem, FBits.eq_of_ne_left y hn hz]

end

/-! ## Tactics -/

open Lean Meta Elab Tactic

/-- Case splits on the first proposition `p` of a `decide p` or an `if p` of
the goal. -/
elab "bvr_split_decide" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let some e := t.find? (fun e => !e.hasLooseBVars &&
      (e.isAppOfArity ``Decidable.decide 2 || e.isAppOfArity ``ite 5))
    | throwError "bvr_split_decide: no decide"
  let p ← Term.exprToSyntax (if e.isAppOfArity ``ite 5 then e.getArg! 1 else e.getArg! 0)
  evalTactic (← `(tactic| by_cases hp : $p <;> simp only [hp, decide_true, decide_false,
    ↓reduceIte, Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.and_true,
    Bool.and_false, Bool.true_or, Bool.false_or, Bool.or_true, Bool.or_false] at ⊢))

/-- Proves an equality of bit-vectors bit by bit, the indices being linear. -/
macro "bvr_bits" : tactic => `(tactic| (
  ext i hi
  simp [BitVec.getElem_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getElem_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
  repeat' bvr_split_decide
  all_goals first | rfl | (exfalso; omega) | (simp; done) | (congr 1; omega)))

/-- The integers read from literals in range (`to_z false`) are their values.
(By `rw`, since they may occur in the widths of bit-vectors.) -/
macro "bvr_zlits" : tactic => `(tactic| (
  (repeat' rw [emod_two_pow_of_lt (by assumption) (by assumption)] at *)
  (repeat' rw [Int.max_eq_left (by assumption)] at *)))

/-- `bvr_wt`, with the integers of the literals in range. -/
macro "bvr_wt_r" : tactic => `(tactic| (
  intro w
  bvr_facts
  bvr_zlits
  (try simp_all [WT_bitVec])
  all_goals grind [size_of_ty, WT_bitVec]))

/-- Closes the value goals left by `bvr_sem_core`. -/
macro "bvr_close" : tactic => `(tactic| first
  | (simp only [BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle, decide_eq_true_eq,
      decide_eq_false_iff_not, Bool.not_eq_true, Bool.not_eq_false] at *; omega)
  | (grind [BitVec.neg_eq_not_add]; done)
  | (bvr_ovf; done)
  | ((try bvr_split); subst_vars; bvr_bits; done))

/-- `bvr_rule_core`, splitting all the `if`s of the body (rather than the
outermost one), so that the calls under them are lifted too. -/
macro "bvr_rule_core_r" : tactic => `(tactic| (
  intro FS O hO
  intros
  (try bvr_flags)
  (try subst_vars)
  simp only [bvr_spec, ty, mk_commut_binop]
  (repeat' split)
  all_goals (try bvr_lift_body)
  all_goals (try simp only [bvr_spec, ty])
  all_goals (try (first | exact Refines.refl | (bvr_comm; done)))
  all_goals (try first
    | apply Refines.denB (fun _ => rfl)
    | apply Refines.den
    | apply Refines.denB)))

/-- `bvr_rule_sem`, with the integers of the literals in range. -/
macro "bvr_rule_sem_r" : tactic => `(tactic| (
  bvr_rule_core_r
  all_goals first
    | (bvr_wt_r; done)
    | (bvr_sem_core
       all_goals bvr_zlits)))

/-- `bvr_rule`, with the integers of the literals in range, and the bitwise
equalities proved bit by bit. -/
macro "bvr_rule_r" : tactic => `(tactic| (
  bvr_rule_core_r
  all_goals first
    | (bvr_wt_r; done)
    | (bvr_sem_core
       all_goals bvr_zlits
       all_goals (try (bvr_close; done)))
    | skip))

end Bvr.Lib
