import Kanon.Lib.Tactic
import Kanon.Lib.Float

/-!
# Lemmas for the resizing, conversion, float and pointer rules
-/

namespace Kanon.Lib

open Classical

/-- The type of a literal whose width is its own size, as in `bv_zero (size v)`
compared to `v`. -/
@[simp] theorem eq_bitVector_size_self {T : Ty} :
    T = .TBitVector (size_of_ty T) ↔ ∃ m, T = .TBitVector m :=
  ⟨fun h => ⟨_, h⟩, fun ⟨m, h⟩ => by subst h; rfl⟩

@[simp] theorem of_bool_eq (b : Bool) : of_bool b = .mk (.Bool b) .TBool := by
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
theorem to_z_bv_of_lit {z : Int} {T : Ty} (w : (Term.mk (.BitVec z) T).WT) :
    to_z false (bv_of_lit (.mk (.BitVec z) T)) = z := by
  obtain ⟨k, hk, hT, h0, h1⟩ := WT_bitVec.1 w
  rcases hT with rfl | rfl <;> simp [bv_of_lit, to_z, size_of_ty, toNat_ofInt_of_lt h0 h1] <;> omega

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
theorem Refines.fcmp_lits {op : Binop} (hop : op = .FEq ∨ op = .FLt ∨ op = .FLeq)
    {f1 f2 : Float} {T1 T2 T : Ty} {b : Bool}
    (hsem : f2.prec = f1.prec → evBinop FS op (some f1.sem) (some f2.sem) = some (.bool b)) :
    Refines FS (.mk (.Binop op (.mk (.Float f1) T1) (.mk (.Float f2) T2)) T) (of_bool b) := by
  refine Refines.intro (fun w => ⟨by simp, by simp [((WT_fcmp hop).1 w).2.2.1]⟩)
    (fun ρ v w w' e => ?_)
  obtain ⟨_, h2, _, w1, w2⟩ := (WT_fcmp hop).1 w
  rw [(WT_float.1 w1).1, (WT_float.1 w2).1] at h2
  rw [eval_binop w, eval_float w1, eval_float w2, hsem (by simpa using h2)] at e
  rw [eval_of_bool]; exact e

/-- A unary operation on a float literal, of the precision of the literal. -/
theorem Refines.funop_lit {op : Unop} (hop : op = .FAbs ∨ op = .FNeg ∨ op = .FSqrt ∨ ∃ rm, op = .FRound rm)
    {f g : Float} {T : Ty}
    (hg : f.WF → g.prec = f.prec ∧ g.WF ∧ evUnop FS op (some f.sem) = some g.sem) :
    Refines FS (.mk (.Unop op (.mk (.Float f) T)) T) (.mk (.Float g) T) :=
  Refines.lit_of_unop (fun w => by
      obtain ⟨_, -, w1⟩ := (WT_funop hop).1 w
      have hf := Float.WF_of_WT w1
      exact ⟨by rw [(WT_float.1 w1).1, (hg hf).1], (hg hf).2.1⟩)
    (fun hf => (hg hf).2.2)

/-- A unary operation on floats that only reads the bits of its operand. -/
theorem Refines.funop_bits {op : Unop} (hop : op = .FAbs ∨ op = .FNeg)
    {F : ∀ {p}, FBits p → FBits p} (hF : ∀ p (x : FBits p), evUnop FS op (some (.float p x)) = some (.float p (F x)))
    {f : Float} {T : Ty} :
    Refines FS (.mk (.Unop op (.mk (.Float f) T)) T) (.mk (.Float ⟨f.prec, (F f.val).toNat⟩) T) :=
  Refines.funop_lit (by rcases hop with h | h <;> simp [h]) fun _ =>
    ⟨rfl, BitVec.isLt _, by simp [Float.sem, hF, Float.val_ofNat_toNat]⟩

/-- An idempotent operation on floats. -/
theorem Refines.funop_idem {op : Unop}
    (hidem : ∀ v, evUnop FS op (evUnop FS op v) = evUnop FS op v) {a : Term} {T : Ty} :
    Refines FS (.mk (.Unop op (.mk (.Unop op a) T)) T) (.mk (.Unop op a) T) := by
  refine Refines.intro (fun w => ⟨(WT_unop.1 w).2, rfl⟩) (fun ρ v w w' e => ?_)
  rw [eval_unop w, eval_unop w'] at e; rw [eval_unop w', ← e, hidem]

/-- An involutive operation on floats. -/
theorem Refines.funop_invol {op : Unop} (hop : op = .FAbs ∨ op = .FNeg ∨ op = .FSqrt ∨ ∃ rm, op = .FRound rm)
    (hinv : ∀ v r, evUnop FS op (evUnop FS op v) = some r → v = some r) {a : Term} {T T' : Ty} :
    Refines FS (.mk (.Unop op (.mk (.Unop op a) T)) T') a := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · have ⟨_, hT, w1⟩ := (WT_funop hop).1 w
    have ⟨_, hT', w2⟩ := (WT_funop hop).1 w1
    exact ⟨w2, by simp_all⟩
  · rw [eval_unop w, eval_unop (WT_unop.1 w).2] at e; exact hinv _ _ e

/-- `fp.eq` against a float literal, given how the general case is decided. -/
theorem Refines.feq_lit {FS : FloatSem} {O : Ops} (hO : O.Sound FS) {f : Float} {T : Ty}
    {v2 E : Term} (hE : Refines FS (sem_eq.spec (.mk (.Float f) T) v2) E) :
    Refines FS (float_eq.spec (.mk (.Float f) T) v2)
      (if f_is_nan f then v_false
       else if f_is_zero f then O.float_is_floatclass .Zero v2 else E) := by
  have ev1 : ∀ ρ v, eval FS ρ (float_eq.spec (.mk (.Float f) T) v2) = some v →
      ∃ y, eval FS ρ v2 = some (.float f.prec y) ∧ v = .bool (f.val.eq y) := by
    intro ρ v e
    have w := eval_WT e
    have ⟨_, w1, _⟩ := WT_binop.1 w
    rw [float_eq.spec, eval_binop w, eval_float w1] at e
    simp only [evBinop, fBin_eq_some, Float.sem] at e
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
      refine Refines.trans ?_ (hO.float_is_floatclass .Zero v2)
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
        simp [Float.sem, FBits.eq_of_ne_left y hn hz]

end

/-! ## Tactics -/

/-- Proves the alternatives on literals of the float operations, by the
oracle. -/
macro "kanon_float" : tactic => `(tactic| (
  intro FS O hO
  intros
  first
    | exact Refines.float_bin_lits hO (by simp)
    | exact Refines.funop_bits (by simp) (fun _ _ => rfl)
    | exact Refines.funop_lit (by simp) (hO.orc.sqrt _)
    | exact Refines.funop_lit (by simp) (hO.orc.round _ _)
    | exact Refines.test_of_unop (fun w => ((WT_ftest (by simp)).1 w).2.1)
        (by simp [evUnop, Float.sem, f_is_class, f_is_negative, f_is_positive])
    | exact Refines.fcmp_lits (by simp) fun hp => by
        simp [evBinop, fBin, Float.sem, f_eq, f_lt, f_le, Float.cmp, hp]))

/-- Proves the alternative on a pointer literal of `ptr_loc` (resp. `ptr_ofs`),
whose spec is `spec`. -/
macro "kanon_ptr " spec:ident : tactic => `(tactic| (
  intro FS O hO l o T
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨n, hn, hT, hl, ho, wl, wo⟩ := WT_ptr.1 (WT_unop.1 w).2
    subst hT
    simp [$spec:ident, hl, ho, wl, wo, size_of_ty]
  · rw [$spec:ident, eval_unop w] at e
    cases hp : eval FS ρ (Term.mk (Kind.Ptr l o) T) with
    | none => simp [hp] at e
    | some pv =>
      obtain ⟨n, x, y, h1, h2, hv⟩ := (eval_ptr_eq_some (WT_unop.1 w).2).1 hp
      subst hv
      rw [hp] at e; simp [evUnop] at e; subst e; first | exact h1 | exact h2))

attribute [kanon_tactic "kanon_ptr ptr_loc.spec"] ptr_loc.spec
attribute [kanon_tactic "kanon_ptr ptr_ofs.spec"] ptr_ofs.spec

attribute [kanon_tactic "kanon_float"] float_is_floatclass.spec float_is_negative.spec
  float_is_positive.spec float_cast.spec float_eq.spec float_lt.spec float_leq.spec
  float_add.spec float_sub.spec float_div.spec float_mul.spec float_rem.spec float_abs.spec
  float_neg.spec float_fma.spec float_fmod_of_rem.spec float_fmod.spec float_min.spec
  float_max.spec float_sqrt.spec float_round.spec

end Kanon.Lib
