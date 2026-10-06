import BitvecMod.Lib.Tactic

/-!
# Resizing

The arms of `Bitvec.extract`, `Bitvec.extend_` and `Bitvec.concat`, over the
interface: the counterpart of the bit-vector part of the language's
`Kanon/Lib/Resize.lean`. Their tactic `bv_rs` is `bv_rule` with:

- the widths, bounds and amounts that `omega` proves nonnegative made natural
  numbers (`bv_rs_nat`), and the widths they determine substituted, so that
  the bit-vectors of the values have the widths of their sorts;
- the sort hypotheses kept when rewriting the sorts of the terms
  (`bv_rs_rw_tys`), for the matches on the sorts of the operands of the
  resizing nodes (`Sem.den_BvExtract`, …);
- the resizing of literals as that of their values (`rs_ofInt_lit_sext`, …),
  and the guards on literals (`Bitvec.lsb`, `Bitvec.is_pow2`) as functions on
  integers (`rs_lsb`, `rs_is_pow2`);
- equalities of bit-vectors proved bit by bit (`bv_rs_bits`), or by the lemmas
  on extractions of sums and products (`rs_extractLsb'_add_lsb`, …);
- the subsort hypotheses that the lifting leaves (`rs_nonzero_extract_pow2`).
-/

namespace BitvecMod

open Classical Kanon

set_option linter.unusedSectionVars false

namespace Lib

open Prim

/-! ## Literals -/

theorem rs_emod_two_pow_nonneg (z : Int) (k : Nat) : 0 ≤ z % 2 ^ k :=
  Int.emod_nonneg _ (Int.ne_of_gt (Int.pow_pos (by decide)))

theorem rs_emod_two_pow_lt (z : Int) (k : Nat) : z % 2 ^ k < 2 ^ k :=
  Int.emod_lt_of_pos _ (Int.pow_pos (by decide))

theorem rs_ofInt_emod {n : Nat} {k : Int} (hk : k = n) (z : Int) :
    BitVec.ofInt n (z % 2 ^ k.toNat) = BitVec.ofInt n z := by
  subst hk
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofInt]

theorem rs_ofInt_emod_nat {n k : Nat} (hk : k = n) (z : Int) :
    BitVec.ofInt n (z % 2 ^ k) = BitVec.ofInt n z := by
  subst hk
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofInt]

theorem rs_sext_of {n : Nat} (hn : 0 < n) (z : Int) :
    sext_of (n : Int) z = (BitVec.ofInt n z).toInt := by
  have h2 : ((2 : Int) ^ n + 1) / 2 = 2 ^ (n - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Int.pow_succ]; omega
  have h3 : (2 : Int) ^ n = 2 * 2 ^ (n - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Int.pow_succ]; omega
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  simp only [sext_of, signed_extract, zasr, Int.toNat_zero, Int.pow_zero, Int.ediv_one,
    Int.toNat_natCast, BitVec.toInt_ofInt, Int.bmod, e, h2]
  split <;> split <;> omega

theorem rs_ofInt_lit_sext {n m : Nat} (hn : 0 < n) {k : Int} (hm : (n : Int) + k = m) (a : Int) :
    BitVec.ofInt m (lit_sext k n a) = (BitVec.ofInt n a).signExtend m := by
  rw [lit_sext, ofInt_masked hm, rs_sext_of hn]
  rfl

theorem rs_ofInt_lit_zext {n m : Nat} {a : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) :
    BitVec.ofInt m (lit_zext a) = (BitVec.ofInt n a).setWidth m := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  have hp : p < 2 ^ n := by exact_mod_cast ha1
  apply BitVec.eq_of_toNat_eq
  have hx : (BitVec.ofInt n (p : Int)).toNat = p := by
    rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
  rw [lit_zext, BitVec.toNat_setWidth, hx, BitVec.toNat_ofInt, ← Int.natCast_emod,
    Int.toNat_natCast]

/-- The existentials of the typing of the resizing nodes, at known widths. -/
theorem rs_exists_pos_eq {a : Int} {p : Int → Prop} :
    (∃ n, 0 < n ∧ a = n ∧ p n) ↔ 0 < a ∧ p a :=
  ⟨fun ⟨_, h1, h2, h3⟩ => by subst h2; exact ⟨h1, h3⟩,
    fun ⟨h1, h2⟩ => ⟨_, h1, rfl, h2⟩⟩

theorem rs_exists_pos_eq₂ {a b : Int} {p : Int → Int → Prop} :
    (∃ n, 0 < n ∧ ∃ m, 0 < m ∧ a = n ∧ b = m ∧ p n m) ↔ 0 < a ∧ 0 < b ∧ p a b :=
  ⟨fun ⟨_, h1, _, h2, h3, h4, h5⟩ => by subst h3 h4; exact ⟨h1, h2, h5⟩,
    fun ⟨h1, h2, h3⟩ => ⟨_, h1, _, h2, rfl, rfl, h3⟩⟩

theorem rs_lit_concat_nat (m p q : Nat) :
    Prim.lit_concat (m : Int) (p : Int) (q : Int) = ((p <<< m ||| q : Nat) : Int) := by
  simp only [Prim.lit_concat, Prim.z_lsl, Prim.zlor, Int.toNat_natCast, Nat.shiftLeft_eq]
  rfl

theorem rs_concat_lt {n m p q : Nat} (hp : (p : Int) < 2 ^ n) (hq : (q : Int) < 2 ^ m) :
    ((p <<< m ||| q : Nat) : Int) < 2 ^ (n + m) := by
  have hp' : p < 2 ^ n := by exact_mod_cast hp
  have hq' : q < 2 ^ m := by exact_mod_cast hq
  have hlt := BitVec.toNat_shiftLeft_or_toNat_lt_two_pow_add (BitVec.ofNat n p) (BitVec.ofNat m q)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp', Nat.mod_eq_of_lt hq'] at hlt
  exact_mod_cast hlt

theorem rs_ofInt_append {n m p q : Nat} (hp : (p : Int) < 2 ^ n) (hq : (q : Int) < 2 ^ m) :
    BitVec.ofInt n (p : Int) ++ BitVec.ofInt m (q : Int) =
      BitVec.ofInt (n + m) ((p <<< m ||| q : Nat) : Int) := by
  have hp' : p < 2 ^ n := by exact_mod_cast hp
  have hq' : q < 2 ^ m := by exact_mod_cast hq
  have hx : (BitVec.ofInt n (p : Int)).toNat = p := by
    rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp']
  have hy : (BitVec.ofInt m (q : Int)).toNat = q := by
    rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq']
  have hlt := rs_concat_lt hp hq
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, hx, hy, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by exact_mod_cast hlt)]

theorem rs_zasr_nat (p f : Nat) : Prim.zasr (p : Int) (f : Int) = ((p >>> f : Nat) : Int) := by
  simp only [Prim.zasr, Int.toNat_natCast, Nat.shiftRight_eq_div_pow]; norm_cast
theorem rs_toNat_ofInt_nat {w p : Nat} (hp : (p : Int) < 2 ^ w) :
    (BitVec.ofInt w (p : Int)).toNat = p := by
  have : p < 2 ^ w := by exact_mod_cast hp
  rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt this]
theorem rs_extractLsb'_ofInt {w f n p : Nat} (hp : (p : Int) < 2 ^ w) :
    (BitVec.ofInt w (p : Int)).extractLsb' f n = BitVec.ofInt n ((p >>> f : Nat) : Int) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, rs_toNat_ofInt_nat hp, BitVec.ofInt_natCast, BitVec.toNat_ofNat]

theorem rs_two_pow_pos (k : Nat) : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)

theorem rs_ofInt_zero (n : Nat) : BitVec.ofInt n 0 = 0#n := by
  apply BitVec.eq_of_toNat_eq; simp

theorem rs_toNat_natCast_add (a b : Nat) : ((a : Int) + (b : Int)).toNat = a + b := by
  omega


/-! ## Lowest set bits and powers of two -/

theorem rs_popcountNat_eq_zero : ∀ {m : Nat}, popcountNat m = 0 → m = 0
  | 0, _ => rfl
  | k + 1, h => by
      rw [popcountNat] at h
      have : (k + 1) / 2 < k + 1 := by omega
      have := rs_popcountNat_eq_zero (m := (k + 1) / 2) (by omega)
      omega

theorem rs_popcountNat_eq_one : ∀ {m : Nat}, popcountNat m = 1 → ∃ j, m = 2 ^ j
  | 0, h => by simp [popcountNat] at h
  | k + 1, h => by
      rw [popcountNat] at h
      have : (k + 1) / 2 < k + 1 := by omega
      by_cases hm : (k + 1) % 2 = 1
      · have := rs_popcountNat_eq_zero (m := (k + 1) / 2) (by omega)
        exact ⟨0, by omega⟩
      · obtain ⟨j, hj⟩ := rs_popcountNat_eq_one (m := (k + 1) / 2) (by omega)
        exact ⟨j + 1, by rw [Nat.pow_succ]; omega⟩

theorem rs_lowbit_spec : ∀ m : Nat, 0 < m →
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
      obtain ⟨t, ht, hd⟩ := rs_lowbit_spec (m / 2) (by omega)
      refine ⟨t + 1, Nat.eq_of_testBit_eq (fun i => ?_), ?_⟩
      · rw [Nat.pow_add 2 t 1, ← ht, Nat.testBit_mul_two_pow, Nat.testBit_bitwise rfl]
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
theorem rs_lsb_dvd {p : Nat} {j : Int} (hj0 : 0 ≤ j)
    (hj : j < if (p : Int) = 0 then 128 else Prim.log2 (Prim.z_land (p : Int) (-(p : Int)))) :
    2 ^ (j.toNat + 1) ∣ p := by
  rcases p with _ | k
  · exact Nat.dvd_zero _
  obtain ⟨t, ht, hd⟩ := rs_lowbit_spec (k + 1) (by omega)
  have : Prim.log2 (Prim.z_land ((k + 1 : Nat) : Int) (-((k + 1 : Nat) : Int))) = t := by
    show Prim.log2 (Prim.z_land (Int.ofNat (k + 1)) (Int.negSucc k)) = t
    simp only [Nat.add_sub_cancel] at ht
    simp only [Prim.z_land, Prim.log2, ht]
    exact congrArg Nat.cast (Nat.log2_two_pow (n := t))
  have hne : ((k + 1 : Nat) : Int) ≠ 0 := by omega
  simp only [hne, ↓reduceIte, this] at hj
  exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hd

theorem rs_getLsbD_add_of_dvd {w : Nat} (a b : BitVec w) {q : Nat} (h : 2 ^ q ∣ a.toNat) {p : Nat}
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

theorem rs_zasr_zero (z : Int) : Prim.zasr z 0 = z := by simp [Prim.zasr]

theorem rs_log2_nat (p : Nat) : Prim.log2 (p : Int) = (Nat.log2 p : Int) := by
  simp [Prim.log2]

/-- The lowest set bit of a literal (`Bitvec.lsb`), on integers. -/
def rs_lsb (z : Int) : Int := if z = 0 then 128 else Prim.log2 (Prim.z_land z (-z))

/-- Whether a literal is a power of two (`Bitvec.is_pow2`), on integers. -/
def rs_is_pow2 (z : Int) : Bool := decide (z > 0) && decide (Prim.popcount z = 1)

/-- Adding a literal whose lowest set bit is above the extracted bits. -/
theorem rs_extractLsb'_add_lsb {w i n p : Nat} (x : BitVec w) (h1 : (p : Int) < 2 ^ w)
    (hj : (i : Int) + n - 1 < rs_lsb (p : Int)) :
    (BitVec.ofInt w (p : Int) + x).extractLsb' i n = x.extractLsb' i n := by
  rcases n with _ | n
  · exact Subsingleton.elim _ _
  have hp : p < 2 ^ w := by exact_mod_cast h1
  have hd := rs_lsb_dvd (j := (i : Int) + (n + 1 : Nat) - 1) (by omega) hj
  ext t ht
  simp only [BitVec.getElem_extractLsb']
  rw [rs_getLsbD_add_of_dvd _ _ (q := ((i : Int) + (n + 1 : Nat) - 1).toNat + 1)
    (by rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]; exact hd) (by omega)]

theorem rs_extractLsb'_add_lsb' {w i n p : Nat} (x : BitVec w) (h1 : (p : Int) < 2 ^ w)
    (hj : (i : Int) + n - 1 < rs_lsb (p : Int)) :
    (x + BitVec.ofInt w (p : Int)).extractLsb' i n = x.extractLsb' i n := by
  rw [BitVec.add_comm]; exact rs_extractLsb'_add_lsb x h1 hj

theorem rs_pow2 {p : Nat} (h : rs_is_pow2 (p : Int) = true) : p = 2 ^ Nat.log2 p := by
  simp only [rs_is_pow2, Bool.and_eq_true, Prim.popcount, Int.toNat_natCast] at h
  have h2 : popcountNat p = 1 := by exact_mod_cast of_decide_eq_true h.2
  obtain ⟨j, hj⟩ := rs_popcountNat_eq_one h2
  rw [hj, Nat.log2_two_pow]

/-- Multiplying by a power of two above the extracted bits. -/
theorem rs_extractLsb'_mul_pow2 {w i n p : Nat} (x : BitVec w) (hp : rs_is_pow2 (p : Int) = true)
    (hk : (i : Int) + n ≤ Nat.log2 p) :
    (BitVec.ofInt w (p : Int) * x).extractLsb' i n = 0#n := by
  have e := rs_pow2 hp
  have : BitVec.ofInt w (p : Int) = BitVec.twoPow w (Nat.log2 p) := by
    rw [← BitVec.toNat_inj, BitVec.toNat_twoPow, BitVec.ofInt_natCast, BitVec.toNat_ofNat, ← e]
  rw [this, BitVec.twoPow_mul_eq_shiftLeft]
  ext t ht
  simp; omega

theorem rs_extractLsb'_mul_pow2' {w i n p : Nat} (x : BitVec w) (hp : rs_is_pow2 (p : Int) = true)
    (hk : (i : Int) + n ≤ Nat.log2 p) :
    (x * BitVec.ofInt w (p : Int)).extractLsb' i n = 0#n := by
  rw [BitVec.mul_comm]; exact rs_extractLsb'_mul_pow2 x hp hk

/-- The remainder by a power of two below the extracted bits. -/
theorem rs_extractLsb'_umod_pow2 {w n p : Nat} (x : BitVec w) (hp : rs_is_pow2 (p : Int) = true)
    (h1 : (p : Int) < 2 ^ w) (hk : Nat.log2 p < n) :
    (x.extractLsb' 0 n).umod (BitVec.ofInt n (p : Int)) =
      (x.umod (BitVec.ofInt w (p : Int))).extractLsb' 0 n := by
  have e := rs_pow2 hp
  have hkn : p < 2 ^ n := by rw [e]; exact Nat.pow_lt_pow_right (by decide) hk
  have hkw : p < 2 ^ w := by exact_mod_cast h1
  show x.extractLsb' 0 n % BitVec.ofInt n (p : Int) = (x % BitVec.ofInt w (p : Int)).extractLsb' 0 n
  rw [← BitVec.toNat_inj]
  simp only [BitVec.toNat_umod, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.ofInt_natCast,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hkw, Nat.mod_eq_of_lt hkn]
  rw [Nat.mod_mod_of_dvd _ (by rw [e]; exact Nat.pow_dvd_pow 2 (by omega))]
  have hp0 : 0 < p := by rw [e]; exact Nat.two_pow_pos _
  exact (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hp0) hkn)).symm

/-! ## The guards and subsorts of the interface -/

section
variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
  {LBool : KanonBool.Syntax B} {LCore : CoreMod.Syntax B} {L : Syntax B LBool LCore}
  [KanonBool.Sem LBool] [CoreMod.Sem LCore] [Sem L]

theorem rs_bitvec_lsb_eq (z : Int) : L.bitvec_lsb z = rs_lsb z := by
  simp [Syntax.bitvec_lsb_eq, Sem.log2_eq, Sem.z_land_eq, rs_lsb]

theorem rs_bitvec_is_pow2_eq (z : Int) : L.bitvec_is_pow2 z = rs_is_pow2 z := by
  simp [Syntax.bitvec_is_pow2_eq, Sem.popcount_eq, rs_is_pow2]

/-- The divisor of `Bitvec.extract.r_urem`, the low bits of a power of two
whose exponent is below them, is not zero. -/
theorem rs_nonzero_extract_pow2 {to z : Int} {t : S.Ty} (hp : L.bitvec_is_pow2 z = true)
    (hl : L.bitvec_log2 z < to) :
    L.Nonzero (L.bitvec_mk_bv (to - 0 + 1) (L.bitvec_lit_extract 0 to t z)) := by
  rw [rs_bitvec_is_pow2_eq] at hp
  rw [Sem.log2_eq] at hl
  have hz : 0 < z := by
    simp only [rs_is_pow2, Bool.and_eq_true, decide_eq_true_eq] at hp; exact hp.1
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hz)
  have e := rs_pow2 hp
  rw [rs_log2_nat] at hl
  rw [Sem.mk_bv_eq, Sem.mk_masked_eq, Sem.lit_extract_eq]
  apply Sem.nonzero_BitVec
  intro m hm
  rw [Sem.size_of_ty_TBitVector] at hm
  have hpm : p < 2 ^ m := by
    rw [e]; exact Nat.pow_lt_pow_right (by decide) (by omega)
  have hpm' : ((p : Int) : Int) < 2 ^ m := by exact_mod_cast hpm
  rw [Prim.lit_extract, rs_zasr_zero, rs_ofInt_emod (by omega), ofInt_masked (by omega)]
  intro h0
  have := congrArg BitVec.toNat h0
  rw [rs_toNat_ofInt_nat hpm'] at this
  simp at this
  omega

end

/-! ## Meta-level tactics -/

open Lean Meta Elab Tactic in
/-- Replaces the integer variables that `omega` proves nonnegative (the widths,
the bounds of the extractions, the amounts of the extensions and shifts, and
the literals) by natural numbers. -/
partial def rsNatVars : TacticM Unit := do
  let g ← getMainGoal
  let decls ← g.withContext do return (← getLCtx).decls.toList.filterMap id
  for d in decls do
    if d.isImplementationDetail then continue
    let isInt ← g.withContext do isDefEq d.type (mkConst ``Int)
    unless isInt && d.isLet == false do continue
    let le ← g.withContext do mkAppM ``LE.le #[toExpr (0 : Int), d.toExpr]
    let pf ← g.withContext do mkFreshExprMVar le
    let ok ← try
        pure (← Tactic.run pf.mvarId! (evalTactic (← `(tactic| omega)))).isEmpty
      catch _ => pure false
    unless ok do continue
    let r ← g.withContext do
      let pf ← mkAppM ``Int.eq_ofNat_of_zero_le #[← instantiateMVars pf]
      let (h, g) ← (← g.assert `hw (← inferType pf) pf).intro1P
      let [sg] := (← g.cases h).toList | return none
      let heq := sg.fields[1]!.fvarId!
      let some sg' ← observing? (subst sg.mvarId heq) | return none
      return some sg'
    let some g' := r | continue
    replaceMainGoal [g']
    return ← rsNatVars
  return

open Lean Elab Tactic in
/-- `rsNatVars` on the main goal. -/
elab "bv_rs_nat" : tactic => rsNatVars

open Lean Meta Elab Tactic in
/-- `bv_rw_tys`, keeping the hypotheses `S.ty x = e` themselves (which
`simp only [h] at *` rewrites to `True`): rewrites, by all of them at once, the
goal and the other hypotheses. -/
elab "bv_rs_rw_tys" : tactic => withMainContext do
  -- two sorts of the same term: rewrite the later hypothesis by the first
  let mut seen : Array (Expr × FVarId) := #[]
  for h in ← tyHyps (← getMainGoal) do
    let g ← getMainGoal
    let (t?, r) ← g.withContext do
      let some d := (← getLCtx).find? h | return (none, none)
      let some (_, a, b) := (← instantiateMVars d.type).eq? | return (none, none)
      let t := if a.isAppOfArity ``Kanon.Sem.ty 2 then a else b
      match ← seen.findM? (fun (t', _) => isDefEq t t') with
      | none => return (some t, none)
      | some (_, h0) =>
        let some d0 := (← getLCtx).find? h0 | return (none, none)
        let some (_, a0, _) := (← instantiateMVars d0.type).eq? | return (none, none)
        let thms ← ({} : SimpTheorems).add (.fvar h0) #[] d0.toExpr
          (inv := !a0.isAppOfArity ``Kanon.Sem.ty 2)
        let ctx ← Simp.mkContext {} (simpTheorems := #[thms])
          (congrTheorems := ← getSimpCongrTheorems)
        try
          let r ← simpGoal g ctx (fvarIdsToSimp := #[h]) (simplifyTarget := false)
          return (none, some r.1)
        catch _ => return (none, none)
    if let some t := t? then seen := seen.push (t, h)
    match r with
    | some none => replaceMainGoal []; return
    | some (some (_, g')) => replaceMainGoal [g']
    | none => pure ()
  let g ← getMainGoal
  let hs ← tyHyps g
  if hs.isEmpty then return
  let r ← g.withContext do
    let mut thms : SimpTheorems := {}
    -- the equations between sorts of terms, kept acyclic (`S.ty v → S.ty u`)
    let mut edges : Array (Expr × Expr) := #[]
    for h in hs do
      let some d := (← getLCtx).find? h | continue
      let some (_, a, b) := (← instantiateMVars d.type).eq? | continue
      if a.isAppOfArity ``Kanon.Sem.ty 2 && b.isAppOfArity ``Kanon.Sem.ty 2 then
        let (v, u) := (a.appArg!, b.appArg!)
        let mut cur := u
        let mut cyc := cur == v
        for _ in [0:edges.size] do
          match edges.find? (·.1 == cur) with
          | some (_, nxt) => cur := nxt; if cur == v then cyc := true
          | none => break
        if cyc then continue
        edges := edges.push (v, u)
      thms ← thms.add (.fvar h) #[] d.toExpr (inv := !a.isAppOfArity ``Kanon.Sem.ty 2)
    let ctx ← Simp.mkContext {} (simpTheorems := #[thms])
      (congrTheorems := ← getSimpCongrTheorems)
    let mut others := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail || hs.contains d.fvarId then continue
      if ← isProp d.type then others := others.push d.fvarId
    try return some (← simpGoal g ctx (fvarIdsToSimp := others)).1
    catch _ => return none
  match r with
  | none => pure ()
  | some none => replaceMainGoal []
  | some (some (_, g')) => replaceMainGoal [g']

open Lean Meta Elab Tactic in
/-- Replaces the equations between the sorts of two terms (`S.ty v = S.ty u`)
by the sort of `v` when that of `u` is known (`S.ty u = T`, `T` not a sort of a
term), so that `simp_all` does not loop on them. -/
elab "bv_rs_ty_chain" : tactic => withMainContext do
  for _ in [0:4] do
    let g ← getMainGoal
    let r ← g.withContext do
      let lctx ← getLCtx
      let isTy (e : Expr) := e.isAppOfArity ``Kanon.Sem.ty 2
      -- the known sorts, `S.ty u = T`
      let mut known : Array (Expr × Expr) := #[]
      for d in lctx do
        if d.isImplementationDetail then continue
        let some (_, a, b) := (← instantiateMVars d.type).eq? | continue
        if isTy a && !isTy b then known := known.push (a.appArg!, d.toExpr)
        else if isTy b && !isTy a then known := known.push (b.appArg!, ← mkEqSymm d.toExpr)
      for d in lctx do
        if d.isImplementationDetail then continue
        let some (_, a, b) := (← instantiateMVars d.type).eq? | continue
        unless isTy a && isTy b do continue
        for (lhs, rhs, pf) in [(a, b, pure d.toExpr), (b, a, mkEqSymm d.toExpr)] do
          if let some (_, hu) := known.find? (·.1 == rhs.appArg!) then
            unless known.any (·.1 == lhs.appArg!) do
              let pf ← mkEqTrans (← pf) hu
              let (_, g') ← (← g.assert `hty (← inferType pf) pf).intro1P
              return some (← g'.clear d.fvarId)
          else if known.any (·.1 == lhs.appArg!) then
            -- both known: the equation is redundant
            if known.any (·.1 == rhs.appArg!) then return some (← g.clear d.fvarId)
      return none
    match r with
    | some g' => replaceMainGoal [g']
    | none => return

open Lean Meta Elab Tactic in
/-- Clears the equations on the sorts of terms (once the values are unfolded,
on which `simp_all` may loop). -/
elab "bv_rs_clear_tys" : tactic => withMainContext do
  let mut g ← getMainGoal
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let some (_, a, b) := (← instantiateMVars d.type).eq? | continue
    unless a.isAppOfArity ``Kanon.Sem.ty 2 || b.isAppOfArity ``Kanon.Sem.ty 2 do continue
    try g ← g.clear d.fvarId catch _ => pure ()
  replaceMainGoal [g]

open Lean Meta Elab Tactic in
/-- Case splits on the first proposition `p` of a `decide p` or an `if p` of
the goal. -/
elab "bv_rs_split_decide" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let some e := t.find? (fun e => !e.hasLooseBVars &&
      (e.isAppOfArity ``Decidable.decide 2 || e.isAppOfArity ``ite 5 ||
       e.isAppOfArity ``dite 5))
    | throwError "bv_rs_split_decide: no decide"
  let p ← Term.exprToSyntax
    (if e.isAppOfArity ``Decidable.decide 2 then e.getArg! 0 else e.getArg! 1)
  evalTactic (← `(tactic| by_cases hp : $p <;> simp only [hp, decide_true, decide_false,
    ↓reduceIte, ↓reduceDIte, Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and,
    Bool.and_true, Bool.and_false, Bool.true_or, Bool.false_or, Bool.or_true, Bool.or_false]
    at ⊢))

end Lib

open Lib

/-- The equations between natural numbers cast to integers, as equations of
natural numbers (to substitute the widths they determine). -/
macro "bv_rs_nat_eqs" : tactic => `(tactic| (
  (try simp only [rs_toNat_natCast_add, Int.toNat_natCast, ← Int.natCast_add, Int.ofNat_inj,
    Int.sub_zero, Int.add_zero, Int.sub_add_cancel] at *)
  (try subst_vars)))


/-- Proves an equality of bit-vectors bit by bit, the indices being linear. -/
macro "bv_rs_bits" : tactic => `(tactic| (
  ext i hi
  simp [BitVec.getElem_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getElem_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, BitVec.getElem_signExtend,
    BitVec.getElem_append, BitVec.msb_eq_getLsbD_last]
  all_goals (try intros)
  all_goals (repeat' bv_rs_split_decide)
  all_goals first
    | rfl
    | (exfalso; omega)
    | (simp_all; done)
    | (congr 1; omega)
    | (have := BitVec.lt_of_getLsbD ‹_›; omega)
    | (apply BitVec.getLsbD_of_ge; omega)
    | (exact (BitVec.getLsbD_of_ge _ _ (by omega)).symm)
    | (simp_all; omega)))

/-- `bv_facts`, with `bv_rs_rw_tys`. -/
macro "bv_rs_facts" : tactic => `(tactic| (
  (try simp only [bv_wt, bv_lits, true_and, and_true] at *)
  (try kanon_split)
  (try subst_vars)
  (try bv_rs_rw_tys)
  (try simp only [bv_wt, bv_lits, true_and, and_true] at *)
  (try kanon_split)
  (try subst_vars)
  (try bv_rs_ty_chain)))

set_option hygiene false in
/-- `bv_sem_core`, with the widths made natural numbers and the sorts of the
operands rewritten after the values of the nodes are unfolded; the conditionals
of the hypothesis `e` are split. -/
macro "bv_rs_sem_core" : tactic => `(tactic| (
  first
    | intro n w ht ρ x e
    | intro w ρ x e
  bv_rs_facts
  (try bv_rs_nat)
  bv_rs_nat_eqs
  (try simp only [bv_den, bv_lits] at e ⊢)
  (try bv_rs_rw_tys)
  (try simp only [bv_lits, BitvecMod.Lib.TBitVector_inj_iff, Int.ofNat_inj] at *)
  (try subst_vars)
  bv_lit_ops
  run_tac Kanon.Proof.caseAllAtoms (some #[``BitvecMod.Lib.den_cases, ``BitvecMod.Lib.denB_cases])
  all_goals (try bv_bool_vars)
  all_goals (try simp only [Option.map_some, Option.map_none, Option.some.injEq,
    reduceCtorEq, BitvecMod.ckOp_some, BitvecMod.binOp_some, BitvecMod.negOp_some] at e ⊢)
  all_goals (try subst e)
  all_goals (try (split at e <;> simp only [Option.map_some, Option.map_none, Option.some.injEq,
    reduceCtorEq] at e <;> subst e))))

/-- The guards on literals as functions on integers, then the operations on
literals (in range) as those on bit-vectors, and the resizing of literals. -/
macro "bv_rs_lits" : tactic => `(tactic| (
  (try simp only [rs_bitvec_lsb_eq, rs_bitvec_is_pow2_eq, rs_log2_nat, Int.toNat_zero] at *)
  (try simp (disch := first | assumption | omega) only [rs_ofInt_emod, rs_ofInt_emod_nat,
    rs_ofInt_lit_sext, rs_ofInt_lit_zext, rs_lit_concat_nat, rs_ofInt_append, Prim.lit_extract,
    rs_zasr_nat, rs_zasr_zero, ofInt_masked, rs_toNat_ofInt_nat, rs_extractLsb'_ofInt,
    BitVec.shiftLeft_eq',
    BitVec.ushiftRight_eq', rs_ofInt_zero, BitVec.extractLsb'_add, BitVec.extractLsb'_mul,
    rs_extractLsb'_add_lsb, rs_extractLsb'_add_lsb', rs_extractLsb'_mul_pow2,
    rs_extractLsb'_mul_pow2', rs_extractLsb'_umod_pow2, ↓reduceIte] at *)))

/-- `bv_wt`, with the widths made natural numbers. -/
macro "bv_rs_wt" : tactic => `(tactic| (
  intro w
  bv_rs_facts
  (try bv_rs_nat)
  bv_rs_nat_eqs
  (try simp_all [bv_range, Prim.lit_extract, rs_two_pow_pos, rs_emod_two_pow_nonneg,
    rs_emod_two_pow_lt, rs_lit_concat_nat, rs_concat_lt, rs_exists_pos_eq, rs_exists_pos_eq₂])
  all_goals first | done | omega | grind))

/-- The value half: `bv_rs_sem_core`, the literals, then `simp_all`, `omega` or
bit by bit. -/
macro "bv_rs_sem" : tactic => `(tactic| (
  bv_rs_sem_core
  all_goals bv_rs_lits
  all_goals first
    | done
    | (simp_all; done)
    | omega
    | ((try simp only [↓reduceIte] at *); bv_rs_bits; done)
    | skip))

/-- `kanon_rule_lift` after the introductions. -/
macro "bv_rs_rule_lift_core" : tactic => `(tactic| (
  (try kanon_guards)
  (try kanon_split)
  (try subst_vars)
  (try simp only [kanon_spec, kanon_body])
  (repeat' split)
  all_goals (try kanon_lift_body)
  all_goals (try simp only [kanon_spec, kanon_body])
  all_goals (try first
    | kanon_refl
    | (kanon_comm; done)
    | kanon_rule_close
    | kanon_close_lemmas)))

/-- `kanon_rule_lift`, in two steps (`bv_cmp` unfolds a helper in between). -/
macro "bv_rs_rule_lift" : tactic => `(tactic| (
  intro _
  intros
  bv_rs_rule_lift_core))


/-- Proves an arm of `Bitvec.extract`, `Bitvec.extend_` or `Bitvec.concat`. -/
macro "bv_rs" : tactic => `(tactic| (
  bv_rs_rule_lift
  bv_rule_apply
  all_goals first
    | exact rs_nonzero_extract_pow2 ‹_› ‹_›
    | bv_rs_sem
    | (bv_rs_wt; done)
    | skip))

attribute [kanon_tactic "bv_rs"] Bitvec.extract.spec Bitvec.extend_.spec Bitvec.concat.spec

end BitvecMod
