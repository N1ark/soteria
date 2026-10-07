import BitvecMod.Tactic
import BitvecMod.LitOps
import BitvecMod.Statements.Comm

/-!
# The lemmas that the arithmetic, comparison and resizing proofs share

The overflow flags of `BitVec` through integers (`sadd_ok`, …), the bound of the values of a term
by `msb_of` (`msb_bound`), and the commutativity of `Add` and `Mul` (for the swapped arms).
-/

noncomputable section

namespace BitvecMod

open Classical Kanon Prim LitOps

set_option linter.unusedSectionVars false


theorem two_pow_pos (n : Nat) : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)

theorem zasr_zero (z : Int) : zasr z 0 = z := by simp [zasr]

theorem signed_extract_zero {n : Nat} (hn : 0 < n) (z : Int) :
    signed_extract z 0 (n : Int) = (BitVec.ofInt n z).toInt := by
  have h2 : ((2 : Int) ^ n + 1) / 2 = 2 ^ (n - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Int.pow_succ]; omega
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  simp only [Prim.signed_extract, zasr_zero, Int.toNat_natCast, BitVec.toInt_ofInt, Int.bmod, e, h2]
  split <;> split <;> omega

theorem z_lsl_one (k : Int) : Prim.z_lsl 1 k = 2 ^ k.toNat := by simp [Prim.z_lsl]

theorem ofInt_emod_two_pow (n : Nat) (z : Int) :
    BitVec.ofInt n (z % 2 ^ n) = BitVec.ofInt n z := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]

theorem toNat_ofInt_of_lt {n : Nat} {k : Int} (h0 : 0 ≤ k) (h1 : k < 2 ^ n) :
    (BitVec.ofInt n k).toNat = k.toNat := by
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt h0 (by push_cast; exact h1)]

theorem smtUDiv_toNat {n : Nat} {a b : BitVec n} (hb : b.toNat ≠ 0) :
    (a.smtUDiv b).toNat = a.toNat / b.toNat := by
  simp [BitVec.smtUDiv_eq, ← BitVec.toNat_inj, hb]

theorem popcountNat_eq_zero : ∀ {m : Nat}, popcountNat m = 0 → m = 0
  | 0, _ => rfl
  | k + 1, h => by
      rw [popcountNat] at h
      have : (k + 1) / 2 < k + 1 := by omega
      have := popcountNat_eq_zero (m := (k + 1) / 2) (by omega)
      omega

theorem popcountNat_eq_one : ∀ {m : Nat}, popcountNat m = 1 → ∃ j, m = 2 ^ j
  | 0, h => by simp [popcountNat] at h
  | k + 1, h => by
      rw [popcountNat] at h
      have : (k + 1) / 2 < k + 1 := by omega
      by_cases hm : (k + 1) % 2 = 1
      · have := popcountNat_eq_zero (m := (k + 1) / 2) (by omega)
        exact ⟨0, by omega⟩
      · obtain ⟨j, hj⟩ := popcountNat_eq_one (m := (k + 1) / 2) (by omega)
        exact ⟨j + 1, by rw [Nat.pow_succ]; omega⟩

theorem ovf_comm {n : Nat} (x y : BitVec n) : (x.saddOverflow y = y.saddOverflow x) ∧
    (x.uaddOverflow y = y.uaddOverflow x) ∧ (x.smulOverflow y = y.smulOverflow x) ∧
    (x.umulOverflow y = y.umulOverflow x) := by
  simp [BitVec.saddOverflow, BitVec.uaddOverflow, BitVec.smulOverflow,
    BitVec.umulOverflow, Int.add_comm, Nat.add_comm, Int.mul_comm, Nat.mul_comm]

section
variable {w : Nat} {x y : BitVec w}

theorem sadd_ok : x.saddOverflow y = false ↔
    -2 ^ (w - 1) ≤ x.toInt + y.toInt ∧ x.toInt + y.toInt < 2 ^ (w - 1) := by
  simp [BitVec.saddOverflow]; omega

theorem ssub_ok : x.ssubOverflow y = false ↔
    -2 ^ (w - 1) ≤ x.toInt - y.toInt ∧ x.toInt - y.toInt < 2 ^ (w - 1) := by
  simp [BitVec.ssubOverflow]; omega

theorem smul_ok : x.smulOverflow y = false ↔
    -2 ^ (w - 1) ≤ x.toInt * y.toInt ∧ x.toInt * y.toInt < 2 ^ (w - 1) := by
  simp [BitVec.smulOverflow]; omega

theorem uadd_ok : x.uaddOverflow y = false ↔ x.toNat + y.toNat < 2 ^ w := by
  simp [BitVec.uaddOverflow]

theorem usub_ok : x.usubOverflow y = false ↔ y.toNat ≤ x.toNat := by
  simp [BitVec.usubOverflow]

theorem umul_ok : x.umulOverflow y = false ↔ x.toNat * y.toNat < 2 ^ w := by
  simp [BitVec.umulOverflow]

theorem toInt_add_ok (h : x.saddOverflow y = false) : (x + y).toInt = x.toInt + y.toInt :=
  BitVec.toInt_add_of_not_saddOverflow (by simp [h])

theorem toInt_sub_ok (h : x.ssubOverflow y = false) : (x - y).toInt = x.toInt - y.toInt :=
  BitVec.toInt_sub_of_not_ssubOverflow (by simp [h])

theorem toInt_mul_ok (h : x.smulOverflow y = false) : (x * y).toInt = x.toInt * y.toInt :=
  BitVec.toInt_mul_of_not_smulOverflow (by simp [h])

theorem toNat_add_ok (h : x.uaddOverflow y = false) : (x + y).toNat = x.toNat + y.toNat :=
  BitVec.toNat_add_of_not_uaddOverflow (by simp [h])

theorem toNat_sub_ok (h : x.usubOverflow y = false) : (x - y).toNat = x.toNat - y.toNat :=
  BitVec.toNat_sub_of_not_usubOverflow (by simp [h])

theorem toNat_mul_ok (h : x.umulOverflow y = false) : (x * y).toNat = x.toNat * y.toNat :=
  BitVec.toNat_mul_of_not_umulOverflow (by simp [h])

end

theorem smulOverflow_neg_swap {n : Nat} {c v : BitVec n} (hc : c ≠ BitVec.intMin n)
    (hv : v ≠ BitVec.intMin n) : (-c).smulOverflow v = c.smulOverflow (-v) := by
  simp only [BitVec.smulOverflow, BitVec.toInt_neg_of_ne_intMin hc,
    BitVec.toInt_neg_of_ne_intMin hv, Int.neg_mul, Int.mul_neg]

theorem umul_assoc_ok {n : Nat} {x y z : BitVec n} (h1 : x.umulOverflow y = false)
    (h2 : (x * y).umulOverflow z = false) : x.umulOverflow (y * z) = false := by
  have e := toNat_mul_ok h1
  rw [umul_ok] at *
  rw [e] at h2
  have : (y * z).toNat ≤ y.toNat * z.toNat := by rw [BitVec.toNat_mul]; exact Nat.mod_le _ _
  calc x.toNat * (y * z).toNat ≤ x.toNat * (y.toNat * z.toNat) := Nat.mul_le_mul_left _ this
    _ = x.toNat * y.toNat * z.toNat := (Nat.mul_assoc ..).symm
    _ < 2 ^ n := h2

theorem smul_assoc_ok {n : Nat} {x y z : BitVec n} (h1 : x.smulOverflow y = false)
    (h2 : (x * y).smulOverflow z = false) (h3 : y.smulOverflow z = false) :
    x.smulOverflow (y * z) = false := by
  rwa [← BitVec.smulOverflow_assoc (by simp [h1]) (by simp [h3])]

theorem toInt_bounds {w : Nat} (x : BitVec w) :
    -2 ^ (w - 1) ≤ x.toInt ∧ x.toInt < 2 ^ (w - 1) :=
  ⟨BitVec.le_toInt x, BitVec.toInt_lt⟩

open Lean Meta Elab Tactic in
/-- Adds the integer meaning of the non-overflow hypotheses. -/
def ovfEqs (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.eq? | continue
    unless rhs.isConstOf ``Bool.false do continue
    let lems := [(``BitVec.saddOverflow, ``toInt_add_ok), (``BitVec.ssubOverflow, ``toInt_sub_ok),
      (``BitVec.smulOverflow, ``toInt_mul_ok), (``BitVec.uaddOverflow, ``toNat_add_ok),
      (``BitVec.usubOverflow, ``toNat_sub_ok), (``BitVec.umulOverflow, ``toNat_mul_ok)]
    for (f, lem) in lems do
      if lhs.isAppOfArity f 3 then
        let pf ← mkAppM lem #[d.toExpr]
        let (_, g') ← (← g.assert `hovf (← inferType pf) pf).intro1P
        g := g'
  return g

theorem ofInt_zero' (n : Nat) : BitVec.ofInt n 0 = 0#n := by
  apply BitVec.eq_of_toNat_eq; simp

theorem exists_sigma_eq {m : Nat} {y : BitVec m} {P : (n : Nat) → BitVec n → Prop} :
    (∃ n x, (⟨m, y⟩ : (n : Nat) × BitVec n) = ⟨n, x⟩ ∧ P n x) ↔ P m y :=
  ⟨fun ⟨_, _, h, p⟩ => by cases h; exact p, fun p => ⟨_, _, rfl, p⟩⟩

theorem natCast_sub_one_toNat (n : Nat) : ((n : Int) - 1).toNat = n - 1 := by omega

theorem toNat_natCast_add (a b : Nat) : ((a : Int) + (b : Int)).toNat = a + b := by omega

section
variable {n : Nat}

theorem toInt_cond (x : BitVec n) :
    (2 * (x.toNat : Int) < 2 ^ n ∧ x.toInt = x.toNat) ∨
      (2 ^ n ≤ 2 * (x.toNat : Int) ∧ x.toInt = x.toNat - 2 ^ n) := by
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  rw [BitVec.toInt_eq_toNat_cond]
  split
  · left; exact ⟨by omega, rfl⟩
  · right; exact ⟨by omega, by rw [e]⟩

theorem toNat_lt_int (x : BitVec n) : 0 ≤ (x.toNat : Int) ∧ (x.toNat : Int) < 2 ^ n := by
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  have := x.isLt; omega

theorem two_pow_pred (n : Nat) : n = 0 ∨ ((2 : Int) ^ n = 2 * 2 ^ (n - 1) ∧ 2 ^ n = 2 * 2 ^ (n - 1)) := by
  rcases n with _ | k
  · exact .inl rfl
  · right; simp only [Nat.add_sub_cancel]; constructor
    · rw [Int.pow_succ]; omega
    · rw [Nat.pow_succ]; omega

end

/-- What a literal is, for `omega`, before it is generalized. -/
theorem lit_facts (n : Nat) (z : Int) :
    (0 ≤ z → z < 2 ^ n → ((BitVec.ofInt n z).toNat : Int) = z) ∧
      (BitVec.ofInt n z).toInt = z.bmod (2 ^ n) := by
  refine ⟨fun h0 h1 => ?_, by simp⟩
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  rw [BitVec.toNat_ofInt, e, Int.emod_eq_of_lt h0 h1, Int.toNat_of_nonneg h0]

/-! ## The bound of `msb_of` -/

/-- The bound that `msb_of` gives the values of a term. -/
def MsbOk (x : Nat) (m : Int) : Prop := (x : Int) < 2 ^ (m + 1).toNat

theorem pow_le_pow_int {a b : Nat} (h : a ≤ b) : (2 : Int) ^ a ≤ 2 ^ b := by
  have := Nat.pow_le_pow_right (by decide : 0 < 2) h
  have e1 : ((2 ^ a : Nat) : Int) = (2 : Int) ^ a := by push_cast; rfl
  have e2 : ((2 ^ b : Nat) : Int) = (2 : Int) ^ b := by push_cast; rfl
  omega

theorem msbOk_mono {x : Nat} {m m' : Int} (h : MsbOk x m) (hm : m ≤ m') : MsbOk x m' := by
  unfold MsbOk at *
  have := pow_le_pow_int (a := (m + 1).toNat) (b := (m' + 1).toNat) (by omega)
  omega

theorem msbOk_le {x y : Nat} {m : Int} (h : MsbOk y m) (hm : x ≤ y) : MsbOk x m := by
  unfold MsbOk at *; omega

theorem msbOk_log2 {x : Nat} {z : Int} (hz : 0 < z) (hx : (x : Int) ≤ z) : MsbOk x (Prim.log2 z) := by
  unfold MsbOk Prim.log2
  have := Nat.lt_log2_self (n := z.toNat)
  have e : ((z.toNat.log2 : Nat) : Int) + 1 = ((z.toNat.log2 + 1 : Nat) : Int) := by push_cast; rfl
  rw [e, Int.toNat_natCast]
  have e2 : ((2 ^ (z.toNat.log2 + 1) : Nat) : Int) = (2 : Int) ^ (z.toNat.log2 + 1) := by
    push_cast; rfl
  omega

theorem msbOk_width {n : Nat} (x : BitVec n) : MsbOk x.toNat ((n : Int) - 1) := by
  unfold MsbOk
  rw [show ((n : Int) - 1 + 1).toNat = n by omega]
  have := x.isLt
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  omega

section
variable {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [Lang S] [Typed S]

/-- The values of a term of a sort of bit-vectors are below `2 ^ (msb_of v + 1)`. -/
theorem msb_bound (ρ : S.Env) : ∀ (k : Nat) (v : S.Term), S.size v < k → ∀ (n : Nat) (x : BitVec n),
    S.WT v → S.ty v = sort (.TBitVector n) → S.ev ρ v = some (bv n x) →
    MsbOk x.toNat (Bitvec.msb_of v) := by
  intro k
  induction k with
  | zero => intro v hs; omega
  | succ k ih =>
  intro v hs n x w ht e
  rw [Bitvec.msb_of.eq_1]
  refine getD_firstSome_cons ?_ (getD_firstSome_cons ?_ (getD_firstSome_cons ?_
    (getD_firstSome_cons ?_ (getD_firstSome_cons ?_ (getD_firstSome_cons ?_
    (getD_firstSome_cons ?_ (getD_firstSome_cons ?_ (getD_firstSome_nil ?_))))))))
  · intro r hr
    split at hr
    · rename_i z hp
      split at hr
      · cases hr
        rename_i hz
        obtain ⟨t, rfl⟩ := NodeEmbed.exists_of_proj _ hp
        rw [ty_mk] at ht; subst ht
        rw [WT_mk] at w
        simp only [Node.wt, bv_wf, Node.All] at w
        obtain ⟨⟨⟨m, hm, hmt⟩, hr⟩, -⟩ := w
        rw [sort_inj_iff, Srt.TBitVector.injEq] at hmt
        have hr := hr _ (.inl rfl)
        rw [ev_mk] at e
        simp only [Node.map, Node.eval] at e
        bv_widths
        simp only [ofBV_some, Option.some.injEq, Embed.inj_eq_iff, Sigma.mk.injEq, heq_eq_eq,
          true_and] at e
        subst e
        apply msbOk_log2 (by simpa using hz)
        have := lit_facts n z
        simp at hz
        omega
      · cases hr
    · cases hr
  · intro r hr
    split at hr
    · rename_i z hp
      split at hr
      · cases hr
        rw [Bitvec.size, ht, size_of_ty_TBitVector]
        exact msbOk_width x
      · cases hr
    · cases hr
  -- BitAnd
  · intro r hr
    split at hr
    · rename_i a b hp
      cases hr
      obtain ⟨t, rfl⟩ := NodeEmbed.exists_of_proj _ hp
      have hsz := Lang.size_proj _ _ hp
      simp only [Node.All] at hsz
      rw [ty_mk] at ht; subst ht
      rw [WT_mk] at w
      simp only [Node.wt, Node.All] at w
      obtain ⟨⟨⟨m, hm, hma⟩, hb, ht⟩, wa, wb⟩ := w
      rw [hma] at ht
      simp only [Embed.inj_eq_iff, Srt.TBitVector.injEq] at ht
      subst ht
      rw [ev_mk] at e
      simp only [Node.map, Node.eval] at e
      bv_widths
      simp only [ofBV, Option.map_eq_some_iff] at e
      obtain ⟨y, hy, e⟩ := e
      simp only [Embed.inj_eq_iff, Sigma.mk.injEq, heq_eq_eq, true_and] at e
      subst e
      cases ha : asBV n (S.ev ρ a) <;> cases hb' : asBV n (S.ev ρ b) <;>
        simp only [ha, hb', binOp_none_l, binOp_none_r, binOp_some, reduceCtorEq,
          Option.some.injEq] at hy
      subst hy
      rename_i xa xb
      rw [asBV_eq_some] at ha hb'
      have ia := ih a (by omega) n xa wa hma ha
      have ib := ih b (by omega) n xb wb (hb.trans hma) hb'
      simp only [Bitvec.zmin]
      rw [BitVec.toNat_and]
      split
      · exact msbOk_le ia Nat.and_le_left
      · exact msbOk_le ib Nat.and_le_right
    · cases hr
  -- Ite
  · intro r hr
    split at hr
    · rename_i g l r' hp
      cases hr
      obtain ⟨t, rfl⟩ := NodeEmbed.exists_of_proj _ hp
      have hsz := KanonBool.Lang.size_proj _ _ hp
      simp only [KanonBool.Node.All] at hsz
      rw [KanonBool.ty_mk] at ht; subst ht
      rw [KanonBool.WT_mk] at w
      simp only [KanonBool.Node.wt, KanonBool.Node.All] at w
      obtain ⟨⟨-, hr', ht⟩, -, wl, wr⟩ := w
      rw [KanonBool.ev_mk] at e
      simp only [KanonBool.Node.map, KanonBool.Node.eval, KanonBool.pite_eq_some] at e
      simp only [Bitvec.zmax]
      rcases e with ⟨-, el⟩ | ⟨-, -, er⟩
      · have il := ih l (by omega) n x wl ht.symm el
        split
        · exact il
        · rename_i hc; simp only [decide_eq_true_eq] at hc; exact msbOk_mono il (by omega)
      · have ir := ih r' (by omega) n x wr (hr'.trans ht.symm) er
        split
        · rename_i hc; simp only [decide_eq_true_eq] at hc; exact msbOk_mono ir (by omega)
        · exact ir
    · cases hr
  -- BvExtend false
  · intro r hr
    split at hr
    · rename_i k' u hp
      cases hr
      obtain ⟨t, rfl⟩ := NodeEmbed.exists_of_proj _ hp
      have hsz := Lang.size_proj _ _ hp
      simp only [Node.All] at hsz
      rw [ty_mk] at ht; subst ht
      rw [WT_mk] at w
      simp only [Node.wt, Node.All] at w
      obtain ⟨⟨m, hm, hmu, -, -⟩, wu⟩ := w
      rw [ev_mk] at e
      simp only [Node.map, Node.eval] at e
      obtain ⟨n', xu, hu, h⟩ := withW_eq_some.1 e
      have hv := Typed.ev_sort ρ u _ _ wu hmu hu
      simp only [Srt.val] at hv
      obtain ⟨-, y, hy⟩ := hv
      rw [Embed.inj_eq_iff] at hy
      cases hy
      rw [hu, asBV_bv] at h
      simp only [Option.map_some, ofBV_some, Option.some.injEq, Embed.inj_eq_iff] at h
      have hmu' : S.ty u = sort (.TBitVector ((m.toNat : Nat) : Int)) := by
        rw [Int.toNat_of_nonneg (by omega)]; exact hmu
      have iu := ih u (by omega) _ y wu hmu' hu
      revert h
      generalize m.toNat + k'.toNat = q
      intro h
      cases h
      simp only [Bool.false_eq_true, ite_false] at *
      refine msbOk_le iu ?_
      rw [BitVec.toNat_setWidth]
      exact Nat.mod_le _ _
    · cases hr
  -- Rem false _ #k
  · intro r hr
    split at hr
    · rename_i a b hp
      split at hr
      · rename_i k hk
        split at hr
        · cases hr
          rename_i hk1
          simp only [decide_eq_true_eq] at hk1
          obtain ⟨t, rfl⟩ := NodeEmbed.exists_of_proj _ hp
          obtain ⟨t', rfl⟩ := NodeEmbed.exists_of_proj _ hk
          rw [ty_mk] at ht; subst ht
          rw [WT_mk] at w
          simp only [Node.wt, Node.All] at w
          obtain ⟨⟨⟨m, hm, hma⟩, hb, ht⟩, wa, wb⟩ := w
          rw [hma] at ht
          simp only [Embed.inj_eq_iff, Srt.TBitVector.injEq] at ht
          subst ht
          rw [ty_mk] at hb
          rw [WT_mk] at wb
          simp only [Node.wt, bv_wf, Node.All] at wb
          obtain ⟨⟨-, hr⟩, -⟩ := wb
          have hr := hr _ (.inl (hb.trans hma))
          rw [ev_mk] at e
          simp only [Node.map, Node.eval, ev_mk] at e
          subst hb
          bv_widths
          simp only [ofBV, Option.map_eq_some_iff] at e
          obtain ⟨y, hy, e⟩ := e
          simp only [Embed.inj_eq_iff, Sigma.mk.injEq, heq_eq_eq, true_and] at e
          subst e
          simp only [asBV_bv, Option.map_some] at hy
          cases ha : asBV n (S.ev ρ a) <;>
            simp only [ha, binOp_none_l, binOp_some, reduceCtorEq, Option.some.injEq,
              Bool.false_eq_true, ite_false] at hy
          subst hy
          rename_i xa
          apply msbOk_log2 (by omega)
          have := lit_facts n k
          have hlt := BitVec.toNat_umod (x := xa) (y := BitVec.ofInt n k)
          have : (xa.umod (BitVec.ofInt n k)).toNat < (BitVec.ofInt n k).toNat :=
            hlt ▸ Nat.mod_lt _ (by omega)
          omega
        · cases hr
      · cases hr
    · cases hr
  -- Mod _ #k
  · intro r hr
    split at hr
    · rename_i a b hp
      split at hr
      · rename_i k hk
        split at hr
        · cases hr
          rename_i hk1
          obtain ⟨t, rfl⟩ := NodeEmbed.exists_of_proj _ hp
          obtain ⟨t', rfl⟩ := NodeEmbed.exists_of_proj _ hk
          simp only [Bitvec.size, ty_mk, ht, size_of_ty_TBitVector, Bool.and_eq_true,
            decide_eq_true_eq, z_lsl_one] at hk1
          rw [ty_mk] at ht; subst ht
          rw [WT_mk] at w
          simp only [Node.wt, Node.All] at w
          obtain ⟨⟨⟨m, hm, hma⟩, hb, ht⟩, wa, wb⟩ := w
          rw [hma] at ht
          simp only [Embed.inj_eq_iff, Srt.TBitVector.injEq] at ht
          subst ht
          rw [ty_mk] at hb
          rw [WT_mk] at wb
          simp only [Node.wt, bv_wf, Node.All] at wb
          obtain ⟨⟨-, hr⟩, -⟩ := wb
          have hr := hr _ (.inl (hb.trans hma))
          rw [ev_mk] at e
          simp only [Node.map, Node.eval, ev_mk] at e
          subst hb
          bv_widths
          simp only [ofBV, Option.map_eq_some_iff] at e
          obtain ⟨y, hy, e⟩ := e
          simp only [Embed.inj_eq_iff, Sigma.mk.injEq, heq_eq_eq, true_and] at e
          subst e
          simp only [asBV_bv, Option.map_some] at hy
          cases ha : asBV n (S.ev ρ a) <;>
            simp only [ha, binOp_none_l, binOp_none_r, binOp_some, reduceCtorEq, Option.some.injEq,
              Bool.false_eq_true, ite_false, ite_true] at hy
          subst hy
          rename_i xa
          have hl := lit_facts n k
          have tp := two_pow_pred n
          have hc := toInt_cond (BitVec.ofInt n k)
          have hn : (n : Int).toNat = n := Int.toNat_natCast n
          rw [show ((n : Int) - 1).toNat = n - 1 by omega] at hk1
          apply msbOk_log2 (by omega)
          have hs := BitVec.toInt_smod (x := xa) (y := BitVec.ofInt n k)
          have hkv : (BitVec.ofInt n k).toInt = k := by omega
          rw [hkv] at hs
          have h0 := Int.fmod_nonneg_of_pos xa.toInt (b := k) (by omega)
          have h1 := Int.fmod_lt_of_pos xa.toInt (b := k) (by omega)
          have := toInt_cond (xa.smod (BitVec.ofInt n k))
          have := toNat_lt_int (xa.smod (BitVec.ofInt n k))
          omega
        · cases hr
      · cases hr
    · cases hr
  -- Rem true #k _
  · intro r hr
    split at hr
    · rename_i b a hp
      split at hr
      · rename_i k hk
        split at hr
        · cases hr
          rename_i hk1
          obtain ⟨t, rfl⟩ := NodeEmbed.exists_of_proj _ hp
          obtain ⟨t', rfl⟩ := NodeEmbed.exists_of_proj _ hk
          simp only [Bitvec.size, ty_mk, ht, size_of_ty_TBitVector, Bool.and_eq_true,
            decide_eq_true_eq, z_lsl_one] at hk1
          rw [ty_mk] at ht; subst ht
          rw [WT_mk] at w
          simp only [Node.wt, Node.All] at w
          obtain ⟨⟨⟨m, hm, hmb⟩, ha, ht⟩, wb, wa⟩ := w
          have hma := ha.trans hmb
          have hb := hmb.trans hma.symm
          rw [hmb] at ht
          simp only [Embed.inj_eq_iff, Srt.TBitVector.injEq] at ht
          subst ht
          rw [ty_mk] at hb
          rw [WT_mk] at wb
          simp only [Node.wt, bv_wf, Node.All] at wb
          obtain ⟨⟨-, hr⟩, -⟩ := wb
          have hr := hr _ (.inl (hb.trans hma))
          rw [ev_mk] at e
          simp only [Node.map, Node.eval, ev_mk] at e
          subst hb
          bv_widths
          simp only [ofBV, Option.map_eq_some_iff] at e
          obtain ⟨y, hy, e⟩ := e
          simp only [Embed.inj_eq_iff, Sigma.mk.injEq, heq_eq_eq, true_and] at e
          subst e
          simp only [asBV_bv, Option.map_some] at hy
          cases ha : asBV n (S.ev ρ a) <;>
            simp only [ha, binOp_none_l, binOp_none_r, binOp_some, reduceCtorEq, Option.some.injEq,
              Bool.false_eq_true, ite_false, ite_true] at hy
          subst hy
          rename_i xa
          have hl := lit_facts n k
          have tp := two_pow_pred n
          have hc := toInt_cond (BitVec.ofInt n k)
          have hn : (n : Int).toNat = n := Int.toNat_natCast n
          rw [show ((n : Int) - 1).toNat = n - 1 by omega] at hk1
          apply msbOk_log2 (by omega)
          have hs := BitVec.toInt_srem (BitVec.ofInt n k) xa
          have hkv : (BitVec.ofInt n k).toInt = k := by omega
          rw [hkv] at hs
          have h0 := Int.tmod_nonneg xa.toInt (a := k) (by omega)
          have h1 := Int.natAbs_tmod k xa.toInt
          have h2 := Nat.mod_le k.natAbs xa.toInt.natAbs
          have := toInt_cond (BitVec.srem (BitVec.ofInt n k) xa)
          have := toNat_lt_int (BitVec.srem (BitVec.ofInt n k) xa)
          omega
        · cases hr
      · cases hr
    · cases hr
  · rw [Bitvec.size, ht, size_of_ty_TBitVector]
    exact msbOk_width x




/-- `msb_bound`, at any width and for the values of the term, before its value is known. -/
theorem msb_bound_int (ρ : S.Env) {v : S.Term} {m : Int} (w : S.WT v)
    (ht : S.ty v = sort (.TBitVector m)) :
    ∀ (n : Nat) (x : BitVec n), S.ev ρ v = some (bv n x) →
      (x.toNat : Int) < 2 ^ (Bitvec.msb_of v + 1).toNat := by
  intro n x e
  have hv := Typed.ev_sort ρ v _ _ w ht e
  simp only [Srt.val] at hv
  obtain ⟨hm, y, hy⟩ := hv
  rw [Embed.inj_eq_iff] at hy
  cases hy
  have ht' : S.ty v = sort (.TBitVector ((m.toNat : Nat) : Int)) := by
    rw [Int.toNat_of_nonneg (by omega)]; exact ht
  exact msb_bound ρ _ v (Nat.lt_succ_self _) _ y w ht' e

end

/-! ## The commutativity of `Add` and `Mul`, for the swapped arms -/

/-- `ckOp` of a commutative operation whose overflow flags are symmetric. -/
theorem ckOp_comm {n : Nat} (c : CoreMod.Checked) {so uo : BitVec n → BitVec n → Bool}
    {f : BitVec n → BitVec n → BitVec n} (hs : ∀ a b, so a b = so b a) (hu : ∀ a b, uo a b = uo b a)
    (hf : ∀ a b, f a b = f b a) (x y : Option (BitVec n)) :
    ckOp c so uo f x y = ckOp c so uo f y x := by
  cases x <;> cases y <;> simp only [ckOp, hs, hu, hf]

/-- Closes a goal whose context holds `¬True`, `false = true` or `true = false` (the
branches of the conditionals on constants that the lifting of an arm splits). -/
macro "bv_vacuous" : tactic => `(tactic| first
  | exact absurd trivial ‹¬True›
  | exact absurd ‹false = true› Bool.false_ne_true
  | exact absurd ‹true = false› Bool.true_ne_false)

/-- A refinement between two nodes of the same type with the same typing and values. -/
theorem comm_refines {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [Lang S]
    {n m : Node S.Term} {t : S.Ty} (hw : S.WT (mk n t) → S.WT (mk m t))
    (he : ∀ ρ, S.ev ρ (mk n t) = S.ev ρ (mk m t)) : S.Refines (mk n t) (mk m t) :=
  Kanon.Sem.Refines.intro (fun w => ⟨hw w, by simp only [ty_mk]⟩)
    (fun ρ v _ _ e => (he ρ) ▸ e)

/-- `Add.comm`, for the swapped arms. -/
@[kanon_arm] theorem Add.comm.proof : Add.comm.Stmt := by
  intro S _ _ _ _ _ _ c a b t
  refine comm_refines (fun w => ?_) (fun ρ => ?_)
  · simp only [WT_mk, Node.wt, Node.All] at w ⊢
    obtain ⟨⟨⟨n, hn, ha⟩, hb, rfl⟩, wa, wb⟩ := w
    exact ⟨⟨⟨n, hn, hb.trans ha⟩, hb.symm, hb.symm⟩, wb, wa⟩
  · simp only [ev_mk, Node.map, Node.eval]
    rw [ckOp_comm c (fun x y => by simp only [BitVec.saddOverflow, Int.add_comm])
      (fun x y => by simp only [BitVec.uaddOverflow, Nat.add_comm]) BitVec.add_comm]

/-- `Mul.comm`, for the swapped arms. -/
@[kanon_arm] theorem Mul.comm.proof : Mul.comm.Stmt := by
  intro S _ _ _ _ _ _ c a b t
  refine comm_refines (fun w => ?_) (fun ρ => ?_)
  · simp only [WT_mk, Node.wt, Node.All] at w ⊢
    obtain ⟨⟨⟨n, hn, ha⟩, hb, rfl⟩, wa, wb⟩ := w
    exact ⟨⟨⟨n, hn, hb.trans ha⟩, hb.symm, hb.symm⟩, wb, wa⟩
  · simp only [ev_mk, Node.map, Node.eval]
    rw [ckOp_comm c (fun x y => by simp only [BitVec.smulOverflow, Int.mul_comm])
      (fun x y => by simp only [BitVec.umulOverflow, Nat.mul_comm]) BitVec.mul_comm]

end BitvecMod
