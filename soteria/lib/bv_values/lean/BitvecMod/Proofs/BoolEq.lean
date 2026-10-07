import BitvecMod.Proofs.ArithLib
import BitvecMod.Proofs.CompareConst
import BitvecMod.Statements.Bool.eq

/-!
# The proofs of the arms `r_msb` and `r_mul_const` of `Bool.eq`

`r_msb` compares the low bits below the bound on the most significant bits;
`r_mul_const` characterizes `k = c * x`, without overflow, by the quotient `k / c`.
-/

namespace BitvecMod

namespace BoolEq
open Arith

theorem eq_iff_extract_low {n k : Nat} {x y : BitVec n} (hx : (x.toNat : Int) < 2 ^ k)
    (hy : (y.toNat : Int) < 2 ^ k) : x = y ↔ x.extractLsb' 0 k = y.extractLsb' 0 k := by
  have e : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by push_cast; rfl
  rw [← BitVec.toNat_inj, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, Nat.shiftRight_zero, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem msb_lift {x : Nat} {p q : Int} (h : (x : Int) < 2 ^ (p + 1).toNat) (hpq : p + 1 ≤ q) :
    (x : Int) < 2 ^ q.toNat :=
  Int.lt_of_lt_of_le h (pow_le_pow_int (by omega))

variable {n : Nat}

theorem toInt_eq_iff_ofInt {x : BitVec n} {q : Int} (h0 : 0 < n)
    (hr : -2 ^ (n - 1) ≤ q ∧ q < 2 ^ (n - 1)) : x.toInt = q ↔ x = BitVec.ofInt n q := by
  constructor
  · intro h; rw [← BitVec.toInt_inj, BitVec.toInt_ofInt_eq_self h0 hr.1 hr.2, h]
  · intro h; rw [h, BitVec.toInt_ofInt_eq_self h0 hr.1 hr.2]

theorem mul_eq_s (k c x : BitVec n) (hov : c.smulOverflow x = false) :
    (k = c * x) ↔
      (if c.toInt = 0 then k.toInt = 0
       else if k.toInt = 0 then x = 0#n
       else if c.toInt ∣ k.toInt then
         ((-2 ^ (n - 1) ≤ k.toInt.tdiv c.toInt ∧ k.toInt.tdiv c.toInt < 2 ^ (n - 1)) ∧
           x = BitVec.ofInt n (k.toInt.tdiv c.toInt))
       else False) := by
  rw [← BitVec.toInt_inj, toInt_mul_ok hov]
  have bx := toInt_bounds x
  by_cases hc : c.toInt = 0
  · simp only [hc, ↓reduceIte, Int.zero_mul]
  simp only [hc, ↓reduceIte]
  by_cases hk : k.toInt = 0
  · simp only [hk, ↓reduceIte]
    rw [← BitVec.toInt_inj, BitVec.toInt_zero]
    constructor
    · intro h
      rcases Int.mul_eq_zero.1 h.symm with h | h
      · exact absurd h hc
      · exact h
    · intro h; rw [h, Int.mul_zero]
  simp only [hk, ↓reduceIte]
  by_cases hd : c.toInt ∣ k.toInt
  · simp only [hd, ↓reduceIte]
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; exact absurd (by simp [BitVec.eq_nil c]) hc
      · exact h0
    have hq := Int.mul_tdiv_cancel' hd
    generalize k.toInt.tdiv c.toInt = q at *
    rw [← hq, Int.mul_eq_mul_left_iff hc]
    constructor
    · intro h; subst h
      exact ⟨bx, (toInt_eq_iff_ofInt hn bx).1 rfl⟩
    · rintro ⟨hr, h⟩
      exact ((toInt_eq_iff_ofInt hn hr).2 h).symm
  · simp only [hd, ↓reduceIte, iff_false]
    intro h; exact hd ⟨_, h⟩

theorem mul_eq_u (k c x : BitVec n) (hov : c.umulOverflow x = false) :
    (k = c * x) ↔
      (if (c.toNat : Int) = 0 then (k.toNat : Int) = 0
       else if (k.toNat : Int) = 0 then x = 0#n
       else if (c.toNat : Int) ∣ (k.toNat : Int) then
         ((0 ≤ (k.toNat : Int).tdiv c.toNat ∧ (k.toNat : Int).tdiv c.toNat < 2 ^ n) ∧
           x = BitVec.ofInt n ((k.toNat : Int).tdiv c.toNat))
       else False) := by
  rw [← BitVec.toNat_inj, toNat_mul_ok hov, ← Int.ofNat_inj, Int.natCast_mul]
  have bx := toNat_lt_int x
  by_cases hc : (c.toNat : Int) = 0
  · simp only [hc, ↓reduceIte, Int.zero_mul]
  simp only [hc, ↓reduceIte]
  by_cases hk : (k.toNat : Int) = 0
  · simp only [hk, ↓reduceIte]
    rw [← BitVec.toNat_inj, BitVec.toNat_zero, ← Int.ofNat_inj]
    constructor
    · intro h
      rcases Int.mul_eq_zero.1 h.symm with h | h
      · exact absurd h hc
      · exact h
    · intro h; rw [h, Int.natCast_zero, Int.mul_zero]
  simp only [hk, ↓reduceIte]
  by_cases hd : (c.toNat : Int) ∣ (k.toNat : Int)
  · simp only [hd, ↓reduceIte]
    have hq := Int.mul_tdiv_cancel' hd
    generalize (k.toNat : Int).tdiv c.toNat = q at *
    rw [← hq, Int.mul_eq_mul_left_iff hc]
    have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
    constructor
    · intro h; subst h
      refine ⟨bx, ?_⟩
      rw [← BitVec.toNat_inj, BitVec.toNat_ofInt, e, Int.emod_eq_of_lt bx.1 bx.2, Int.toNat_natCast]
    · rintro ⟨hr, h⟩
      rw [h, BitVec.toNat_ofInt, e, Int.emod_eq_of_lt hr.1 hr.2, Int.toNat_of_nonneg hr.1]
  · simp only [hd, ↓reduceIte, iff_false]
    intro h; exact hd ⟨_, h⟩

theorem toNat_ofInt_lit {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ n) :
    ((BitVec.ofInt n z).toNat : Int) = z :=
  (lit_facts n z).1 h0 h1

end BoolEq

section
variable {D : Kanon.Dom} [Values D]

theorem BoolEq.bv_inj {n : Nat} {a b : BitVec n} : (bv (D := D) n a = bv n b) ↔ a = b := by
  simp only [bv, Kanon.Embed.inj_eq_iff, Sigma.mk.injEq, heq_eq_eq, true_and]

end

@[kanon_arm] theorem Bool.eq.r_msb.main.proof : Bool.eq.r_msb.main.Stmt := by
  (try intro _)
  intros
  kanon_rule_lift
  all_goals (try simp only [Kanon.Embed.proj_eq_some_iff] at *)
  all_goals kanon_on_refines (
    (try dsimp only)
    bv_split_ifs
    all_goals (try kanon_lift_body)
    all_goals (try simp only [kanon_spec, kanon_body])
    all_goals (try first
      | kanon_refl
      | (kanon_comm; done)))
  all_goals kanon_on_refines (
    refine Kanon.Sem.Refines.intro ?_ ?_
    · bv_arith_wt
    bv_arith_sem_core)
  all_goals (try (repeat' (first
    | (simp only [BitvecMod.ckOp_some, BitvecMod.ckOp_none_l, BitvecMod.ckOp_none_r,
        BitvecMod.binOp_some, BitvecMod.binOp_none_l, BitvecMod.binOp_none_r,
        BitvecMod.negOp_some, BitvecMod.negOp_none, Option.some.injEq, reduceCtorEq, Option.map_none, Option.map_some, BitvecMod.binB_some, BitvecMod.binB_none_l, BitvecMod.binB_none_r, BitvecMod.ofB_none, BitvecMod.ofB_some] at e)
    | split at e)))
  all_goals (try subst e)
  all_goals (try bv_arith_lit_ops)
  all_goals (refine ⟨_, _, rfl, rfl, ?_⟩)
  all_goals (simp only [Kanon.Embed.inj_eq_iff, Sigma.mk.injEq, heq_eq_eq, true_and])
  all_goals (rw [decide_eq_decide]; apply BoolEq.eq_iff_extract_low
    <;> exact BoolEq.msb_lift (by assumption) (by omega))

section
variable {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [Lang S] [KanonBool.Typed S]
  [CoreMod.Typed S] [Typed S]

omit [KanonBool.Typed S] [CoreMod.Typed S] in
/-- The value of `n == m * x`: that of `x`, the non-overflow of the product, the equality. -/
theorem eqm_lhs {n m : Int} {t2 t6 t8 : S.Ty} {ck : CoreMod.Checked} {x : S.Term} {ρ : S.Env}
    {v : S.Val}
    (w : S.WT (KanonBool.mk (.Eq (mk (.BitVec n) t2) (mk (.Mul ck (mk (.BitVec m) t6) x) t8))
      (KanonBool.sort .TBool)))
    (e : S.ev ρ (KanonBool.mk (.Eq (mk (.BitVec n) t2) (mk (.Mul ck (mk (.BitVec m) t6) x) t8))
      (KanonBool.sort .TBool)) = some v) :
    ∃ N : Nat, 0 < N ∧ S.ty x = sort (.TBitVector N) ∧ 0 ≤ n ∧ n < 2 ^ N ∧ 0 ≤ m ∧ m < 2 ^ N ∧
      ∃ xv : BitVec N, S.ev ρ x = some (bv N xv) ∧
        (ck.signed = true → (BitVec.ofInt N m).smulOverflow xv = false) ∧
        (ck.unsigned = true → (BitVec.ofInt N m).umulOverflow xv = false) ∧
        v = KanonBool.Values.vbool.inj (decide (BitVec.ofInt N n = BitVec.ofInt N m * xv)) := by
  simp only [KanonBool.WT_mk, KanonBool.Node.wt, KanonBool.Node.All] at w
  obtain ⟨⟨hB, -⟩, wA, wB⟩ := w
  have wA' := wA
  simp only [WT_mk, Node.wt, Node.All] at wA'
  obtain ⟨⟨⟨N, hN, h2⟩, -⟩, -⟩ := wA'
  obtain ⟨N, rfl⟩ : ∃ k : Nat, N = k := ⟨N.toNat, by omega⟩
  obtain ⟨n0, n1, hA⟩ := cc_lit (ρ := ρ) wA h2 (by omega)
  simp only [ty_mk] at hB
  simp only [KanonBool.ev_mk, KanonBool.Node.eval, KanonBool.Node.map, hA] at e
  rcases ev_cases (ρ := ρ) wB (by rw [ty_mk]; exact hB.trans h2) with hv | ⟨_, hv, -, b, rfl⟩
  · simp [hv, KanonBool.peq] at e
  replace hv : S.ev ρ (mk (.Mul ck (mk (.BitVec m) t6) x) t8) = some (bv N b) := hv
  obtain ⟨hM, hX, wM, wX, a, xv, ha, hx, hs, hu, rfl⟩ := cc_mul wB (hB.trans h2) (by omega) hv
  simp only [ty_mk] at hM hX
  obtain ⟨m0, m1, hm⟩ := cc_lit (ρ := ρ) wM hM (by omega)
  rw [hm] at ha
  obtain rfl := cc_bv_eq ha
  simp only [hv, KanonBool.peq, Option.some.injEq, BoolEq.bv_inj] at e
  exact ⟨N, by omega, hX.trans hM, n0, n1, m0, m1, xv, hx, hs, hu, e.symm⟩
omit [KanonBool.Typed S] [CoreMod.Typed S] [Typed S] in
/-- The typing of `n == m * x`: that of `x`. -/
theorem eqm_wt {n m : Int} {t2 t6 t8 : S.Ty} {ck : CoreMod.Checked} {x : S.Term}
    (w : S.WT (KanonBool.mk (.Eq (mk (.BitVec n) t2) (mk (.Mul ck (mk (.BitVec m) t6) x) t8))
      (KanonBool.sort .TBool))) :
    ∃ N : Int, 0 < N ∧ S.ty x = sort (.TBitVector N) ∧ S.WT x := by
  simp only [KanonBool.WT_mk, KanonBool.Node.wt, KanonBool.Node.All, WT_mk, Node.wt, Node.All,
    ty_mk] at w
  obtain ⟨-, -, ⟨⟨⟨N, hN, hM⟩, hX, -⟩, -, wX⟩⟩ := w
  exact ⟨N, hN, hX.trans hM, wX⟩
end

set_option hygiene false in
/-- A branch of `Bool.eq.r_mul_const`: the typing of its right side, and its value from that of
the left side (`eqm_lhs`) by `BoolEq.mul_eq_s` / `BoolEq.mul_eq_u`. -/
macro "eqm_branch" : tactic => `(tactic| (
  refine Kanon.Sem.Refines.intro ?_ (fun ρ v w _ e => ?_)
  · intro w
    first
      | exact ⟨KanonBool.WT_v_true, by rw [KanonBool.ty_v_true, KanonBool.ty_mk]⟩
      | exact ⟨KanonBool.WT_v_false, by rw [KanonBool.ty_v_false, KanonBool.ty_mk]⟩
      | (obtain ⟨N, hN, hx, wx⟩ := eqm_wt w
         simp only [KanonBool.WT_mk, KanonBool.Node.wt, KanonBool.Node.All, KanonBool.ty_mk,
           WT_mk, Node.wt, Node.All, bv_wf, ty_mk, bv_zero, mk_masked, hx, wx,
           size_of_ty_TBitVector, sort_inj_iff, Srt.TBitVector.injEq, reduceCtorEq, or_false,
           forall_eq', and_true, true_and]
         have hp : (0 : Int) < 2 ^ N.toNat := Int.pow_pos (by decide)
         and_intros
         all_goals first
           | rfl
           | exact ⟨N, hN, rfl⟩
           | exact Int.le_refl 0
           | exact hp
           | exact Int.emod_nonneg _ (by omega)
           | exact Int.emod_lt_of_pos _ hp)
  · obtain ⟨N, hN, hx, n0, n1, m0, m1, xv, hxv, hsm, hum, rfl⟩ := eqm_lhs w e
    have hw : Values.width (D := S.toDom) (sort (.TBitVector N)) = N := by
      simpa using width_sort (S := S) ρ (.inl rfl) (show (0 : Int) < N by omega)
    simp only [KanonBool.ev_v_true, KanonBool.ev_v_false, KanonBool.ev_mk, KanonBool.Node.eval,
      KanonBool.Node.map, hxv, ev_mk, Node.eval, Node.map, bv_zero, mk_masked, hx,
      size_of_ty_TBitVector, Int.toNat_natCast]
    (try rw [hw])
    simp only [ofBV_some, KanonBool.peq, Option.some.injEq, Kanon.Embed.inj_eq_iff, BoolEq.bv_inj,
      ofInt_emod_two_pow, ofInt_zero']
    simp only [hx, size_of_ty_TBitVector, signed_extract_zero hN, z_lsl_one, Int.toNat_natCast,
      natCast_sub_one_toNat] at *
    first
      | (have hsg : ck.signed = true := by simpa [Bitvec.is_checked, hu] using hg
         simp only [BoolEq.mul_eq_s _ _ _ (hsm hsg)])
      | simp only [BoolEq.mul_eq_u _ _ _ (hum hu), BoolEq.toNat_ofInt_lit n0 n1,
          BoolEq.toNat_ofInt_lit m0 m1]
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and, Prim.divisible, Prim.tdiv, decide_eq_true_eq,
      Bool.and_eq_true] at *
    simp_all
    all_goals (intros; omega)))


@[kanon_arm] theorem Bool.eq.r_mul_const.main.proof : Bool.eq.r_mul_const.main.Stmt := by
  intro S _ _ _ _ _ _ O hO n t2 ck m t6 x t8 hg
  (try kanon_guards)
  (try kanon_split)
  (try subst_vars)
  (try simp only [kanon_spec, kanon_body])
  (try dsimp only)
  cases hu : ck.unsigned <;>
    simp only [Bool.not_true, Bool.not_false, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false]
  all_goals (repeat' split)
  all_goals (try (mul_untag; kanon_lift_body))
  all_goals (try simp only [kanon_spec, kanon_body, KanonBool.Bool.eq.spec])
  all_goals eqm_branch

end BitvecMod
