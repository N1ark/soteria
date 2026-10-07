import BitvecMod.Proofs.CompareLib
import KanonBool.Proofs

/-!
# The arms that compare bounds on the same term

`Bool.and_`/`Bool.or_` `.r_upper_bounds`, `.r_lower_bounds`, `.r_complementary`,
`.r_upper_eq`, `.r_lower_eq`: each side is a bound `a < c`, `a ≤ c` (upper), `c < a`, `c ≤ a`
(lower) or `a = k` on the same term `a`, whose value is a test `P z` of the integer `z` that is the
value of `a` (signed or not, `bz`), with the bound of the rules (`Bitvec.upper_bound`,
`Bitvec.lower_bound`) in `P` (`BndVal`). The arms then hold by an implication between the tests
(`bnd_and_l`, …), one `omega` on the bounds.
-/

noncomputable section

namespace BitvecMod

open Classical Kanon

section
variable {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [Lang S] [KanonBool.Typed S]
  [CoreMod.Typed S] [Typed S]

/-- A bit-vector as an integer, signed or not. -/
def bz (s : Bool) {n : Nat} (x : BitVec n) : Int := if s then x.toInt else (x.toNat : Int)

/-- A well-typed `B` is a boolean test `P` of the integer value of the bit-vector `a`, signed if
`s`: `B` is poison when `a` is. -/
def BndVal (s : Bool) (a B : S.Term) (P : Int → Bool) : Prop :=
  S.WT B → S.WT a ∧ S.ty B = KanonBool.sort .TBool ∧ ∃ n : Nat, 0 < n ∧
    S.ty a = sort (.TBitVector n) ∧ ∀ ρ, (S.ev ρ a = none → S.ev ρ B = none) ∧
      ∀ xv : BitVec n, S.ev ρ a = some (bv n xv) →
        S.ev ρ B = some (KanonBool.Values.vbool.inj (P (bz s xv)))

set_option hygiene false in
/-- The bound of a comparison with a literal `c`, of a term of width `n`. -/
macro "bnd_bound_tac" : tactic => `(tactic| (
  simp only [Bitvec.upper_bound, Bitvec.lower_bound, proj_mk, Kanon.firstSome_some,
    Kanon.firstSome_none, Option.getD_some, Bitvec.size, ty_mk, ha,
    size_of_ty_TBitVector, Bitvec.to_z, bz, reduceCtorEq]
  cases s <;> simp only [↓reduceIte, Bool.false_eq_true,
    signed_extract_zero (show 0 < n by omega), toNat_ofInt_of_lt c0 c1, Int.toNat_of_nonneg c0]))

set_option hygiene false in
/-- The value of a comparison with a literal `c`, from the value `xv` of the term. -/
macro "bnd_val_tac" : tactic => `(tactic| (
  have hw : Values.width (D := S.toDom) (S.ty a) = n := by
    rw [ha]; simpa using width_sort (S := S) ρ (.inl rfl) (show (0 : Int) < n by omega)
  simp only [ev_mk, Node.eval, Node.map, h]
  rw [hw, hb]
  simp only [withW_bv, asBV_bv, ofBV_some, binB_some, ofB_some, Option.some.injEq,
    Kanon.Embed.inj_eq_iff, bz]
  cases s <;> simp [BitVec.slt, BitVec.ult, BitVec.sle, BitVec.ule] <;> omega))

/-! The tests of the bounds `a < c`, `a ≤ c`, `c < a`, `c ≤ a`. -/

omit [KanonBool.Typed S] [CoreMod.Typed S] in
theorem bnd_up_lt {s : Bool} {a : S.Term} {c : Int} {t t' : S.Ty} :
    BndVal s a (mk (.Lt s a (mk (.BitVec c) t)) t')
      (fun z => decide (z ≤ Bitvec.upper_bound (mk (.Lt s a (mk (.BitVec c) t)) t'))) := by
  intro w
  simp only [WT_mk, Node.wt, Node.All, ty_mk, bv_wf] at w
  obtain ⟨⟨⟨N, hN, ha⟩, ht, rfl⟩, wa, ⟨-, r⟩, -⟩ := w
  obtain ⟨n, rfl⟩ : ∃ n : Nat, N = n := ⟨N.toNat, by omega⟩
  subst ht
  obtain ⟨c0, c1⟩ := r n (.inl ha)
  simp only [Int.toNat_natCast] at c1
  have hb : Bitvec.upper_bound (mk (.Lt s a (mk (.BitVec c) (S.ty a))) (KanonBool.sort .TBool)) =
      bz s (BitVec.ofInt n c) - 1 := by bnd_bound_tac
  refine ⟨wa, ty_mk _ _, n, by omega, ha, fun ρ => ⟨fun h => ?_, fun xv h => ?_⟩⟩
  · simp only [ev_mk, Node.eval, Node.map, h, withW_none]
  · bnd_val_tac

omit [KanonBool.Typed S] [CoreMod.Typed S] in
theorem bnd_up_le {s : Bool} {a : S.Term} {c : Int} {t t' : S.Ty} :
    BndVal s a (mk (.Leq s a (mk (.BitVec c) t)) t')
      (fun z => decide (z ≤ Bitvec.upper_bound (mk (.Leq s a (mk (.BitVec c) t)) t'))) := by
  intro w
  simp only [WT_mk, Node.wt, Node.All, ty_mk, bv_wf] at w
  obtain ⟨⟨⟨N, hN, ha⟩, ht, rfl⟩, wa, ⟨-, r⟩, -⟩ := w
  obtain ⟨n, rfl⟩ : ∃ n : Nat, N = n := ⟨N.toNat, by omega⟩
  subst ht
  obtain ⟨c0, c1⟩ := r n (.inl ha)
  simp only [Int.toNat_natCast] at c1
  have hb : Bitvec.upper_bound (mk (.Leq s a (mk (.BitVec c) (S.ty a))) (KanonBool.sort .TBool)) =
      bz s (BitVec.ofInt n c) := by bnd_bound_tac
  refine ⟨wa, ty_mk _ _, n, by omega, ha, fun ρ => ⟨fun h => ?_, fun xv h => ?_⟩⟩
  · simp only [ev_mk, Node.eval, Node.map, h, withW_none]
  · bnd_val_tac

omit [KanonBool.Typed S] [CoreMod.Typed S] in
theorem bnd_lo_lt {s : Bool} {a : S.Term} {c : Int} {t t' : S.Ty} :
    BndVal s a (mk (.Lt s (mk (.BitVec c) t) a) t')
      (fun z => decide (Bitvec.lower_bound (mk (.Lt s (mk (.BitVec c) t) a) t') ≤ z)) := by
  intro w
  simp only [WT_mk, Node.wt, Node.All, ty_mk, bv_wf] at w
  obtain ⟨⟨⟨N, hN, ha⟩, ht, rfl⟩, ⟨⟨-, r⟩, -⟩, wa⟩ := w
  obtain ⟨n, rfl⟩ : ∃ n : Nat, N = n := ⟨N.toNat, by omega⟩
  subst ht
  obtain ⟨c0, c1⟩ := r n (.inl ha)
  simp only [Int.toNat_natCast] at c1
  have hb : Bitvec.lower_bound (mk (.Lt s (mk (.BitVec c) (S.ty a)) a) (KanonBool.sort .TBool)) =
      bz s (BitVec.ofInt n c) + 1 := by bnd_bound_tac
  refine ⟨wa, ty_mk _ _, n, by omega, ha, fun ρ => ⟨fun h => ?_, fun xv h => ?_⟩⟩
  · simp only [ev_mk, Node.eval, Node.map, h, asBV_none, binB_none_r, ofB_none, withW_none_k]
  · bnd_val_tac

omit [KanonBool.Typed S] [CoreMod.Typed S] in
theorem bnd_lo_le {s : Bool} {a : S.Term} {c : Int} {t t' : S.Ty} :
    BndVal s a (mk (.Leq s (mk (.BitVec c) t) a) t')
      (fun z => decide (Bitvec.lower_bound (mk (.Leq s (mk (.BitVec c) t) a) t') ≤ z)) := by
  intro w
  simp only [WT_mk, Node.wt, Node.All, ty_mk, bv_wf] at w
  obtain ⟨⟨⟨N, hN, ha⟩, ht, rfl⟩, ⟨⟨-, r⟩, -⟩, wa⟩ := w
  obtain ⟨n, rfl⟩ : ∃ n : Nat, N = n := ⟨N.toNat, by omega⟩
  subst ht
  obtain ⟨c0, c1⟩ := r n (.inl ha)
  simp only [Int.toNat_natCast] at c1
  have hb : Bitvec.lower_bound (mk (.Leq s (mk (.BitVec c) (S.ty a)) a) (KanonBool.sort .TBool)) =
      bz s (BitVec.ofInt n c) := by bnd_bound_tac
  refine ⟨wa, ty_mk _ _, n, by omega, ha, fun ρ => ⟨fun h => ?_, fun xv h => ?_⟩⟩
  · simp only [ev_mk, Node.eval, Node.map, h, asBV_none, binB_none_r, ofB_none, withW_none_k]
  · bnd_val_tac

omit [KanonBool.Typed S] [CoreMod.Typed S] in
/-- The test of `a = k`. -/
theorem bnd_eq {s : Bool} {a : S.Term} {k : Int} {t t' : S.Ty} :
    BndVal s a (KanonBool.mk (.Eq a (mk (.BitVec k) t)) t')
      (fun z => decide (z = Bitvec.to_z s (Bitvec.size a) k)) := by
  intro w
  simp only [KanonBool.WT_mk, KanonBool.Node.wt, KanonBool.Node.All, WT_mk, Node.wt, Node.All,
    ty_mk, bv_wf] at w
  obtain ⟨⟨ht, rfl⟩, wa, ⟨⟨N, hN, ha⟩, r⟩, -⟩ := w
  obtain ⟨n, rfl⟩ : ∃ n : Nat, N = n := ⟨N.toNat, by omega⟩
  subst ht
  obtain ⟨c0, c1⟩ := r n (.inl ha)
  simp only [Int.toNat_natCast] at c1
  refine ⟨wa, KanonBool.ty_mk _ _, n, by omega, ha, fun ρ => ⟨fun h => ?_, fun xv h => ?_⟩⟩
  · simp only [KanonBool.ev_mk, KanonBool.Node.eval, KanonBool.Node.map, h, KanonBool.peq]
  · have hw : Values.width (D := S.toDom) (S.ty a) = n := by
      rw [ha]; simpa using width_sort (S := S) ρ (.inl rfl) (show (0 : Int) < n by omega)
    simp only [KanonBool.ev_mk, KanonBool.Node.eval, KanonBool.Node.map, h, ev_mk, Node.eval,
      Node.map]
    rw [hw]
    simp only [ofBV_some, KanonBool.peq, Option.some.injEq, Kanon.Embed.inj_eq_iff, Bitvec.size,
      ha, size_of_ty_TBitVector, Bitvec.to_z, bz]
    cases s <;> simp only [↓reduceIte, Bool.false_eq_true,
      signed_extract_zero (show 0 < n by omega), decide_eq_decide, Sigma.mk.injEq, heq_eq_eq,
      true_and]
    · rw [← BitVec.toNat_inj, toNat_ofInt_of_lt c0 c1]
      omega
    · exact BitVec.toInt_inj.symm

omit [KanonBool.Typed S] [CoreMod.Typed S] in
/-- Two tests of the same term: booleans, poison together, or tests of the same integer. -/
theorem bnd_pair {s : Bool} {a B1 B2 : S.Term} {P Q : Int → Bool} (h1 : BndVal s a B1 P)
    (h2 : BndVal s a B2 Q) (w1 : S.WT B1) (w2 : S.WT B2) (ρ : S.Env) :
    S.ty B1 = KanonBool.sort .TBool ∧
      ((S.ev ρ B1 = none ∧ S.ev ρ B2 = none) ∨
        ∃ z, S.ev ρ B1 = some (KanonBool.Values.vbool.inj (P z)) ∧
          S.ev ρ B2 = some (KanonBool.Values.vbool.inj (Q z))) := by
  obtain ⟨wa, t1, n, -, ha, h1⟩ := h1 w1
  obtain ⟨-, -, n', -, ha', h2⟩ := h2 w2
  obtain rfl : n' = n := by
    have : (n' : Int) = n := by rw [ha] at ha'; simpa using ha'.symm
    omega
  refine ⟨t1, ?_⟩
  rcases ev_cases (ρ := ρ) wa ha with hv | ⟨_, hv, -, xv, rfl⟩
  · exact .inl ⟨(h1 ρ).1 hv, (h2 ρ).1 hv⟩
  · exact .inr ⟨_, (h1 ρ).2 xv hv, (h2 ρ).2 xv hv⟩

set_option hygiene false in
/-- A conjunction or disjunction of two tests of the same term, by `bnd_pair`. -/
macro "bnd_comb_tac" : tactic => `(tactic| (
  refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  all_goals simp only [KanonBool.Bool.and_.spec, KanonBool.Bool.or_.spec, KanonBool.WT_mk,
    KanonBool.Node.wt, KanonBool.Node.All, KanonBool.ty_mk, and_true] at w
  · simp only [KanonBool.Bool.and_.spec, KanonBool.Bool.or_.spec, KanonBool.ty_mk,
      KanonBool.WT_v_true, KanonBool.ty_v_true, true_and]
    try first | exact ⟨w.2.1, w.1.1⟩ | exact ⟨w.2.2, w.1.2⟩
  · obtain ⟨-, hp⟩ := bnd_pair h1 h2 w.2.1 w.2.2 ρ
    simp only [KanonBool.Bool.and_.spec, KanonBool.Bool.or_.spec, KanonBool.ev_mk,
      KanonBool.Node.eval, KanonBool.Node.map] at e
    (try rw [KanonBool.ev_v_true])
    rcases hp with ⟨e1, e2⟩ | ⟨z, e1, e2⟩ <;> rw [e1, e2] at e
    · simp [KanonBool.pand, KanonBool.por] at e
    · have := h z
      rw [← e]
      first | rw [e1] | rw [e2] | skip
      rcases hP : P z <;> rcases hQ : Q z <;>
        simp_all [KanonBool.pand, KanonBool.por, Kanon.Embed.inj_eq_iff]))

/-! The arms: `B1 && B2` is the test that implies the other, `B1 || B2` the one implied, and
`B1 || B2` is true when one of the tests always holds. -/

variable {s : Bool} {a B1 B2 : S.Term} {P Q : Int → Bool}

omit [KanonBool.Typed S] [CoreMod.Typed S] in
theorem bnd_and_l (h1 : BndVal s a B1 P) (h2 : BndVal s a B2 Q)
    (h : ∀ z, P z = true → Q z = true) :
    S.Refines (KanonBool.Bool.and_.spec B1 B2) B1 := by bnd_comb_tac

omit [KanonBool.Typed S] [CoreMod.Typed S] in
theorem bnd_and_r (h1 : BndVal s a B1 P) (h2 : BndVal s a B2 Q)
    (h : ∀ z, Q z = true → P z = true) :
    S.Refines (KanonBool.Bool.and_.spec B1 B2) B2 := by bnd_comb_tac

omit [KanonBool.Typed S] [CoreMod.Typed S] in
theorem bnd_or_l (h1 : BndVal s a B1 P) (h2 : BndVal s a B2 Q)
    (h : ∀ z, Q z = true → P z = true) :
    S.Refines (KanonBool.Bool.or_.spec B1 B2) B1 := by bnd_comb_tac

omit [KanonBool.Typed S] [CoreMod.Typed S] in
theorem bnd_or_r (h1 : BndVal s a B1 P) (h2 : BndVal s a B2 Q)
    (h : ∀ z, P z = true → Q z = true) :
    S.Refines (KanonBool.Bool.or_.spec B1 B2) B2 := by bnd_comb_tac

omit [CoreMod.Typed S] in
theorem bnd_or_true (h1 : BndVal s a B1 P) (h2 : BndVal s a B2 Q)
    (h : ∀ z, P z = false → Q z = true) :
    S.Refines (KanonBool.Bool.or_.spec B1 B2) KanonBool.v_true := by bnd_comb_tac

/-- A test of a bound, or of `a = k`, on a term. -/
macro "bnd_val" : tactic => `(tactic|
  first | exact bnd_up_lt | exact bnd_up_le | exact bnd_lo_lt | exact bnd_lo_le | exact bnd_eq)

/-- An arm on two tests of the same term: its guards, the conditional of its result split, the
combinator of the tests, and the implication between them by `omega` on the bounds. -/
macro "bnd_arm" : tactic => `(tactic| (
  intro _ _ _ _ _ _ _ _ _
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_imp]
  intros
  subst_vars
  (try split)
  all_goals first
    | refine bnd_and_l (by bnd_val) (by bnd_val) ?_
    | refine bnd_and_r (by bnd_val) (by bnd_val) ?_
    | refine bnd_or_l (by bnd_val) (by bnd_val) ?_
    | refine bnd_or_r (by bnd_val) (by bnd_val) ?_
    | refine bnd_or_true (by bnd_val) (by bnd_val) ?_
  all_goals
    intro z hz
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at *
    omega))

end

end BitvecMod
