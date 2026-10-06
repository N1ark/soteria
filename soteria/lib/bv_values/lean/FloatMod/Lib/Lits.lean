import FloatMod.Lib.Float

/-!
# Unary operations, comparisons and conversions of float literals

The folding of the operations of the float module on literals, by their
evaluation (`Sem.ev_FAbs`, …) and what the oracles compute
(`Oracle.Compat`): a unary operation (`Refines.un_lit`), a comparison
(`Refines.cmp_lits`); and the idempotent and involutive operations
(`Refines.un_idem`, `Refines.un_invol`). The arms are proved with them in
`Proofs/Float/*.lean`.
-/

namespace FloatMod

open Classical Kanon Kanon.Sem CoreMod

set_option linter.unusedSectionVars false

namespace Lib

variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
  {LBool : KanonBool.Syntax B} {LCore : CoreMod.Syntax B}
  {LBitvec : BitvecMod.Syntax B LBool LCore} {L : Syntax B LBool LCore LBitvec}
  [KanonBool.Sem LBool] [CoreMod.Sem LCore] [BitvecMod.Sem LBitvec] [Sem L]

/-- A unary operation on a float literal, whose result is the term `r`. -/
theorem Refines.un_lit {K : S.Term → B.Kind} {F : (p : Fp) → FBits p → Option S.Val}
    (hWT : ∀ a t, S.WT (B.node (K a) t) → S.WT a)
    (hev : ∀ ρ a t, S.ev ρ (B.node (K a) t) = fUn (Sem.vfloat L) F (S.ev ρ a))
    {f : CoreMod.Float} {t1 t : S.Ty} {r : S.Term}
    (hr : S.WT (B.node (K (B.node (L.FloatK f) t1)) t) → t1 = L.TFloat f.prec → f.WF →
      S.WT r ∧ S.ty r = t)
    (hv : f.WF → ∀ ρ, F f.prec f.val = S.ev ρ r) :
    S.Refines (B.node (K (B.node (L.FloatK f) t1)) t) r := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;>
    obtain ⟨ht1, hf⟩ := WT_lit.1 (hWT _ _ w)
  · rw [B.ty_node]; exact hr w ht1 hf
  · rw [hev, Sem.ev_Float, fUn_some (Sem.vfloat_inj (L := L)), hv hf] at e
    exact e

/-- The literal of a float of a given precision. -/
theorem lit_WT {g : CoreMod.Float} (hg : g.WF) :
    S.WT (B.node (L.FloatK g) (L.TFloat (L.float_f_prec g))) := by
  rw [WT_lit, Sem.f_prec_eq]; exact ⟨rfl, hg⟩

theorem lit_ty {g : CoreMod.Float} :
    S.ty (B.node (L.FloatK g) (L.TFloat (L.float_f_prec g))) = L.TFloat g.prec := by
  rw [B.ty_node, Sem.f_prec_eq]; rfl

theorem ofNat_toNat_val {p : Fp} (x : FBits p) :
    (⟨p, x.toNat⟩ : CoreMod.Float).val = x := by
  simp [CoreMod.Float.val]

/-- Two unary operations on floats, composed. -/
theorem fUn_comp {g h : (p : Fp) → FBits p → FBits p} (a : Option S.Val) :
    fUn (Sem.vfloat L) (fun p x => some (Sem.vfloat L p (g p x)))
      (fUn (Sem.vfloat L) (fun p x => some (Sem.vfloat L p (h p x))) a) =
    fUn (Sem.vfloat L) (fun p x => some (Sem.vfloat L p (g p (h p x)))) a := by
  rcases a with _ | v
  · simp
  · by_cases h : ∃ p x, v = Sem.vfloat L p x
    · obtain ⟨p, x, rfl⟩ := h
      simp only [fUn_some (Sem.vfloat_inj (L := L))]
    · have e : decF (Sem.vfloat L) (some v) = none := by
        unfold decF
        have h' : ¬∃ p x, some v = some (Sem.vfloat L p x) := fun ⟨p, x, hx⟩ =>
          h ⟨p, x, Option.some.inj hx⟩
        simp only [h', ↓reduceDIte]
      simp only [fUn, e, decF_none]

theorem fbits_abs_abs {p : Fp} (x : FBits p) : x.abs.abs = x.abs := by
  simp only [FBits.abs, BitVec.and_assoc, BitVec.and_self]

theorem fbits_neg_neg {p : Fp} (x : FBits p) : x.neg.neg = x := by
  simp only [FBits.neg, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- The idempotence of a unary operation on floats. -/
theorem Refines.un_idem {K : S.Term → B.Kind} {g : (p : Fp) → FBits p → FBits p}
    (hWT : ∀ a t, S.WT (B.node (K a) t) ↔
      ((∃ p, S.ty a = L.TFloat p) ∧ t = S.ty a) ∧ S.WT a)
    (hev : ∀ ρ a t, S.ev ρ (B.node (K a) t) =
      fUn (Sem.vfloat L) (fun p x => some (Sem.vfloat L p (g p x))) (S.ev ρ a))
    (hg : ∀ p x, g p (g p x) = g p x) {w : S.Term} {t t' : S.Ty} :
    S.Refines (B.node (K (B.node (K w) t)) t') (B.node (K w) t) := by
  refine Refines.intro (fun hw => ?_) (fun ρ v hw _ e => ?_)
  · rw [hWT] at hw
    refine ⟨hw.2, ?_⟩
    rw [B.ty_node, B.ty_node, hw.1.2, B.ty_node]
  · rw [hev, hev, fUn_comp] at e
    rw [hev]; simpa only [hg] using e

/-- An involutive unary operation on floats. -/
theorem Refines.un_invol {K : S.Term → B.Kind} {g : (p : Fp) → FBits p → FBits p}
    (hWT : ∀ a t, S.WT (B.node (K a) t) ↔
      ((∃ p, S.ty a = L.TFloat p) ∧ t = S.ty a) ∧ S.WT a)
    (hev : ∀ ρ a t, S.ev ρ (B.node (K a) t) =
      fUn (Sem.vfloat L) (fun p x => some (Sem.vfloat L p (g p x))) (S.ev ρ a))
    (hg : ∀ p x, g p (g p x) = x) {v : S.Term} {t t' : S.Ty} :
    S.Refines (B.node (K (B.node (K v) t)) t') v := by
  refine Refines.intro (fun hw => ?_) (fun ρ u hw _ e => ?_)
  · rw [hWT] at hw
    have hw2 := (hWT _ _).1 hw.2
    refine ⟨hw2.2, ?_⟩
    rw [B.ty_node, hw.1.2, B.ty_node, hw2.1.2]
  · have hw2 := (hWT _ _).1 ((hWT _ _).1 hw).2
    rw [hev, hev, fUn_comp] at e
    simp only [hg] at e
    obtain ⟨p, hp⟩ := hw2.1.1
    rcases ea : S.ev ρ v with _ | a
    · rw [ea] at e; simp at e
    · obtain ⟨x, rfl⟩ := Sem.ev_float ρ v a p hw2.2 hp ea
      rw [ea, fUn_some (Sem.vfloat_inj (L := L))] at e
      exact e

/-- A comparison of float literals. -/
theorem Refines.cmp_lits {K : S.Term → S.Term → B.Kind} {c : ∀ {p}, FBits p → FBits p → Bool}
    (hWT : ∀ a b t, S.WT (B.node (K a b) t) ↔
      ((∃ p, S.ty a = L.TFloat p) ∧ S.ty b = S.ty a ∧ t = LBool.TBool) ∧ S.WT a ∧ S.WT b)
    (hev : ∀ ρ a b t, S.ev ρ (B.node (K a b) t) =
      fBin (Sem.vfloat L) (fun _ x y => some (KanonBool.Sem.vbool LBool (c x y))) (S.ev ρ a)
        (S.ev ρ b))
    {f1 f2 : CoreMod.Float} {t1 t2 t : S.Ty} :
    S.Refines (B.node (K (B.node (L.FloatK f1) t1) (B.node (L.FloatK f2) t2)) t)
      (B.node (LBool.BoolK (CoreMod.Float.cmp c f1 f2)) LBool.TBool) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> rw [hWT] at w
  · exact ⟨(LBool.WT_Bool _ _).2 rfl, by rw [B.ty_node, B.ty_node, w.1.2.2]⟩
  · obtain ⟨⟨-, h2, -⟩, w1, w2⟩ := w
    obtain ⟨rfl, -⟩ := WT_lit.1 w1
    obtain ⟨rfl, -⟩ := WT_lit.1 w2
    rw [B.ty_node, B.ty_node] at h2
    have hp := L.TFloat_inj _ _ h2
    obtain ⟨p1, b1⟩ := f1
    obtain ⟨p2, b2⟩ := f2
    simp only at hp
    subst hp
    rw [hev, Sem.ev_Float, Sem.ev_Float, fBin_some (Sem.vfloat_inj (L := L))] at e
    rw [KanonBool.Sem.ev_Bool, ← e]
    simp [CoreMod.Float.cmp]

theorem bvUn_some {f : (n : Nat) → BitVec n → Option S.Val} (n : Nat) (x : BitVec n) :
    BitvecMod.bvUn (BitvecMod.Sem.vbv LBitvec) f (some (BitvecMod.Sem.vbv LBitvec n x)) = f n x := by
  rw [BitvecMod.bvUn, BitvecMod.decBV_some BitvecMod.Lib.vbv_sigma_inj]

end Lib

end FloatMod
