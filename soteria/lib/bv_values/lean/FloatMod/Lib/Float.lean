import FloatMod.Lib.Lift

/-!
# Floats by evaluation

The literals of the float module (`WT_lit`) and the folding of the operations
on them by the oracles, which compute what the arithmetic of the language does
(`Oracle.Compat`): `Refines.bin_lits` for the binary operations, given to
`kanon_close_lemmas` for each of them (`Refines.fAdd_lits`, …).
-/

namespace FloatMod

open Classical Kanon Kanon.Sem CoreMod

set_option linter.unusedSectionVars false

namespace Lib

variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
  {LBool : KanonBool.Syntax B} {LCore : CoreMod.Syntax B}
  {LBitvec : BitvecMod.Syntax B LBool LCore} {L : Syntax B LBool LCore LBitvec}
  [KanonBool.Sem LBool] [CoreMod.Sem LCore] [BitvecMod.Sem LBitvec] [Sem L]

/-- A float literal is of the sort of its precision, which it fits. -/
theorem WT_lit {f : CoreMod.Float} {t : S.Ty} :
    S.WT (B.node (L.FloatK f) t) ↔ t = L.TFloat f.prec ∧ f.WF := by
  rw [L.WT_Float, Sem.float_wf_Float, Sem.f_prec_eq]; rfl

/-- Folding a binary operation on float literals of the same precision into
the literal that `lit` computes, when it computes what the operation does. -/
theorem Refines.bin_lits {K : S.Term → S.Term → B.Kind}
    {op : (p : Fp) → FBits p → FBits p → FBits p} {lit : CoreMod.Float → CoreMod.Float → CoreMod.Float}
    (hlit : ∀ f1 f2 : CoreMod.Float, f1.WF → f2.WF → f1.prec = f2.prec →
      (lit f1 f2).prec = f1.prec ∧ (lit f1 f2).WF ∧
        fBin (Sem.vfloat L) (fun p x y => some (Sem.vfloat L p (op p x y)))
          (some (Sem.vfloat L f1.prec f1.val)) (some (Sem.vfloat L f2.prec f2.val)) =
          some (Sem.vfloat L (lit f1 f2).prec (lit f1 f2).val))
    (hWT : ∀ a b t, S.WT (B.node (K a b) t) ↔
      ((∃ p, S.ty a = L.TFloat p) ∧ S.ty b = S.ty a ∧ t = S.ty a) ∧ S.WT a ∧ S.WT b)
    (hev : ∀ ρ a b t, S.ev ρ (B.node (K a b) t) =
      fBin (Sem.vfloat L) (fun p x y => some (Sem.vfloat L p (op p x y))) (S.ev ρ a) (S.ev ρ b))
    {f1 f2 : CoreMod.Float} {t1 t2 t : S.Ty} :
    S.Refines (B.node (K (B.node (L.FloatK f1) t1) (B.node (L.FloatK f2) t2)) t)
      (B.node (L.FloatK (lit f1 f2)) (L.TFloat (L.float_f_prec (lit f1 f2)))) := by
  have key : S.WT (B.node (K (B.node (L.FloatK f1) t1) (B.node (L.FloatK f2) t2)) t) →
      t = L.TFloat f1.prec ∧ f1.WF ∧ f2.WF ∧ f1.prec = f2.prec := by
    intro w
    obtain ⟨⟨-, h2, h3⟩, w1, w2⟩ := (hWT _ _ _).1 w
    obtain ⟨rfl, h1⟩ := WT_lit.1 w1
    obtain ⟨rfl, h4⟩ := WT_lit.1 w2
    simp only [B.ty_node] at h2 h3
    exact ⟨h3, h1, h4, (L.TFloat_inj _ _ h2).symm⟩
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;>
    obtain ⟨ht, h1, h2, hp⟩ := key w <;> obtain ⟨e1, e2, e3⟩ := hlit f1 f2 h1 h2 hp
  · rw [Sem.f_prec_eq]
    exact ⟨WT_lit.2 ⟨rfl, e2⟩, by rw [B.ty_node, B.ty_node, ht]; exact congrArg _ e1⟩
  · rw [hev, Sem.ev_Float, Sem.ev_Float, e3] at e
    rw [Sem.ev_Float]; exact e

variable {O : Ops L}

theorem Refines.fAdd_lits (hO : O.Sound) {f1 f2 : CoreMod.Float} {t1 t2 t : S.Ty} :
    S.Refines (B.node (L.FAddK (B.node (L.FloatK f1) t1) (B.node (L.FloatK f2) t2)) t)
      (B.node (L.FloatK (O.float_f_add f1 f2)) (L.TFloat (L.float_f_prec (O.float_f_add f1 f2)))) :=
  Refines.bin_lits (hO.float_orc.bin _ _ (by simp)) L.WT_FAdd Sem.ev_FAdd

theorem Refines.fSub_lits (hO : O.Sound) {f1 f2 : CoreMod.Float} {t1 t2 t : S.Ty} :
    S.Refines (B.node (L.FSubK (B.node (L.FloatK f1) t1) (B.node (L.FloatK f2) t2)) t)
      (B.node (L.FloatK (O.float_f_sub f1 f2)) (L.TFloat (L.float_f_prec (O.float_f_sub f1 f2)))) :=
  Refines.bin_lits (hO.float_orc.bin _ _ (by simp)) L.WT_FSub Sem.ev_FSub

theorem Refines.fMul_lits (hO : O.Sound) {f1 f2 : CoreMod.Float} {t1 t2 t : S.Ty} :
    S.Refines (B.node (L.FMulK (B.node (L.FloatK f1) t1) (B.node (L.FloatK f2) t2)) t)
      (B.node (L.FloatK (O.float_f_mul f1 f2)) (L.TFloat (L.float_f_prec (O.float_f_mul f1 f2)))) :=
  Refines.bin_lits (hO.float_orc.bin _ _ (by simp)) L.WT_FMul Sem.ev_FMul

theorem Refines.fDiv_lits (hO : O.Sound) {f1 f2 : CoreMod.Float} {t1 t2 t : S.Ty} :
    S.Refines (B.node (L.FDivK (B.node (L.FloatK f1) t1) (B.node (L.FloatK f2) t2)) t)
      (B.node (L.FloatK (O.float_f_div f1 f2)) (L.TFloat (L.float_f_prec (O.float_f_div f1 f2)))) :=
  Refines.bin_lits (hO.float_orc.bin _ _ (by simp)) L.WT_FDiv Sem.ev_FDiv

theorem Refines.fRem_lits (hO : O.Sound) {f1 f2 : CoreMod.Float} {t1 t2 t : S.Ty} :
    S.Refines (B.node (L.FRemK (B.node (L.FloatK f1) t1) (B.node (L.FloatK f2) t2)) t)
      (B.node (L.FloatK (O.float_f_rem f1 f2)) (L.TFloat (L.float_f_prec (O.float_f_rem f1 f2)))) :=
  Refines.bin_lits (hO.float_orc.bin _ _ (by simp)) L.WT_FRem Sem.ev_FRem

theorem Refines.fMin_lits (hO : O.Sound) {f1 f2 : CoreMod.Float} {t1 t2 t : S.Ty} :
    S.Refines (B.node (L.FMinK (B.node (L.FloatK f1) t1) (B.node (L.FloatK f2) t2)) t)
      (B.node (L.FloatK (O.float_f_min f1 f2)) (L.TFloat (L.float_f_prec (O.float_f_min f1 f2)))) :=
  Refines.bin_lits (hO.float_orc.bin _ _ (by simp)) L.WT_FMin Sem.ev_FMin

theorem Refines.fMax_lits (hO : O.Sound) {f1 f2 : CoreMod.Float} {t1 t2 t : S.Ty} :
    S.Refines (B.node (L.FMaxK (B.node (L.FloatK f1) t1) (B.node (L.FloatK f2) t2)) t)
      (B.node (L.FloatK (O.float_f_max f1 f2)) (L.TFloat (L.float_f_prec (O.float_f_max f1 f2)))) :=
  Refines.bin_lits (hO.float_orc.bin _ _ (by simp)) L.WT_FMax Sem.ev_FMax

attribute [kanon_close_lemma] Refines.fAdd_lits Refines.fSub_lits Refines.fMul_lits
  Refines.fDiv_lits Refines.fRem_lits Refines.fMin_lits Refines.fMax_lits

end Lib

end FloatMod
