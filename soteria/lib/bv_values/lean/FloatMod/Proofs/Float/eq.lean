import FloatMod.Soundness.Laws
import FloatMod.Statements.Float.eq

/-! The arms of `Float.eq` that the default tactic does not prove. -/

namespace FloatMod

open Classical Kanon Kanon.Sem CoreMod Lib

set_option linter.unusedSectionVars false

namespace Lib

variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
  {LBool : KanonBool.Syntax B} {LCore : CoreMod.Syntax B}
  {LBitvec : BitvecMod.Syntax B LBool LCore} {L : Syntax B LBool LCore LBitvec}
  [KanonBool.Sem LBool] [CoreMod.Sem LCore] [BitvecMod.Sem LBitvec] [Sem L]

theorem fbits_eq_self {p : Fp} (x : FBits p) : x.eq x = !x.isNaN := by
  simp [FBits.eq]

/-- `v == v` on floats is `v` not being NaN. -/
theorem Refines.feq_self {v : S.Term} {t : S.Ty} :
    S.Refines (B.node (L.FEqK v v) t)
      (B.node (LBool.NotK (B.node (L.FIsK .NaN v) LBool.TBool)) LBool.TBool) := by
  refine Refines.intro (fun w => ?_) (fun ρ u w _ e => ?_) <;> rw [L.WT_FEq] at w
  · obtain ⟨⟨hp, -, ht⟩, wv, -⟩ := w
    refine ⟨(LBool.WT_Not _ _).2
      ⟨⟨by rw [B.ty_node], rfl⟩, (L.WT_FIs _ _ _).2 ⟨⟨hp, rfl⟩, wv⟩⟩,
      by rw [B.ty_node, B.ty_node, ht]⟩
  · obtain ⟨⟨⟨p, hp⟩, -, -⟩, wv, -⟩ := w
    rw [Sem.ev_FEq] at e
    rw [KanonBool.Sem.ev_Not, Sem.ev_FIs]
    rcases ev : S.ev ρ v with _ | a
    · rw [ev] at e; simp at e
    · obtain ⟨x, rfl⟩ := Sem.ev_float ρ v a p wv hp ev
      rw [ev, fBin_some (Sem.vfloat_inj (L := L)), fbits_eq_self] at e
      rw [fUn_some (Sem.vfloat_inj (L := L)), ← e]
      cases h : x.isNaN <;> simp [KanonBool.pnot, FBits.isClass, h, KanonBool.Sem.vbool_inj.eq_iff]

theorem fbits_not_isNaN_of_isZero {p : Fp} {x : FBits p} (h : x.isZero = true) :
    x.isNaN = false := by
  simp only [FBits.isZero, FBits.isNaN, Bool.and_eq_true, beq_iff_eq] at h ⊢
  simp [h.2]

theorem fbits_eq_of_isNaN_left {p : Fp} {x : FBits p} (y : FBits p) (h : x.isNaN = true) :
    x.eq y = false := by
  simp [FBits.eq, h]

theorem fbits_eq_of_isZero_left {p : Fp} {x : FBits p} (y : FBits p) (h : x.isZero = true) :
    x.eq y = y.isZero := by
  have hx := fbits_not_isNaN_of_isZero h
  unfold FBits.eq
  by_cases hy : y.isZero = true
  · simp [hx, hy, h, fbits_not_isNaN_of_isZero hy]
  · have : (x == y) = false := by
      simp only [beq_eq_false_iff_ne]; rintro rfl; exact hy h
    simp [hx, hy, this]

theorem fbits_eq_of_ne_left {p : Fp} {x : FBits p} (y : FBits p) (h1 : x.isNaN = false)
    (h2 : x.isZero = false) : x.eq y = decide (x = y) := by
  unfold FBits.eq
  by_cases hxy : x = y
  · subst hxy; simp [h1]
  · have : (x == y) = false := by simp [hxy]
    simp [h2, this, hxy]

/-- `fp.eq` against a float literal, by the value it compares to. -/
theorem Refines.feq_lit {f : CoreMod.Float} {t2 t : S.Ty} {v r : S.Term}
    (hr : S.WT v → S.ty v = L.TFloat f.prec → S.WT (B.node (L.FloatK f) t2) →
      t2 = L.TFloat f.prec → S.WT r ∧ S.ty r = LBool.TBool)
    (hv : ∀ ρ (y : FBits f.prec), S.WT v → S.ty v = L.TFloat f.prec →
      S.ev ρ v = some (Sem.vfloat L f.prec y) →
      S.ev ρ r = some (KanonBool.Sem.vbool LBool (f.val.eq y))) :
    S.Refines (B.node (L.FEqK (B.node (L.FloatK f) t2) v) t) r := by
  refine Refines.intro (fun w => ?_) (fun ρ u w _ e => ?_) <;>
    obtain ⟨⟨-, h2, ht⟩, w1, wv⟩ := (L.WT_FEq _ _ _).1 w <;>
    obtain ⟨rfl, -⟩ := WT_lit.1 w1 <;> rw [B.ty_node] at h2
  · rw [B.ty_node, ht]; exact hr wv h2 w1 rfl
  · rw [Sem.ev_FEq, Sem.ev_Float] at e
    rcases ev : S.ev ρ v with _ | a
    · rw [ev] at e; simp at e
    · obtain ⟨y, rfl⟩ := Sem.ev_float ρ v a _ wv h2 ev
      rw [ev, fBin_some (Sem.vfloat_inj (L := L))] at e
      rw [hv ρ y wv h2 ev, ← e]

/-- The three cases of `Float.eq` against a literal (`f` NaN, zero, or else). -/
theorem Refines.feq_lit_nan {f : CoreMod.Float} {t2 t : S.Ty} {v : S.Term}
    (hn : L.float_f_is_nan f = true) :
    S.Refines (B.node (L.FEqK (B.node (L.FloatK f) t2) v) t) LBool.bool_v_false := by
  rw [KanonBool.Sem.v_false_eq]
  refine Refines.feq_lit (fun _ _ _ _ => ⟨(LBool.WT_Bool _ _).2 rfl, B.ty_node _ _⟩)
    (fun ρ y _ _ _ => ?_)
  rw [Sem.f_is_nan_eq] at hn
  rw [KanonBool.Sem.ev_Bool, fbits_eq_of_isNaN_left y hn]

theorem Refines.feq_lit_zero {f : CoreMod.Float} {t2 t : S.Ty} {v : S.Term}
    (hz : L.float_f_is_zero f = true) :
    S.Refines (B.node (L.FEqK (B.node (L.FloatK f) t2) v) t)
      (B.node (L.FIsK .Zero v) LBool.TBool) := by
  refine Refines.feq_lit (fun wv hv _ _ => ⟨(L.WT_FIs _ _ _).2 ⟨⟨⟨_, hv⟩, rfl⟩, wv⟩,
    B.ty_node _ _⟩) (fun ρ y _ _ ev => ?_)
  rw [Sem.f_is_zero_eq] at hz
  rw [Sem.ev_FIs, ev, fUn_some (Sem.vfloat_inj (L := L)), fbits_eq_of_isZero_left y hz]
  rfl

theorem Refines.feq_lit_eq {f : CoreMod.Float} {t2 t : S.Ty} {v : S.Term}
    (hn : ¬L.float_f_is_nan f = true) (hz : ¬L.float_f_is_zero f = true) :
    S.Refines (B.node (L.FEqK (B.node (L.FloatK f) t2) v) t)
      (B.node (LBool.EqK (B.node (L.FloatK f) t2) v) LBool.TBool) := by
  refine Refines.feq_lit (fun wv hv w1 ht2 => ⟨(LBool.WT_Eq _ _ _).2
    ⟨⟨by rw [hv, B.ty_node, ht2], rfl⟩, w1, wv⟩, B.ty_node _ _⟩) (fun ρ y _ _ ev => ?_)
  rw [Sem.f_is_nan_eq, Bool.not_eq_true] at hn
  rw [Sem.f_is_zero_eq, Bool.not_eq_true] at hz
  rw [KanonBool.Sem.ev_Eq, ev, Sem.ev_Float, KanonBool.peq_some,
    fbits_eq_of_ne_left y hn hz]
  congr 2
  simp only [decide_eq_decide]
  constructor
  · intro h; have := Sem.vfloat_inj _ _ _ _ h; simp at this; exact this
  · intro h; rw [h]

end Lib

@[kanon_arm] theorem Float.eq.r_lits.main.proof : Float.eq.r_lits.main.Stmt := by
  intro S _ _ B LBool LCore LBitvec L _ _ _ _ O hO f1 t1 f2 t2
  simp only [kanon_spec, Sem.f_eq_eq, Prim.f_eq]
  exact Refines.cmp_lits L.WT_FEq Sem.ev_FEq


@[kanon_arm] theorem Float.eq.r_same.main.proof : Float.eq.r_same.main.Stmt := by
  kanon_rule_lift
  exact Refines.feq_self

@[kanon_arm] theorem Float.eq.r_lit.main.proof : Float.eq.r_lit.main.Stmt := by
  kanon_rule_lift
  · exact Refines.feq_lit_nan ‹_›
  · exact Refines.feq_lit_zero ‹_›
  · exact Refines.feq_lit_eq ‹_› ‹_›

@[kanon_arm] theorem Float.eq.r_lit.swap.proof : Float.eq.r_lit.swap.Stmt := by
  kanon_rule_lift
  · exact Refines.trans (FEq.comm.proof _ _ _ _) (Refines.feq_lit_nan ‹_›)
  · exact Refines.trans (FEq.comm.proof _ _ _ _) (Refines.feq_lit_zero ‹_›)
  · exact Refines.trans (FEq.comm.proof _ _ _ _) (Refines.feq_lit_eq ‹_› ‹_›)

end FloatMod
