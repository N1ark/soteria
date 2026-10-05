import Kanon.Staged.Interface.Float
import Kanon.Lang.Bitvec
import FloatMod.Sem

/-!
# The language, for the float module

The float module is proved once (`FloatMod`): the language gives its interface
(`floatSyntax`) and what it needs of its semantics: its float values, its
floating-point arithmetic (`FS`), the evaluation of the nodes with it, and that
the oracles compute what `FS` does (`Oracle.Compat.float`, from the language's
`Oracle.Compat`).
-/

namespace Kanon

open Classical CoreMod Lib

variable (FS : FloatSem)

namespace Lang

theorem vfloat_inj : ∀ p q (x : FBits p) (y : FBits q), Val.float p x = Val.float q y →
    (⟨p, x⟩ : Σ p, FBits p) = ⟨q, y⟩ := by
  intro p q x y h; cases h; rfl

/-- The float that a value of the language is. -/
theorem decF_eq (v : Val) : FloatMod.decF Val.float (some v) =
    match v with
    | .float p x => some ⟨p, x⟩
    | _ => none := by
  cases v with
  | float p x => exact FloatMod.decF_some vfloat_inj p x
  | _ => rw [FloatMod.decF, dif_neg]; rintro ⟨_, _, h⟩; cases h

theorem fBin_eq (f : (p : Fp) → FBits p → FBits p → Option Val) (a b : Option Val) :
    FloatMod.fBin Val.float f a b = Kanon.fBin f a b := by
  rcases a with _ | va
  · simp [Kanon.fBin]
  rcases b with _ | vb
  · rcases va <;> simp [Kanon.fBin]
  rcases va <;> rcases vb <;> simp [FloatMod.fBin, Kanon.fBin, decF_eq]

theorem fUn_eq (f : (p : Fp) → FBits p → Option Val) (a : Option Val) :
    FloatMod.fUn Val.float f a = match a with
      | some (.float p x) => f p x
      | _ => none := by
  rcases a with _ | va
  · simp
  · rcases va <;> simp [FloatMod.fUn, decF_eq]

theorem bvUn_eq (f : (n : Nat) → BitVec n → Option Val) (a : Option Val) :
    BitvecMod.bvUn Val.bv f a = match a with
      | some (.bv n x) => f n x
      | _ => none := by
  rcases a with _ | va
  · simp [BitvecMod.bvUn, BitvecMod.decBV_none]
  · rcases va <;> simp [BitvecMod.bvUn, decBV_eq]

end Lang

open Lang in
/-- Unfolds the evaluation of a node of the float module, and the operations
of the module on values to the language's. -/
macro "lang_ev_unfold" : tactic => `(tactic| (
  intros
  simp only [bitvecSem_vbv, bitvecSem_vbv', boolSem_vbool, boolSem_vbool']
  simp only [floatSyntax, modBase, sem, ev, evOp1, evOp2, evOp3, fArith, fUn_eq, fBin_eq,
    bvUn_eq]))

/-- `lang_ev_unfold`, then by the cases of the evaluation of the node. -/
macro "lang_ev" : tactic => `(tactic| (
  lang_ev_unfold
  try (split <;> simp_all)))

/-- What the float module needs of the semantics. -/
noncomputable instance floatSem : FloatMod.Sem (S := sem FS) (floatSyntax FS) where
  vfloat := Val.float
  vfloat_inj := Lang.vfloat_inj
  vfloat_ne_vbool _ _ _ e := by cases e
  vfloat_ne_vbv _ _ _ _ e := by cases e
  ev_float ρ t v p w ht e := by
    have := ev_hasSort t w v e
    simp only [floatSyntax, sem] at ht
    rw [ht] at this
    rcases v with _ | _ | _ | ⟨q, x⟩ | _ <;> simp [Val.hasSort] at this
    subst this
    exact ⟨x, rfl⟩
  fadd := FS.add
  fsub := FS.sub
  fmul := FS.mul
  fdiv := FS.div
  frem := FS.rem
  fmin := FS.min
  fmax := FS.max
  ffma := FS.fma
  fsqrt := FS.sqrt
  fround := FS.round
  fconvert := FS.convert
  ftoBv := FS.toBv
  fofBv := FS.ofBv
  ev_Float _ _ _ := rfl
  ev_BvOfFloat ρ rm s n a t := by
    lang_ev_unfold
    rcases ev FS ρ a with _ | ⟨_ | _ | _ | _ | _⟩ <;> rfl
  ev_FloatOfBv ρ rm s p a t := by
    lang_ev_unfold
    rcases ev FS ρ a with _ | ⟨_ | _ | _ | _ | _⟩ <;> rfl
  ev_FloatOfBvRaw ρ p a t := by
    lang_ev_unfold
    rcases ev FS ρ a with _ | ⟨_ | _ | _ | _ | _⟩ <;> rfl
  ev_FloatOfFloat ρ rm p a t := by
    lang_ev_unfold
    rcases ev FS ρ a with _ | ⟨_ | _ | _ | _ | _⟩ <;> rfl
  ev_FAbs := by lang_ev
  ev_FNeg := by lang_ev
  ev_FSqrt := by lang_ev
  ev_FRound := by lang_ev
  ev_FIs := by lang_ev
  ev_FIsNeg := by lang_ev
  ev_FIsPos := by lang_ev
  ev_FEq := by lang_ev
  ev_FLeq := by lang_ev
  ev_FLt := by lang_ev
  ev_FAdd := by lang_ev
  ev_FSub := by lang_ev
  ev_FMul := by lang_ev
  ev_FDiv := by lang_ev
  ev_FRem := by lang_ev
  ev_FMin := by lang_ev
  ev_FMax := by lang_ev
  ev_Fma ρ a b c t := by
    lang_ev
    rcases ev FS ρ a with _ | ⟨_ | _ | _ | ⟨p, x⟩ | _⟩ <;>
      rcases ev FS ρ b with _ | ⟨_ | _ | _ | ⟨q, y⟩ | _⟩ <;>
      rcases ev FS ρ c with _ | ⟨_ | _ | _ | ⟨r, z⟩ | _⟩ <;>
      simp [evFma, FloatMod.fTern, Lang.decF_eq]
  float_wf_Float _ _ := Iff.rfl
  fp_of_ty_TFloat _ := rfl
  fp_size_eq _ := rfl
  f_prec_eq _ := rfl
  fp_of_size_eq _ := rfl
  f_equal_eq _ _ := rfl
  f_bits_equal_eq _ _ := rfl
  f_to_bits_eq _ := rfl
  f_of_bits_eq _ _ := rfl
  f_nan_eq _ := rfl
  f_is_class_eq _ _ := rfl
  f_is_nan_eq _ := rfl
  f_is_zero_eq _ := rfl
  f_is_negative_eq _ := rfl
  f_is_positive_eq _ := rfl
  f_eq_eq _ _ := rfl
  f_lt_eq _ _ := rfl
  f_le_eq _ _ := rfl
  f_abs_eq _ := rfl
  f_neg_eq _ := rfl

/-- What the float module assumes of the oracles, from what the language
assumes of them. -/
theorem Oracle.Compat.float {FS : FloatSem} {orc : Oracle} (h : orc.Compat FS) :
    FloatMod.Oracle.Compat (S := sem FS) (floatSyntax FS) orc.f_add orc.f_sub orc.f_mul
      orc.f_div orc.f_rem orc.f_fmod orc.f_min orc.f_max orc.f_fma orc.f_sqrt orc.f_round
      orc.f_convert orc.f_to_int orc.f_of_int where
  bin op lit hmem f1 f2 w1 w2 hp := by
    have key := fun op' hm => h.bin op' lit hm f1 f2 w1 w2 hp
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨e1, e2, e3⟩ := key .FAdd (by simp)
      exact ⟨e1, e2, (Lang.fBin_eq _ _ _).trans e3⟩
    · obtain ⟨e1, e2, e3⟩ := key .FSub (by simp)
      exact ⟨e1, e2, (Lang.fBin_eq _ _ _).trans e3⟩
    · obtain ⟨e1, e2, e3⟩ := key .FMul (by simp)
      exact ⟨e1, e2, (Lang.fBin_eq _ _ _).trans e3⟩
    · obtain ⟨e1, e2, e3⟩ := key .FDiv (by simp)
      exact ⟨e1, e2, (Lang.fBin_eq _ _ _).trans e3⟩
    · obtain ⟨e1, e2, e3⟩ := key .FRem (by simp)
      exact ⟨e1, e2, (Lang.fBin_eq _ _ _).trans e3⟩
    · obtain ⟨e1, e2, e3⟩ := key .FMin (by simp)
      exact ⟨e1, e2, (Lang.fBin_eq _ _ _).trans e3⟩
    · obtain ⟨e1, e2, e3⟩ := key .FMax (by simp)
      exact ⟨e1, e2, (Lang.fBin_eq _ _ _).trans e3⟩
  fma f1 f2 f3 w1 w2 w3 h2 h3 := by
    obtain ⟨e1, e2, e3⟩ := h.fma f1 f2 f3 w1 w2 w3 h2 h3
    refine ⟨e1, e2, ?_⟩
    rcases f1 with ⟨p, b1⟩; rcases f2 with ⟨q, b2⟩; rcases f3 with ⟨r, b3⟩
    simp only at h2 h3; subst h2; subst h3
    simp only [CoreMod.Float.sem] at e3
    rw [evFma, dif_pos ⟨rfl, rfl⟩] at e3
    exact (FloatMod.fTern_some (vf := Val.float) Lang.vfloat_inj _ _ _ _).trans e3
  sqrt f w := by
    obtain ⟨e1, e2, e3⟩ := h.sqrt f w
    exact ⟨e1, e2, Option.some.inj e3⟩
  round rm f w := by
    obtain ⟨e1, e2, e3⟩ := h.round rm f w
    exact ⟨e1, e2, Option.some.inj e3⟩
  convert rm p f w := by
    obtain ⟨e1, e2, e3⟩ := h.convert rm p f w
    exact ⟨e1, e2, Option.some.inj e3⟩
  to_int rm s n f z w hn e :=
    eq_of_heq (Val.bv.inj (Option.some.inj (h.to_int rm s n f z w hn e))).2
  of_int rm s p n z f hn h0 h1 e := by
    obtain ⟨e1, e2, e3⟩ := h.of_int rm s p n z f hn h0 h1 e
    exact ⟨e1, e2, Option.some.inj e3⟩
  fmod f1 f2 w1 w2 hp :=
    ⟨(h.fmod f1 f2 ⟨fun _ => none⟩ w1 w2 hp).1, (h.fmod f1 f2 ⟨fun _ => none⟩ w1 w2 hp).2.1,
      fun ρ => (h.fmod f1 f2 ρ w1 w2 hp).2.2⟩

end Kanon
