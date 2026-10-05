import FloatMod.Statements
import BitvecMod.Lib.Lift
import BitvecMod.Lib.Cong

/-!
# Refinement by congruence

The congruence lemmas of the nodes of the float module, with which
`kanon_congr` proves that the specs are monotone (`Lifts.lean`): the nodes are
strict in their operands (`BitvecMod.Lib.refines_node1`, …).
-/

namespace FloatMod

open Classical Kanon Kanon.Sem CoreMod BitvecMod.Lib

set_option linter.unusedSectionVars false

@[simp] theorem fTern_none_l {V : Type} {vf : (p : Fp) → FBits p → V} {f} {b c : Option V} :
    fTern vf f none b c = none := by simp [fTern]
@[simp] theorem fTern_none_m {V : Type} {vf : (p : Fp) → FBits p → V} {f} {a c : Option V} :
    fTern vf f a none c = none := by simp only [fTern, decF_none]; split <;> simp_all
@[simp] theorem fTern_none_r {V : Type} {vf : (p : Fp) → FBits p → V} {f} {a b : Option V} :
    fTern vf f a b none = none := by simp only [fTern, decF_none]; split <;> simp_all

theorem bvUn_none {V : Type} {vbv : (n : Nat) → BitVec n → V} {f} :
    BitvecMod.bvUn vbv f none = none := by simp [BitvecMod.bvUn, BitvecMod.decBV_none]

attribute [bv_wt] Syntax.WT_BvOfFloat Syntax.WT_FloatOfBv Syntax.WT_FloatOfBvRaw
  Syntax.WT_FloatOfFloat Syntax.WT_FAbs Syntax.WT_FNeg Syntax.WT_FSqrt Syntax.WT_FRound
  Syntax.WT_FIs Syntax.WT_FIsNeg Syntax.WT_FIsPos Syntax.WT_FEq Syntax.WT_FLeq Syntax.WT_FLt
  Syntax.WT_FAdd Syntax.WT_FSub Syntax.WT_FMul Syntax.WT_FDiv Syntax.WT_FRem Syntax.WT_FMin
  Syntax.WT_FMax Syntax.WT_Fma Syntax.WT_Float Sem.float_wf_Float

namespace Lib

variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
  {LBool : KanonBool.Syntax B} {LCore : CoreMod.Syntax B}
  {LBitvec : BitvecMod.Syntax B LBool LCore} {L : Syntax B LBool LCore LBitvec}
  [KanonBool.Sem LBool] [CoreMod.Sem LCore] [BitvecMod.Sem LBitvec] [Sem L]
  {a a' b b' c c' : S.Term} {t t' : S.Ty}

theorem refines_bvOfFloat {rm s n} (ha : S.Refines a a')
    (ht : S.WT (B.node (L.BvOfFloatK rm s n a) t) → t' = t) :
    S.Refines (B.node (L.BvOfFloatK rm s n a) t) (B.node (L.BvOfFloatK rm s n a') t') :=
  refines_node1 (L.WT_BvOfFloat rm s n) (fun _ _ _ h q => by simp only [h]; exact q) fUn_none (fun ρ a t => Sem.ev_BvOfFloat ρ rm s n a t) ha ht

theorem refines_floatOfBv {rm s p} (ha : S.Refines a a')
    (ht : S.WT (B.node (L.FloatOfBvK rm s p a) t) → t' = t) :
    S.Refines (B.node (L.FloatOfBvK rm s p a) t) (B.node (L.FloatOfBvK rm s p a') t') :=
  refines_node1 (L.WT_FloatOfBv rm s p) (fun _ _ _ h q => by simp only [h]; exact q) bvUn_none (fun ρ a t => Sem.ev_FloatOfBv ρ rm s p a t) ha ht

theorem refines_floatOfBvRaw {p} (ha : S.Refines a a')
    (ht : S.WT (B.node (L.FloatOfBvRawK p a) t) → t' = t) :
    S.Refines (B.node (L.FloatOfBvRawK p a) t) (B.node (L.FloatOfBvRawK p a') t') :=
  refines_node1 (L.WT_FloatOfBvRaw p) (fun _ _ _ h q => by simp only [h]; exact q) bvUn_none (fun ρ a t => Sem.ev_FloatOfBvRaw ρ p a t) ha ht

theorem refines_floatOfFloat {rm p} (ha : S.Refines a a')
    (ht : S.WT (B.node (L.FloatOfFloatK rm p a) t) → t' = t) :
    S.Refines (B.node (L.FloatOfFloatK rm p a) t) (B.node (L.FloatOfFloatK rm p a') t') :=
  refines_node1 (L.WT_FloatOfFloat rm p) (fun _ _ _ h q => by simp only [h]; exact q) fUn_none (fun ρ a t => Sem.ev_FloatOfFloat ρ rm p a t) ha ht

theorem refines_fAbs (ha : S.Refines a a')
    (ht : S.WT (B.node (L.FAbsK a) t) → t' = t) :
    S.Refines (B.node (L.FAbsK a) t) (B.node (L.FAbsK a') t') :=
  refines_node1 (L.WT_FAbs) (fun _ _ _ h q => by simp only [h]; exact q) fUn_none Sem.ev_FAbs ha ht

theorem refines_fNeg (ha : S.Refines a a')
    (ht : S.WT (B.node (L.FNegK a) t) → t' = t) :
    S.Refines (B.node (L.FNegK a) t) (B.node (L.FNegK a') t') :=
  refines_node1 (L.WT_FNeg) (fun _ _ _ h q => by simp only [h]; exact q) fUn_none Sem.ev_FNeg ha ht

theorem refines_fSqrt (ha : S.Refines a a')
    (ht : S.WT (B.node (L.FSqrtK a) t) → t' = t) :
    S.Refines (B.node (L.FSqrtK a) t) (B.node (L.FSqrtK a') t') :=
  refines_node1 (L.WT_FSqrt) (fun _ _ _ h q => by simp only [h]; exact q) fUn_none Sem.ev_FSqrt ha ht

theorem refines_fRound {rm} (ha : S.Refines a a')
    (ht : S.WT (B.node (L.FRoundK rm a) t) → t' = t) :
    S.Refines (B.node (L.FRoundK rm a) t) (B.node (L.FRoundK rm a') t') :=
  refines_node1 (L.WT_FRound rm) (fun _ _ _ h q => by simp only [h]; exact q) fUn_none (fun ρ a t => Sem.ev_FRound ρ rm a t) ha ht

theorem refines_fIs {fc} (ha : S.Refines a a')
    (ht : S.WT (B.node (L.FIsK fc a) t) → t' = t) :
    S.Refines (B.node (L.FIsK fc a) t) (B.node (L.FIsK fc a') t') :=
  refines_node1 (L.WT_FIs fc) (fun _ _ _ h q => by simp only [h]; exact q) fUn_none (fun ρ a t => Sem.ev_FIs ρ fc a t) ha ht

theorem refines_fIsNeg (ha : S.Refines a a')
    (ht : S.WT (B.node (L.FIsNegK a) t) → t' = t) :
    S.Refines (B.node (L.FIsNegK a) t) (B.node (L.FIsNegK a') t') :=
  refines_node1 (L.WT_FIsNeg) (fun _ _ _ h q => by simp only [h]; exact q) fUn_none Sem.ev_FIsNeg ha ht

theorem refines_fIsPos (ha : S.Refines a a')
    (ht : S.WT (B.node (L.FIsPosK a) t) → t' = t) :
    S.Refines (B.node (L.FIsPosK a) t) (B.node (L.FIsPosK a') t') :=
  refines_node1 (L.WT_FIsPos) (fun _ _ _ h q => by simp only [h]; exact q) fUn_none Sem.ev_FIsPos ha ht

theorem refines_fEq (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.FEqK a b) t) → t' = t) :
    S.Refines (B.node (L.FEqK a b) t) (B.node (L.FEqK a' b') t') :=
  refines_node2 L.WT_FEq (fun _ _ _ _ _ h h' q => by simp only [h, h']; exact q)
    (fun _ => fBin_none_l _) (fun _ => fBin_none_r _) Sem.ev_FEq ha hb ht

theorem refines_fLeq (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.FLeqK a b) t) → t' = t) :
    S.Refines (B.node (L.FLeqK a b) t) (B.node (L.FLeqK a' b') t') :=
  refines_node2 L.WT_FLeq (fun _ _ _ _ _ h h' q => by simp only [h, h']; exact q)
    (fun _ => fBin_none_l _) (fun _ => fBin_none_r _) Sem.ev_FLeq ha hb ht

theorem refines_fLt (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.FLtK a b) t) → t' = t) :
    S.Refines (B.node (L.FLtK a b) t) (B.node (L.FLtK a' b') t') :=
  refines_node2 L.WT_FLt (fun _ _ _ _ _ h h' q => by simp only [h, h']; exact q)
    (fun _ => fBin_none_l _) (fun _ => fBin_none_r _) Sem.ev_FLt ha hb ht

theorem refines_fAdd (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.FAddK a b) t) → t' = t) :
    S.Refines (B.node (L.FAddK a b) t) (B.node (L.FAddK a' b') t') :=
  refines_node2 L.WT_FAdd (fun _ _ _ _ _ h h' q => by simp only [h, h']; exact q)
    (fun _ => fBin_none_l _) (fun _ => fBin_none_r _) Sem.ev_FAdd ha hb ht

theorem refines_fSub (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.FSubK a b) t) → t' = t) :
    S.Refines (B.node (L.FSubK a b) t) (B.node (L.FSubK a' b') t') :=
  refines_node2 L.WT_FSub (fun _ _ _ _ _ h h' q => by simp only [h, h']; exact q)
    (fun _ => fBin_none_l _) (fun _ => fBin_none_r _) Sem.ev_FSub ha hb ht

theorem refines_fMul (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.FMulK a b) t) → t' = t) :
    S.Refines (B.node (L.FMulK a b) t) (B.node (L.FMulK a' b') t') :=
  refines_node2 L.WT_FMul (fun _ _ _ _ _ h h' q => by simp only [h, h']; exact q)
    (fun _ => fBin_none_l _) (fun _ => fBin_none_r _) Sem.ev_FMul ha hb ht

theorem refines_fDiv (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.FDivK a b) t) → t' = t) :
    S.Refines (B.node (L.FDivK a b) t) (B.node (L.FDivK a' b') t') :=
  refines_node2 L.WT_FDiv (fun _ _ _ _ _ h h' q => by simp only [h, h']; exact q)
    (fun _ => fBin_none_l _) (fun _ => fBin_none_r _) Sem.ev_FDiv ha hb ht

theorem refines_fRem (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.FRemK a b) t) → t' = t) :
    S.Refines (B.node (L.FRemK a b) t) (B.node (L.FRemK a' b') t') :=
  refines_node2 L.WT_FRem (fun _ _ _ _ _ h h' q => by simp only [h, h']; exact q)
    (fun _ => fBin_none_l _) (fun _ => fBin_none_r _) Sem.ev_FRem ha hb ht

theorem refines_fMin (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.FMinK a b) t) → t' = t) :
    S.Refines (B.node (L.FMinK a b) t) (B.node (L.FMinK a' b') t') :=
  refines_node2 L.WT_FMin (fun _ _ _ _ _ h h' q => by simp only [h, h']; exact q)
    (fun _ => fBin_none_l _) (fun _ => fBin_none_r _) Sem.ev_FMin ha hb ht

theorem refines_fMax (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.FMaxK a b) t) → t' = t) :
    S.Refines (B.node (L.FMaxK a b) t) (B.node (L.FMaxK a' b') t') :=
  refines_node2 L.WT_FMax (fun _ _ _ _ _ h h' q => by simp only [h, h']; exact q)
    (fun _ => fBin_none_l _) (fun _ => fBin_none_r _) Sem.ev_FMax ha hb ht

theorem refines_fma (ha : S.Refines a a') (hb : S.Refines b b') (hc : S.Refines c c')
    (ht : S.WT (B.node (L.FmaK a b c) t) → t' = t) :
    S.Refines (B.node (L.FmaK a b c) t) (B.node (L.FmaK a' b' c') t') :=
  refines_node3 L.WT_Fma (fun _ _ _ _ _ _ _ h h' h'' q => by simp only [h, h', h'']; exact q)
    (fun _ _ => fTern_none_l) (fun _ _ => fTern_none_m) (fun _ _ => fTern_none_r) Sem.ev_Fma
    ha hb hc ht

attribute [kanon_congr_lemma] refines_bvOfFloat refines_floatOfBv refines_floatOfBvRaw refines_floatOfFloat refines_fAbs refines_fNeg refines_fSqrt refines_fRound refines_fIs refines_fIsNeg refines_fIsPos refines_fEq refines_fLeq refines_fLt refines_fAdd refines_fSub refines_fMul refines_fDiv refines_fRem refines_fMin refines_fMax refines_fma

end Lib

/-- The side goals of the congruence lemmas of the float module. -/
macro_rules | `(tactic| kanon_congr_side) => `(tactic|
  (intro w
   simp only [Syntax.WT_BvOfFloat, Syntax.WT_FloatOfBv, Syntax.WT_FloatOfBvRaw, Syntax.WT_FloatOfFloat, Syntax.WT_FAbs, Syntax.WT_FNeg, Syntax.WT_FSqrt, Syntax.WT_FRound, Syntax.WT_FIs, Syntax.WT_FIsNeg, Syntax.WT_FIsPos, Syntax.WT_FEq, Syntax.WT_FLeq, Syntax.WT_FLt, Syntax.WT_FAdd, Syntax.WT_FSub, Syntax.WT_FMul, Syntax.WT_FDiv, Syntax.WT_FRem, Syntax.WT_FMin, Syntax.WT_FMax, Syntax.WT_Fma] at w
   kanon_split
   first
     | exact Kanon.Sem.ty_refines (by assumption) (by assumption)
     | (congr 1; rw [Kanon.Sem.ty_refines (by assumption) (by assumption)])))

end FloatMod
