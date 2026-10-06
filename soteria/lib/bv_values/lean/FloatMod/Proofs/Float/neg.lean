import FloatMod.Lib.Rule
import FloatMod.Statements.Float.neg

/-! The arms of `Float.neg` that the default tactic does not prove. -/

namespace FloatMod

open Classical Kanon Kanon.Sem CoreMod Lib

@[kanon_arm] theorem Float.neg.r_lit.main.proof : Float.neg.r_lit.main.Stmt := by
  intro S _ _ B LBool LCore LBitvec L _ _ _ _ O hO f t
  simp only [kanon_spec]
  refine Refines.un_lit (fun a t w => ((L.WT_FNeg a t).1 w).2) Sem.ev_FNeg (fun w ht1 hf => ?_)
    (fun hf ρ => ?_)
  · rw [L.WT_FNeg] at w
    refine ⟨lit_WT (by rw [Sem.f_neg_eq]; exact BitVec.isLt _), ?_⟩
    rw [lit_ty, w.1.2, B.ty_node, ht1, Sem.f_neg_eq]; rfl
  · rw [Sem.ev_Float, Sem.f_neg_eq]; simp [Prim.f_neg, ofNat_toNat_val]

@[kanon_arm] theorem Float.neg.r_neg.main.proof : Float.neg.r_neg.main.Stmt := by
  intro S _ _ B LBool LCore LBitvec L _ _ _ _ O hO v t
  simp only [kanon_spec]
  exact Refines.un_invol L.WT_FNeg Sem.ev_FNeg (fun _ x => fbits_neg_neg x)

end FloatMod
