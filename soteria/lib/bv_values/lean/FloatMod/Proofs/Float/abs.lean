import FloatMod.Lib.Rule
import FloatMod.Statements.Float.abs

/-! The arms of `Float.abs` that the default tactic does not prove. -/

namespace FloatMod

open Classical Kanon Kanon.Sem CoreMod Lib

@[kanon_arm] theorem Float.abs.r_lit.main.proof : Float.abs.r_lit.main.Stmt := by
  intro S _ _ B LBool LCore LBitvec L _ _ _ _ O hO f t
  simp only [kanon_spec]
  refine Refines.un_lit (fun a t w => ((L.WT_FAbs a t).1 w).2) Sem.ev_FAbs (fun w ht1 hf => ?_)
    (fun hf ρ => ?_)
  · rw [L.WT_FAbs] at w
    refine ⟨lit_WT (by rw [Sem.f_abs_eq]; exact BitVec.isLt _), ?_⟩
    rw [lit_ty, w.1.2, B.ty_node, ht1, Sem.f_abs_eq]; rfl
  · rw [Sem.ev_Float, Sem.f_abs_eq]; simp [Prim.f_abs, ofNat_toNat_val]

@[kanon_arm] theorem Float.abs.r_abs.main.proof : Float.abs.r_abs.main.Stmt := by
  intro S _ _ B LBool LCore LBitvec L _ _ _ _ O hO w t
  simp only [kanon_spec]
  exact Refines.un_idem L.WT_FAbs Sem.ev_FAbs (fun _ x => fbits_abs_abs x)

end FloatMod
