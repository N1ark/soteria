import FloatMod.Lib.Rule
import FloatMod.Statements.Float.of_float

/-! The arms of `Float.of_float` that the default tactic does not prove. -/

namespace FloatMod

open Classical Kanon Kanon.Sem CoreMod Lib

@[kanon_arm] theorem Float.of_float.r_lit.main.proof : Float.of_float.r_lit.main.Stmt := by
  intro S _ _ B LBool LCore LBitvec L _ _ _ _ O hO rm sg sz f t
  cases h : O.float_f_to_int rm sg sz f with
  | none =>
    simp only [h, Kanon.firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse,
      Option.getD_some, kanon_spec]
    exact Refines.refl
  | some z =>
    simp only [h, Kanon.firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse,
      Option.getD_some, kanon_spec, BitvecMod.Sem.mk_masked_eq]
    refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;>
      obtain ⟨⟨hsz, -, ht⟩, wl⟩ := (L.WT_BvOfFloat _ _ _ _ _).1 w <;>
      obtain ⟨-, hf⟩ := WT_lit.1 wl
    · refine ⟨(LBitvec.WT_BitVec _ _).2 ⟨⟨_, hsz, rfl⟩, ?_⟩, by rw [B.ty_node, B.ty_node]⟩
      rw [BitvecMod.Sem.bv_wf_BitVec, BitvecMod.Sem.size_of_ty_TBitVector]
      exact ⟨Int.emod_nonneg _ (Int.ne_of_gt (Int.pow_pos (by decide))),
        Int.emod_lt_of_pos _ (Int.pow_pos (by decide))⟩
    · rw [Sem.ev_BvOfFloat, Sem.ev_Float, fUn_some (Sem.vfloat_inj (L := L)),
        hO.float_orc.to_int rm sg sz f z hf hsz h] at e
      rw [BitvecMod.Sem.ev_BitVec, BitvecMod.Sem.size_of_ty_TBitVector, ← e]
      congr 2
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofInt]

end FloatMod
