import FloatMod.Lib.Rule
import FloatMod.Statements.Float.to_float

/-! The arms of `Float.to_float` that the default tactic does not prove. -/

namespace FloatMod

open Classical Kanon Kanon.Sem CoreMod Lib

@[kanon_arm] theorem Float.to_float.r_lit.main.proof : Float.to_float.r_lit.main.Stmt := by
  intro S _ _ B LBool LCore LBitvec L _ _ _ _ O hO rm sg fp z t
  cases h : O.float_f_of_int rm sg fp (LBitvec.bitvec_size (B.node (LBitvec.BitVecK z) t)) z with
  | none =>
    simp only [h, Kanon.firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse,
      Option.getD_some, kanon_spec]
    exact Refines.refl
  | some g =>
    simp only [h, Kanon.firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse,
      Option.getD_some, kanon_spec]
    rw [LBitvec.bitvec_size_eq, B.ty_node] at h
    refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;>
      obtain ⟨⟨⟨m, hm, ht2⟩, ht⟩, wl⟩ := (L.WT_FloatOfBv _ _ _ _ _).1 w <;>
      rw [B.ty_node] at ht2 <;> subst ht2 <;>
      obtain ⟨-, hwf⟩ := (LBitvec.WT_BitVec _ _).1 wl <;>
      rw [BitvecMod.Sem.bv_wf_BitVec, BitvecMod.Sem.size_of_ty_TBitVector] at hwf <;>
      rw [BitvecMod.Sem.size_of_ty_TBitVector] at h <;>
      obtain ⟨hp, hg, hv⟩ := hO.float_orc.of_int rm sg fp m z g hm hwf.1 hwf.2 h
    · exact ⟨lit_WT hg, by rw [lit_ty, B.ty_node, ht, hp]⟩
    · rw [Sem.ev_FloatOfBv, BitvecMod.Sem.ev_BitVec, BitvecMod.Sem.size_of_ty_TBitVector,
        bvUn_some] at e
      rw [Sem.ev_Float, ← e, hv]

end FloatMod
