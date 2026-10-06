import FloatMod.Lib.Rule
import FloatMod.Statements.Float.to_float_bits

/-! The arms of `Float.to_float_bits` that the default tactic does not prove. -/

namespace FloatMod

open Classical Kanon Kanon.Sem CoreMod Lib

@[kanon_arm] theorem Float.to_float_bits.r_lit.main.proof : Float.to_float_bits.r_lit.main.Stmt := by
  intro S _ _ B LBool LCore LBitvec L _ _ _ _ O hO fp z t
  simp only [kanon_spec]
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;>
    obtain ⟨⟨h1, h2⟩, wl⟩ := (L.WT_FloatOfBvRaw _ _ _).1 w <;>
    obtain ⟨⟨m, hm, rfl⟩, hwf⟩ := (LBitvec.WT_BitVec _ _).1 wl <;>
    rw [BitvecMod.Sem.bv_wf_BitVec, BitvecMod.Sem.size_of_ty_TBitVector] at hwf <;>
    rw [B.ty_node, BitvecMod.Lib.TBitVector_inj_iff, Sem.fp_size_eq, Prim.fp_size] at h1 <;> subst h1
  · refine ⟨lit_WT ?_, by rw [lit_ty, B.ty_node, h2, Sem.f_of_bits_eq]; rfl⟩
    rw [Sem.f_of_bits_eq]
    show (z % 2 ^ fp.size).toNat < 2 ^ fp.size
    have : z % 2 ^ fp.size < 2 ^ fp.size := Int.emod_lt_of_pos _ (Int.pow_pos (by decide))
    have : 0 ≤ z % 2 ^ fp.size := Int.emod_nonneg _ (Int.ne_of_gt (Int.pow_pos (by decide)))
    have e : ((2 ^ fp.size : Nat) : Int) = 2 ^ fp.size := by push_cast; rfl
    omega
  · rw [Sem.ev_FloatOfBvRaw, BitvecMod.Sem.ev_BitVec, BitvecMod.Sem.size_of_ty_TBitVector,
      Int.toNat_natCast, bvUn_some, dif_pos rfl] at e
    rw [Sem.ev_Float, ← e, Sem.f_of_bits_eq]
    congr 2
    simp only [Prim.f_of_bits, CoreMod.Float.val]
    apply BitVec.eq_of_toNat_eq
    have : 0 ≤ z % 2 ^ fp.size := Int.emod_nonneg _ (Int.ne_of_gt (Int.pow_pos (by decide)))
    have e : ((2 ^ fp.size : Nat) : Int) = 2 ^ fp.size := by push_cast; rfl
    rw [BitVec.toNat_cast, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    have h3 : z % 2 ^ fp.size < 2 ^ fp.size := Int.emod_lt_of_pos _ (Int.pow_pos (by decide))
    rw [Nat.mod_eq_of_lt (by omega)]
    rw [e]

end FloatMod
