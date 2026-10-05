import BitvecMod.Lifts
import BitvecMod.Statements.Bitvec.rem

/-! The arm of `Bitvec.rem` that `bveq_rule` does not prove. -/

namespace BitvecMod

open Lib.BvEq

/-- The unsigned remainder by a power of two keeps the low bits. -/
@[kanon_arm] theorem Bitvec.rem.r_pow2.main.proof : Bitvec.rem.r_pow2.main.Stmt := by
  bveq_rule_lift
  all_goals bveq_on_refines bv_apply_den
  case hm.refine_2 =>
    intro w; bveq_facts; bv_nat_widths
    simp only [Int.toNat_natCast] at *
    obtain ⟨j, rfl, hl, hj1, hjw⟩ := pow2_facts ‹_› ‹_› ‹_›
    simp only [hl]
    refine ⟨⟨⟨_, ?_, rfl, ?_, rfl⟩, ⟨_, rfl, ?_, ?_, ?_⟩, ‹_›⟩, ?_⟩ <;> omega
  case hm.refine_3 =>
    bveq_sem_core
    all_goals subst e; exact rem_pow2_bv _ _ ‹_› ‹_› rfl

end BitvecMod
