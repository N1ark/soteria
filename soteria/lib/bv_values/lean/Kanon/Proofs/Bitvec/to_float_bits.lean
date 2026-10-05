import Kanon.Lib.Resize
import Kanon.Statements.Bitvec.to_float_bits

/-! The arms of `Bitvec.to_float_bits` that the default tactics do not prove. -/

namespace Kanon

open Classical Lib

@[kanon_arm] theorem Bitvec.to_float_bits.r_lit.main.proof : Bitvec.to_float_bits.r_lit.main.Stmt := by
  intro FS O hO p z T
  simp only [Bitvec.to_float_bits.spec, Term.ty_mk]
  refine Sem.Refines.intro_eval (fun w => ?_) (fun ρ v w w' e => ?_)
  all_goals have ⟨w1, w2⟩ := WT_op1.1 w
  all_goals simp only [Op1.WT, Term.ty_mk, fp_size] at w1
  all_goals have := emod_two_pow_lt z p.size
  all_goals have := emod_two_pow_nonneg z p.size
  all_goals have e1 : ((2 ^ p.size : Nat) : Int) = (2 : Int) ^ p.size := by push_cast; rfl
  · refine ⟨⟨rfl, ?_⟩, rfl⟩
    simp only [f_of_bits]; omega
  · rw [← eval] at e ⊢
    rw [eval_op1 w, eval_bitVec' w2 w1.1] at e
    simp [evOp1] at e
    rw [eval_eq_ev w']; simp only [ev]; rw [← e]
    simp [Float.sem, Float.val, f_of_bits]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofInt, Nat.mod_eq_of_lt (by omega)]; simp

end Kanon
