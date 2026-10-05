import Kanon.Lib.Resize
import Kanon.Statements.Bitvec.not_bool

/-! The arms of `Bitvec.not_bool` that the default tactics do not prove. -/

namespace Kanon

open Classical Lib

@[kanon_arm] theorem Bitvec.not_bool.r_lit.main.proof : Bitvec.not_bool.r_lit.main.Stmt := by
  kanon_rule_sem
  all_goals first
    | exact (‹∀ m : Int, ¬ _ = Ty.TBitVector m› _ ‹Ty.TBitVector _ = _›.symm).elim
    | (obtain ⟨h0, h1⟩ := ‹(0 : Int) ≤ _ ∧ _ < _›
       try subst_vars
       try simp only [Int.toNat_natCast] at *
       simp only [ofInt_eq_zero_iff h0 h1] at *
       simp_all)

end Kanon
