import Kanon.Proofs.CommCases
import Kanon.Proofs.ArithCases
import Kanon.Proofs.EqCases
import Kanon.Proofs.BitwiseCases
import Kanon.Proofs.ResizeCases
import Kanon.Proofs.CompareCases
import Kanon.Proofs.BoolCases
import Kanon.Lib.Rule
import Kanon.Statements

/-! The alternatives that Kanon's default tactics prove (`kanon_proof%`), a few per module so
that each is elaborated on its own (the whole of `Soundness` does not fit in memory). -/

set_option maxHeartbeats 4000000

noncomputable section

namespace Kanon

open Classical Kanon

@[kanon_arm] theorem Bitvec.leq.r_ub_r.main.proof : Bitvec.leq.r_ub_r.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.leq.r_ub_l.main.proof : Bitvec.leq.r_ub_l.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.leq.r_to_unsigned_l.main.proof : Bitvec.leq.r_to_unsigned_l.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.leq.r_to_unsigned_r.main.proof : Bitvec.leq.r_to_unsigned_r.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.leq.r_default.main.proof : Bitvec.leq.r_default.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.add_overflows.r_lits.main.proof : Bitvec.add_overflows.r_lits.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.add_overflows.r_zero.main.proof : Bitvec.add_overflows.r_zero.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.add_overflows.r_size1.main.proof : Bitvec.add_overflows.r_size1.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.add_overflows.r_unsigned.main.proof : Bitvec.add_overflows.r_unsigned.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.add_overflows.r_signed.main.proof : Bitvec.add_overflows.r_signed.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto
