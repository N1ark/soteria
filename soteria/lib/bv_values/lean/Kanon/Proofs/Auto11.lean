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

@[kanon_arm] theorem Bitvec.rem.r_add.main.proof : Bitvec.rem.r_add.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.rem.r_add.swap.proof : Bitvec.rem.r_add.swap.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.rem.r_rem_rem.main.proof : Bitvec.rem.r_rem_rem.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.rem.r_default.main.proof : Bitvec.rem.r_default.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.not_.r_lit.main.proof : Bitvec.not_.r_lit.main.Stmt := kanon_proof% Bitvec.not_.r_lit.main

@[kanon_arm] theorem Bitvec.not_.r_ite.main.proof : Bitvec.not_.r_ite.main.Stmt := kanon_proof% Bitvec.not_.r_ite.main

@[kanon_arm] theorem Bitvec.not_.r_default.main.proof : Bitvec.not_.r_default.main.Stmt := kanon_proof% Bitvec.not_.r_default.main

@[kanon_arm] theorem Bitvec.and_.r_lits.main.proof : Bitvec.and_.r_lits.main.Stmt := kanon_proof% Bitvec.and_.r_lits.main

@[kanon_arm] theorem Bitvec.and_.r_zero.main.proof : Bitvec.and_.r_zero.main.Stmt := kanon_proof% Bitvec.and_.r_zero.main

@[kanon_arm] theorem Bitvec.and_.r_ones.main.proof : Bitvec.and_.r_ones.main.Stmt := kanon_proof% Bitvec.and_.r_ones.main
