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

@[kanon_arm] theorem Bitvec.sub.r_sub_sub.main.proof : Bitvec.sub.r_sub_sub.main.Stmt := kanon_proof% Bitvec.sub.r_sub_sub.main

@[kanon_arm] theorem Bitvec.sub.r_ite_ite.main.proof : Bitvec.sub.r_ite_ite.main.Stmt := kanon_proof% Bitvec.sub.r_ite_ite.main

@[kanon_arm] theorem Bitvec.sub.r_ite_l.main.proof : Bitvec.sub.r_ite_l.main.Stmt := kanon_proof% Bitvec.sub.r_ite_l.main

@[kanon_arm] theorem Bitvec.sub.r_ite_r.main.proof : Bitvec.sub.r_ite_r.main.Stmt := kanon_proof% Bitvec.sub.r_ite_r.main

@[kanon_arm] theorem Bitvec.sub.r_of_bool_l.main.proof : Bitvec.sub.r_of_bool_l.main.Stmt := kanon_proof% Bitvec.sub.r_of_bool_l.main

@[kanon_arm] theorem Bitvec.sub.r_of_bool_r.main.proof : Bitvec.sub.r_of_bool_r.main.Stmt := kanon_proof% Bitvec.sub.r_of_bool_r.main

@[kanon_arm] theorem Bitvec.sub.r_default.main.proof : Bitvec.sub.r_default.main.Stmt := kanon_proof% Bitvec.sub.r_default.main

@[kanon_arm] theorem Bitvec.neg.r_lit.main.proof : Bitvec.neg.r_lit.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.neg.r_neg.main.proof : Bitvec.neg.r_neg.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.neg.r_ite.main.proof : Bitvec.neg.r_ite.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto
