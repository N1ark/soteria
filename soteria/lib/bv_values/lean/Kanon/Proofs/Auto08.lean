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

@[kanon_arm] theorem Bitvec.sub.r_zero_l.main.proof : Bitvec.sub.r_zero_l.main.Stmt := kanon_proof% Bitvec.sub.r_zero_l.main

@[kanon_arm] theorem Bitvec.sub.r_same.main.proof : Bitvec.sub.r_same.main.Stmt := kanon_proof% Bitvec.sub.r_same.main

@[kanon_arm] theorem Bitvec.sub.r_neg_r.main.proof : Bitvec.sub.r_neg_r.main.Stmt := kanon_proof% Bitvec.sub.r_neg_r.main

@[kanon_arm] theorem Bitvec.sub.r_sub_const_l.main.proof : Bitvec.sub.r_sub_const_l.main.Stmt := kanon_proof% Bitvec.sub.r_sub_const_l.main

@[kanon_arm] theorem Bitvec.sub.r_sub_const_r.main.proof : Bitvec.sub.r_sub_const_r.main.Stmt := kanon_proof% Bitvec.sub.r_sub_const_r.main

@[kanon_arm] theorem Bitvec.sub.r_const_add.main.proof : Bitvec.sub.r_const_add.main.Stmt := kanon_proof% Bitvec.sub.r_const_add.main

@[kanon_arm] theorem Bitvec.sub.r_add_const.main.proof : Bitvec.sub.r_add_const.main.Stmt := kanon_proof% Bitvec.sub.r_add_const.main

@[kanon_arm] theorem Bitvec.sub.r_add_cancel_l.main.proof : Bitvec.sub.r_add_cancel_l.main.Stmt := kanon_proof% Bitvec.sub.r_add_cancel_l.main

@[kanon_arm] theorem Bitvec.sub.r_add_cancel_r.main.proof : Bitvec.sub.r_add_cancel_r.main.Stmt := kanon_proof% Bitvec.sub.r_add_cancel_r.main

@[kanon_arm] theorem Bitvec.sub.r_add_add.main.proof : Bitvec.sub.r_add_add.main.Stmt := kanon_proof% Bitvec.sub.r_add_add.main
