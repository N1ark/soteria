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

@[kanon_arm] theorem Bitvec.extract.r_zext_high.main.proof : Bitvec.extract.r_zext_high.main.Stmt := kanon_proof% Bitvec.extract.r_zext_high.main

@[kanon_arm] theorem Bitvec.extract.r_sext_bit.main.proof : Bitvec.extract.r_sext_bit.main.Stmt := kanon_proof% Bitvec.extract.r_sext_bit.main

@[kanon_arm] theorem Bitvec.extract.r_ext_low.main.proof : Bitvec.extract.r_ext_low.main.Stmt := kanon_proof% Bitvec.extract.r_ext_low.main

@[kanon_arm] theorem Bitvec.extract.r_ext_orig.main.proof : Bitvec.extract.r_ext_orig.main.Stmt := kanon_proof% Bitvec.extract.r_ext_orig.main

@[kanon_arm] theorem Bitvec.extract.r_extract.main.proof : Bitvec.extract.r_extract.main.Stmt := kanon_proof% Bitvec.extract.r_extract.main

@[kanon_arm] theorem Bitvec.extract.r_concat.main.proof : Bitvec.extract.r_concat.main.Stmt := kanon_proof% Bitvec.extract.r_concat.main

@[kanon_arm] theorem Bitvec.extract.r_add_low.main.proof : Bitvec.extract.r_add_low.main.Stmt := kanon_proof% Bitvec.extract.r_add_low.main

@[kanon_arm] theorem Bitvec.extract.r_add_const.main.proof : Bitvec.extract.r_add_const.main.Stmt := kanon_proof% Bitvec.extract.r_add_const.main

@[kanon_arm] theorem Bitvec.extract.r_mul_pow2.main.proof : Bitvec.extract.r_mul_pow2.main.Stmt := kanon_proof% Bitvec.extract.r_mul_pow2.main

@[kanon_arm] theorem Bitvec.extract.r_mul_low.main.proof : Bitvec.extract.r_mul_low.main.Stmt := kanon_proof% Bitvec.extract.r_mul_low.main
