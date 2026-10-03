(* The modules of Soteria that the interfaces mention, under one name each.
   After the move into soteria/lib/bv_values, replace this file by aliases to
   the sibling modules ([Svalue_base] = [Svalue_ast], ...). *)

module Solver_lang = Soteria.Bv_values.Solver_lang
module Svalue_base = Soteria.Bv_values.Svalue
module Symex = Soteria.Symex
module Smt = Soteria.Smt
module Var = Soteria.Symex.Var
module F = Floatml.AnyFloat
