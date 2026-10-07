(** The composition of the generic layers over a generated language: the glue
    that each language ([Lang] for C, a Rust module for soteria-rust) applies.

    {v
      module L = Lang_make.Make (Types) (K)
      module Lang = L.V                          (* Analyses, Bv_solver, ... *)
    v}

    Creation order (design 3.6.1): the constants of the language ([K.v_true],
    [K.v_false], the zeros and ones) are created when its prims module is
    initialised, before anything of this functor. *)

module type S = sig
  module V : Value_lang.S
  module Svalue : Svalue_sugar.S with type t = V.t and type ty = V.ty
  module Eval : Eval.S with type t = V.t and type ty = V.ty
  module Expr : Expr.S with type value = V.t and type vty = V.ty
end

module Make
    (T : Value_lang.Term)
    (K : Kanon_fns.Kanon_fns with type t = T.t and type ty = T.ty) :
  S with type V.t = T.t and type V.ty = T.ty = struct
  module Base = Value_lang.Make (T) (K)
  module Eval = Eval.Make (Base)

  module V : Value_lang.S with type t = T.t and type ty = T.ty = struct
    include Base

    let eval = Eval.eval
  end

  module Svalue = Svalue_sugar.Make (V)
  module Expr = Expr.Make (V)
end
