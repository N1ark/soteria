(* The stack of the Rust language: its types ([Types], generated), the
   primitives of its rules ([Prims]), its rules ([Rules], generated), and here
   the constructors and the printing that Kanon cannot express (the analogue of
   [Bv_values.Lang] for the C language), composed as a [Kanon_fns]. *)

module Types = Rust_types
module Prims = Rust_prims
module Rules = Rust_rules
open Rust_types

type t = Types.t
type ty = Types.ty
type pphead = Iface.View_host.pphead
type smt_op = (t, ty) Iface.View_host.smt_op
type smt_sort_op = ty Iface.View_host.smt_sort_op

(* The shared and the rust smart constructors, and the view *)
include Rules

(* {1 Host items of [Kanon_fns]} *)

let v_true = Prims.v_true
let v_false = Prims.v_false
let mk_var v ty = node (Var v) ty
let mk_bv n z = Prims.mk_bv_int n z
let mk_masked n z = Prims.mk_masked_int n z
let bv_zero n = Prims.bv_zero_int n
let bv_one n = Prims.bv_one_int n
let mk_float f = node (Float f) (TFloat (Floatml.AnyFloat.precision f))
let mk_loc n z = node (LocLit z) (TLoc n)
let mk_ptr = Prims.mk_ptr
let mk_seq = Prims.mk_seq
let pp_ty = Prims.pp_ty
