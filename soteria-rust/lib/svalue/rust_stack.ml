(* The generic host stack over the Rust language: the composition of the
   generated rules, the view and the host items ([Rust_lang]) into a
   [Kanon_fns], and of the generic layers over it. The analogue of New_stack of
   the C language. The ONE place that chooses the implementation of
   [Kanon_fns]. *)

module Types = Rust_types

module K :
  Iface.Kanon_fns.Kanon_fns with type t = Types.t and type ty = Types.ty =
  Rust_lang

module L = Iface.Lang_make.Make (Types) (K)
module Lang = L.V
