(* The primitives of the rules of the language (rules/*.kn), checked against
   their declarations by the generated rules: the shared ones (base_prims.ml and
   base_view_prims.ml, a copy of the primitives of the C language over these
   types, with the patches marked PATCH) and those of the rust module
   (rules/rust.kn), which read the crate, raise the exceptions of the old code,
   and give the heads of the SMT encoding. *)

include Base_prims
open Rust_types
module Types = Charon.Types

(* {1 Reading the crate} *)

let ty_of_rust = Rust_charon.ty_of_rust
let usize_bits () = Z.of_int (Rust_charon.usize_bits ())

let variant_of (adt : decl_ref) (var : variant_id) : Types.variant =
  Types.VariantId.nth (Crate.as_enum adt) var

(* [ext_base.ml:field_of_variant]: the sort of the field [idx] of the variant
   [var], read in the declaration of the enum *)
let variant_field_ty (adt : decl_ref) (var : variant_id) (idx : Z.t) : ty =
  let variant = variant_of adt var in
  let field : Types.field = List.nth variant.fields (Z.to_int idx) in
  ty_of_rust field.field_ty

let variant_arity (adt : decl_ref) (var : variant_id) : Z.t =
  Z.of_int (List.length (variant_of adt var).fields)

(* {1 The failures of the old code} *)

let fail_tuple_ty (s : ty) : ty list = Rust_charon.t_as_tuple s
let fail_array_len (s : ty) : Z.t = Rust_charon.array_length s
let fail_array_elem (s : ty) : ty = Rust_charon.array_elem_ty s
let fail_enum_ty (s : ty) : decl_ref = Rust_charon.t_as_enum s
let fail_union_ty (s : ty) : decl_ref = Rust_charon.t_as_union s

let fail_meta (part : meta_part) (m : ptr_meta) : t =
  let pp_part ft = function
    | PartLen -> Fmt.string ft "len"
    | PartVTable -> Fmt.string ft "vtable"
  in
  let pp_kind ft = function
    | MetaUnit -> Fmt.string ft "unit"
    | MetaLen _ -> Fmt.string ft "len"
    | MetaVTable _ -> Fmt.string ft "vtable"
  in
  L.failwith "ptr_meta_as: expected %a but got %a" pp_part part pp_kind m

(* {1 Lists} *)

let nth_term (l : t list) (i : Z.t) : t = List.nth l (Z.to_int i)
let nth_ty (l : ty list) (i : Z.t) : ty = List.nth l (Z.to_int i)

let set_nth (l : t list) (i : Z.t) (x : t) : t list =
  Soteria.Soteria_std.List.set_nth (Z.to_int i) x l

(* [Iarray.get] and [Iarray.copy_and_set] of the arrays: out of range is
   [Invalid_argument "index out of bounds"] *)
module Iarray = Soteria.Soteria_std.Iarray

let iarray_get (a : t Iarray.t) (i : Z.t) : t =
  let i = Z.to_int i in
  if i < 0 || i >= Iarray.length a then invalid_arg "index out of bounds"
  else Iarray.get a i

let iarray_set (a : t Iarray.t) (i : Z.t) (x : t) : t Iarray.t =
  let i = Z.to_int i in
  if i < 0 || i >= Iarray.length a then invalid_arg "index out of bounds"
  else Iarray.copy_and_set i x a

let iarray_length (a : t Iarray.t) : Z.t = Z.of_int (Iarray.length a)
let iarray_to_list (a : t Iarray.t) : t list = Iarray.to_list a
let iarray_of_list (l : t list) : t Iarray.t = Iarray.of_list l
let list_length (l : t list) : Z.t = Z.of_int (List.length l)

(* [ext_base.ml:field_of_variant] on an enum: the variant is the one asked *)
let enum_field (cur : variant_id) (var : variant_id) (vs : t list) (idx : Z.t) :
    t =
  assert (Types.equal_variant_id cur var);
  List.nth vs (Z.to_int idx)

let enum_fields (cur : variant_id) (var : variant_id) (vs : t list) : t list =
  assert (Types.equal_variant_id cur var);
  vs

let bad_blocks (_ : t) : block list =
  L.failwith "rebuild: wrong number of operands"

(* {1 SMT} *)

let so_tuple = Rust_encoding.so_tuple
let so_enum = Rust_encoding.so_enum
let so_thin_ptr = Rust_encoding.so_thin_ptr
let so_full_ptr = Rust_encoding.so_full_ptr
let so_ptr_meta = Rust_encoding.so_ptr_meta
let so_union = Rust_encoding.so_union
let so_poly = Rust_encoding.so_poly
let h_thin_ptr = Rust_encoding.h_thin_ptr
let h_full_ptr = Rust_encoding.h_full_ptr
let h_meta_none = Rust_encoding.h_meta_none
let h_meta_int = Rust_encoding.h_meta_int
let h_meta_ptr = Rust_encoding.h_meta_ptr
let h_enum = Rust_encoding.h_enum
let h_tuple = Rust_encoding.h_tuple
let h_array = Rust_encoding.h_array
let h_union = Rust_encoding.h_union
let h_poly = Rust_encoding.h_poly
let h_thin_part = Rust_encoding.h_thin_part
let h_full_inner = Rust_encoding.h_full_inner
let h_full_meta = Rust_encoding.h_full_meta
let h_meta_as = Rust_encoding.h_meta_as
let h_field = Rust_encoding.h_field
let h_variant_field = Rust_encoding.h_variant_field
let h_is_variant = Rust_encoding.h_is_variant
let h_array_field = Rust_encoding.h_array_field
