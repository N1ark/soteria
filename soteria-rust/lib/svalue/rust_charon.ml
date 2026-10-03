(* The part of the language that reads Charon and the crate being analysed: the
   sorts of the types of Rust and the size of a pointer. Ported from
   soteria-rust/lib/svalue/ext_base.ml ([float_precision], [ty_of_rust],
   [usize_bits]); the sorts are those of the rust module, [TExtension X] being
   [X]. *)

open Charon
open Common.Charon_util
module L = L
module Crate = Crate
module R = Rust_types

let float_precision :
    Values.float_type -> Soteria.Bv_values.Svalue.FloatPrecision.t = function
  | F16 -> F16
  | F32 -> F32
  | F64 -> F64
  | F128 -> F128

let rec ty_of_rust : Types.ty -> R.ty = function
  | TLiteral (TFloat ft) -> R.TFloat (float_precision ft)
  | TLiteral lit -> R.TBitVector (8 * size_of_literal_ty lit)
  | TRef _ | TRawPtr _ | TFnPtr _ -> R.TFullPtr
  | TNever | TFnDef _ -> R.TTuple []
  | TVar _ -> R.TPolyType
  | TPattern (ty, _) -> ty_of_rust ty
  | TArray (ty, n) -> R.TArray (ty_of_rust ty, z_of_constant_expr n)
  | TAdt adt -> (
      assert (tyref_is_substituted adt);
      match (Crate.get_adt adt).kind with
      | Struct fs ->
          R.TTuple
            (List.map (fun (f : Types.field) -> ty_of_rust f.field_ty) fs)
      | Enum _ -> R.TEnum adt
      | Union _ -> R.TUnion adt
      | kind ->
          L.failwith "ty_of_rust unexpected adt kind %a" Types.pp_type_decl_kind
            kind)
  | (TError _ | TPtrMetadata _ | TTraitType _ | TDynTrait _ | TSlice _) as ty ->
      L.failwith "ty_of_rust unexpected type %a" pp_ty ty

let usize_bits () = 8 * size_of_uint_ty Usize

(* {2 The components of a sort}

   They fail on other sorts, with the exception and the message of
   ext_base.ml *)

let t_as_tuple (ty : R.ty) =
  match ty with
  | TTuple tys -> tys
  | _ -> invalid_arg "t_as_tuple: not a tuple type"

let t_as_array (ty : R.ty) =
  match ty with
  | TArray (elem_ty, n) -> (elem_ty, n)
  | _ -> invalid_arg "t_as_array: not an array type"

let array_length (ty : R.ty) =
  match ty with
  | TArray (_, n) -> n
  | _ -> invalid_arg "array_length: not an array type"

let array_elem_ty (ty : R.ty) =
  match ty with
  | TArray (elem_ty, _) -> elem_ty
  | _ -> invalid_arg "array_elem_ty: not an array type"

let t_as_enum (ty : R.ty) =
  match ty with
  | TEnum adt -> adt
  | _ -> invalid_arg "t_as_enum: not an enum type"

let t_as_union (ty : R.ty) =
  match ty with
  | TUnion adt -> adt
  | _ -> invalid_arg "t_as_union: not a union type"
