open Charon

type t =
  | Heap
  | Function of Fun_kind.t
  | VTable of Types.ty [@printer Charon_util.pp_ty]
  | Static of Types.global_decl_ref [@printer Crate.pp_global_decl_ref]
  | Const of Types.global_decl_ref [@printer Crate.pp_global_decl_ref]
  | StaticString
  | AnonConst
[@@deriving show { with_path = false }]

let global_kind_is_const : GAst.global_kind -> bool = function
  | Static | ThreadLocal -> false
  | NamedConst | AnonConst -> true

let of_global_ref gref =
  if global_kind_is_const (Crate.get_global gref).global_kind then Const gref
  else Static gref
