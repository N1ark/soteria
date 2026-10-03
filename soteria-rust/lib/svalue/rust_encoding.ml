(* The SMT encoding of the sorts and the values of the rust module: the
   declarations of the datatypes (tuples, enums, thin and full pointers,
   metadata of pointers) and the operators that build and read them. Ported from
   soteria-rust/lib/svalue/encoding.ml: the [Tuple_sort] ... [Full_ptr_sort]
   modules are the same text; [encode_ty], [encode_unop] and [encode_value] are
   now the operators [so_*] (sorts) and [h_*] (values) that rules/rust.kn
   assigns to the sorts and the nodes.

   The ORDER of the calls to [encode_child], [sort_of_ty] and of the
   declarations ([gen_decl]) in each operator is that of the old functions,
   which is the order of the declarations of the SMT script: see the comments on
   the unary operators, which the old code applied to the encoding of their
   operand, and so encoded it first. *)

open Soteria.Smt
open Rust_types
module Types = Charon.Types
module L = Soteria_rust_lib.L
module Crate = Soteria_rust_lib.Crate
open Rust_charon

type smt_op = (t, ty) Iface.View_host.smt_op
type smt_sort_op = ty Iface.View_host.smt_sort_op

(** Small helper to lazily declare a sort. *)
let declare_sort ?(type_params = []) name f =
  Soteria.Solvers.Decls.declare ~key:name (fun k ->
      k (declare_datatype name type_params (f ())));
  Atom name

let pp_ptr_part ft = function
  | PtrInner -> Fmt.string ft "ptr"
  | PtrSize -> Fmt.string ft "size"
  | PtrAlign -> Fmt.string ft "align"

module Tuple_sort = struct
  let pp_args ft sorts = Fmt.(list ~sep:(any ", ") pp_sexp) ft sorts
  let name sorts = quote (Fmt.str "@tuple<%a>" pp_args sorts)
  let con sorts = quote (Fmt.str "@mk-tuple<%a>" pp_args sorts)
  let field_sel sorts i = quote (Fmt.str "@tuple<%a>.%d" pp_args sorts i)
  let mk sorts fields = con sorts $$. fields
  let get_field sorts i v = field_sel sorts i $. v

  let sort sorts =
    declare_sort (name sorts) (fun () ->
        [ (con sorts, List.mapi (fun i s -> (field_sel sorts i, s)) sorts) ])
end

module Enum_sort = struct
  let pp_base ft adt = Fmt.pf ft "@enum<%a>" Crate.pp_type_decl_ref adt
  let name adt = quote (Fmt.to_to_string pp_base adt)

  let variant_con adt (variant : Types.variant) =
    quote (Fmt.str "%a::%s" pp_base adt variant.variant_name)

  let field_sel adt (variant : Types.variant) i =
    quote (Fmt.str "%a::%s.%d" pp_base adt variant.variant_name i)

  let mk adt variant fields = variant_con adt variant $$. fields
  let get_field adt variant i v = field_sel adt variant i $. v
  let is_variant adt variant v = tester (variant_con adt variant) v

  let sort sort_of_ty (adt : Types.type_decl_ref) =
    let variants = Crate.as_enum adt in
    if List.is_empty variants then
      L.failwith "Cannot encode the empty enum %a to SMT-LIB"
        Crate.pp_type_decl_ref adt;
    declare_sort (name adt) (fun () ->
        variants
        |> List.map @@ fun (variant : Types.variant) ->
           let fields =
             variant.fields
             |> List.mapi @@ fun i (f : Types.field) ->
                (field_sel adt variant i, sort_of_ty (ty_of_rust f.field_ty))
           in
           (variant_con adt variant, fields))
end

module Thin_ptr_sort = struct
  module Ptr_sort = Soteria.Bv_values.Encoding.Ptr_sort

  let pp_base ft () = Fmt.pf ft "@thin-ptr<%d>" (usize_bits ())
  let name () = quote (Fmt.to_to_string pp_base ())
  let con () = quote (Fmt.str "@mk-thin-ptr<%d>" (usize_bits ()))
  let part_sel part = quote (Fmt.str "%a.%a" pp_base () pp_ptr_part part)
  let mk ptr size align = con () $$. [ ptr; size; align ]
  let get_part part v = part_sel part $. v

  let sort () =
    declare_sort (name ()) (fun () ->
        let bits = usize_bits () in
        [
          ( con (),
            [
              (part_sel PtrInner, Ptr_sort.sort bits);
              (part_sel PtrSize, t_bits bits);
              (part_sel PtrAlign, t_bits bits);
            ] );
        ])
end

module Ptr_meta_sort = struct
  let base () = Fmt.str "@ptr-meta<%d>" (usize_bits ())
  let name () = quote (base ())
  let none_con () = quote (base () ^ "::none")
  let int_con () = quote (base () ^ "::int")
  let ptr_con () = quote (base () ^ "::ptr")
  let int_sel () = quote (base () ^ "::int.0")
  let ptr_sel () = quote (base () ^ "::ptr.0")
  let mk_none () = none_con () $$. []
  let mk_int v = int_con () $. v
  let mk_ptr v = ptr_con () $. v
  let get_int v = int_sel () $. v
  let get_ptr v = ptr_sel () $. v

  let sort () =
    declare_sort (name ()) (fun () ->
        let thin_sort = Thin_ptr_sort.sort () in
        [
          (none_con (), []);
          (int_con (), [ (int_sel (), t_bits (usize_bits ())) ]);
          (ptr_con (), [ (ptr_sel (), thin_sort) ]);
        ])
end

module Full_ptr_sort = struct
  let base () = Fmt.str "@full-ptr<%d>" (usize_bits ())
  let name () = quote (base ())
  let con () = quote (Fmt.str "@mk-full-ptr<%d>" (usize_bits ()))
  let ptr_sel () = quote (base () ^ ".ptr")
  let meta_sel () = quote (base () ^ ".meta")
  let mk ptr meta = con () $$. [ ptr; meta ]
  let get_ptr v = ptr_sel () $. v
  let get_meta v = meta_sel () $. v

  let sort () =
    declare_sort (name ()) (fun () ->
        let thin_sort = Thin_ptr_sort.sort () in
        let meta_sort = Ptr_meta_sort.sort () in
        [ (con (), [ (ptr_sel (), thin_sort); (meta_sel (), meta_sort) ]) ])
end

(* More explicit than an [ignore] *)
let gen_decl = ignore
let wrong () = L.failwith "encode_head: wrong number of operands"

(* {1 Sorts} *)

let so_tuple : smt_sort_op =
 fun ~sort_of_ty tys -> Tuple_sort.sort (List.map sort_of_ty tys)

let so_enum adt : smt_sort_op =
 fun ~sort_of_ty _ -> Enum_sort.sort sort_of_ty adt

let so_thin_ptr : smt_sort_op = fun ~sort_of_ty:_ _ -> Thin_ptr_sort.sort ()
let so_full_ptr : smt_sort_op = fun ~sort_of_ty:_ _ -> Full_ptr_sort.sort ()
let so_ptr_meta : smt_sort_op = fun ~sort_of_ty:_ _ -> Ptr_meta_sort.sort ()

let so_union adt : smt_sort_op =
 fun ~sort_of_ty:_ _ ->
  L.failwith "Cannot encode type %a to SMT-LIB" Base_view_prims.pp_ext_ty
    (TUnion adt)

let so_poly : smt_sort_op =
 fun ~sort_of_ty:_ _ ->
  L.failwith "Cannot encode type %a to SMT-LIB" Base_view_prims.pp_ext_ty
    TPolyType

(* {1 Values}

   [ty] is the sort of the node, for the aggregates. *)

let h_tuple (ty : ty) : smt_op =
 fun ~sort_of_ty ~encode_child vs ->
  let tys = t_as_tuple ty in
  let sorts = List.map sort_of_ty tys in
  gen_decl (Tuple_sort.sort sorts);
  Tuple_sort.mk sorts (List.map encode_child vs)

let h_enum (ty : ty) (var : Types.variant_id) : smt_op =
 fun ~sort_of_ty ~encode_child vs ->
  let adt = t_as_enum ty in
  gen_decl (Enum_sort.sort sort_of_ty adt);
  let variant = Types.VariantId.nth (Crate.as_enum adt) var in
  Enum_sort.mk adt variant (List.map encode_child vs)

let h_array (ty : ty) : smt_op =
 fun ~sort_of_ty ~encode_child vs ->
  let elem_ty, len = t_as_array ty in
  if Z.equal Z.zero len then as_type seq_empty (t_seq (sort_of_ty elem_ty))
  else vs |> List.map (fun v -> seq_singl (encode_child v)) |> seq_concat

(* the old code applied [Thin_ptr_sort.mk] to the encodings: the last operand
   was encoded first *)
let h_thin_ptr : smt_op =
 fun ~sort_of_ty:_ ~encode_child -> function
  | [ ptr; size; align ] ->
      gen_decl (Thin_ptr_sort.sort ());
      Thin_ptr_sort.mk (encode_child ptr) (encode_child size)
        (encode_child align)
  | _ -> wrong ()

let h_full_ptr : smt_op =
 fun ~sort_of_ty:_ ~encode_child -> function
  | [ ptr; meta ] ->
      gen_decl (Full_ptr_sort.sort ());
      Full_ptr_sort.mk (encode_child ptr) (encode_child meta)
  | _ -> wrong ()

let h_meta_none : smt_op =
 fun ~sort_of_ty:_ ~encode_child:_ -> function
  | [] -> Ptr_meta_sort.mk_none ()
  | _ -> wrong ()

let h_meta_int : smt_op =
 fun ~sort_of_ty:_ ~encode_child -> function
  | [ v ] -> Ptr_meta_sort.mk_int (encode_child v)
  | _ -> wrong ()

let h_meta_ptr : smt_op =
 fun ~sort_of_ty:_ ~encode_child -> function
  | [ v ] -> Ptr_meta_sort.mk_ptr (encode_child v)
  | _ -> wrong ()

let h_union : smt_op =
 fun ~sort_of_ty:_ ~encode_child:_ _ ->
  L.failwith "Cannot encode union values to SMT-LIB"

let h_poly : smt_op =
 fun ~sort_of_ty:_ ~encode_child:_ _ ->
  L.failwith "Cannot encode polymorphic values to SMT-LIB"

(* {2 The nodes that read a part of a value}

   The old [encode_unop] was applied to its operand's encoding: that is encoded
   first, then the sorts are declared. [v.ty], the sort of the operand, is what
   the old code read. *)

let h_thin_part part : smt_op =
 fun ~sort_of_ty:_ ~encode_child -> function
  | [ v ] ->
      let e = encode_child v in
      gen_decl (Thin_ptr_sort.sort ());
      Thin_ptr_sort.get_part part e
  | _ -> wrong ()

let h_full_inner : smt_op =
 fun ~sort_of_ty:_ ~encode_child -> function
  | [ v ] ->
      let e = encode_child v in
      gen_decl (Full_ptr_sort.sort ());
      Full_ptr_sort.get_ptr e
  | _ -> wrong ()

let h_full_meta : smt_op =
 fun ~sort_of_ty:_ ~encode_child -> function
  | [ v ] ->
      let e = encode_child v in
      gen_decl (Ptr_meta_sort.sort ());
      Full_ptr_sort.get_meta e
  | _ -> wrong ()

let h_meta_as (part : meta_part) : smt_op =
 fun ~sort_of_ty:_ ~encode_child -> function
  | [ v ] -> (
      let e = encode_child v in
      match part with
      | PartLen -> Ptr_meta_sort.get_int e
      | PartVTable -> Ptr_meta_sort.get_ptr e)
  | _ -> wrong ()

let h_field i : smt_op =
 fun ~sort_of_ty ~encode_child -> function
  | [ v ] ->
      let e = encode_child v in
      let sorts = List.map sort_of_ty (t_as_tuple v.ty) in
      gen_decl (Tuple_sort.sort sorts);
      Tuple_sort.get_field sorts (Z.to_int i) e
  | _ -> wrong ()

let h_variant_field var i : smt_op =
 fun ~sort_of_ty ~encode_child -> function
  | [ v ] ->
      let e = encode_child v in
      let adt = t_as_enum v.ty in
      gen_decl (Enum_sort.sort sort_of_ty adt);
      let variant = Types.VariantId.nth (Crate.as_enum adt) var in
      Enum_sort.get_field adt variant (Z.to_int i) e
  | _ -> wrong ()

let h_is_variant var : smt_op =
 fun ~sort_of_ty ~encode_child -> function
  | [ v ] ->
      let e = encode_child v in
      let adt = t_as_enum v.ty in
      let variants = Crate.as_enum adt in
      let variant = Types.VariantId.nth variants var in
      gen_decl (Enum_sort.sort sort_of_ty adt);
      Enum_sort.is_variant adt variant e
  | _ -> wrong ()

let h_array_field i : smt_op =
 fun ~sort_of_ty:_ ~encode_child -> function
  | [ v ] -> seq_nth (encode_child v) (int_k (Z.to_int i))
  | _ -> wrong ()
