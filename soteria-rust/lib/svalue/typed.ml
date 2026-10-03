(* The typed layer of the Rust language, over the generic stack of Soteria
   ([Rust_stack.L]) and the smart constructors of the generated rules
   ([Rust_lang]), which build the nodes themselves. [TExtension X] of the old
   extension is the sort [X], and the nodes [ThinPtr], [Union] and [PolyVal] are
   matched directly (functions [_set_ptr], [tag_of], [as_union] and
   [as_type_var]). The blocks of a union are the records of the generated types;
   the polymorphic records of the interface convert to them at the boundary. *)

open Charon
open Soteria.Soteria_std
open Common.Charon_util
module R = Rust_types
module K = Rust_lang

type ('sc, 'ag) block_value_raw = Scalar of 'sc | Aggregate of 'ag * Types.ty

type ('sc, 'ag, 'ofs, 'sz) block_raw = {
  value : ('sc, 'ag) block_value_raw;
  offset : 'ofs;
  size : 'sz;
}

(* [Make_transparent] exposes [t]/[ty] as the underlying untyped svalue, so the
   extension helpers below can be written without ghost-typing ceremony. The
   [typed.mli] re-seals [t]/[ty] as abstract for the rest of Soteria Rust. *)
module Self = Iface.Typed.Make_transparent (Rust_stack.L)
include Self

module T = struct
  include T

  type sptr_f = [ `FullPtr ]
  type sptr_t = [ `ThinPtr ]
  type tuple = [ `Tuple ]
  type enum = [ `Enum ]
  type union = [ `Union ]
  type poly = [ `Poly ]
  type ptr_meta = [ sint | sptr_t ]
  type scalar = [ sint | sfloat | sptr_f | poly ]
  type aggregate = [ tuple | enum | union ]
  type any = [ scalar | aggregate ]

  let pp_sptr_f = Fmt.nop
  let pp_sptr_t = Fmt.nop
  let pp_tuple = Fmt.nop
  let pp_enum = Fmt.nop
  let pp_union = Fmt.nop
  let pp_poly = Fmt.nop
  let pp_scalar = Fmt.nop
  let pp_aggregate = Fmt.nop
  let pp_any = Fmt.nop
end

type block_value = (T.scalar t, T.aggregate t) block_value_raw
type block = (T.scalar t, T.aggregate t, T.sint t, T.nonzero t) block_raw

(* The blocks of a union and the blocks of the interface *)
let block_to_raw ({ value; offset; size } : block) : R.block =
  {
    bvalue =
      (match value with
      | Scalar v -> R.Scalar v
      | Aggregate (v, ty) -> R.Aggregate (v, ty));
    boffset = offset;
    bsize = size;
  }

let block_of_raw ({ bvalue; boffset; bsize } : R.block) : block =
  {
    value =
      (match bvalue with
      | R.Scalar v -> Scalar v
      | R.Aggregate (v, ty) -> Aggregate (v, ty));
    offset = boffset;
    size = bsize;
  }

(* The printing of a block, [ext_base.ml:pp_block] *)
let pp_block_value pp_v pp_ag ft = function
  | Scalar v -> pp_v ft v
  | Aggregate (ag, ty) -> Fmt.pf ft "%a : %a" pp_ag ag Types.pp_ty ty

let pp_block pp_v pp_ag pp_ofs pp_sz ft { value; offset; size } =
  Fmt.pf ft "(%a: %a-%a)" pp_ofs offset
    (pp_block_value pp_v pp_ag)
    value pp_sz size

let pp_block ft (block : block) = pp_block ppa ppa ppa ppa ft block

(** [CastError (value, expected, got)] *)
exception CastError of T.any t * T.any ty * T.any ty

exception TypedMigration of string

let () =
  Printexc.register_printer (function
    | CastError (v, expected, got) ->
        Some
          (Fmt.str "Cast error: expected %a, got %a for value %a" ppa_ty
             expected ppa_ty got ppa v)
    | TypedMigration msg -> Some (Fmt.str "TODO(typed migration): %s" msg)
    | _ -> None)

let cast_error v ty = raise (CastError (v, ty, get_ty v))
let todo_migration msg = raise (TypedMigration msg)

let float_precision :
    Values.float_type -> Soteria.Bv_values.Bv_base.FloatPrecision.t =
  Rust_charon.float_precision

let of_float_precision :
    Soteria.Bv_values.Bv_base.FloatPrecision.t -> Values.float_type = function
  | F16 -> F16
  | F32 -> F32
  | F64 -> F64
  | F128 -> F128

(* The raw pointer type; only used to materialise a fully-symbolic nondet
   pointer in [Value_codec] (see {!Ptr.of_raw}). *)
let t_ptr () = t_ptr (8 * size_of_uint_ty Usize)
let t_ptr_f () : _ ty = R.TFullPtr
let t_ptr_t () : _ ty = R.TThinPtr
let t_loc () = t_loc (8 * size_of_uint_ty Usize)
let t_usize () = t_int (8 * size_of_uint_ty Usize)

let t_lit : Types.literal_type -> [> T.sint ] ty = function
  | (TInt _ | TUInt _ | TBool | TChar) as ty -> t_int (size_of_literal_ty ty * 8)
  | TFloat _ -> failwith "t_lit: unexpected float literal type"

let t_float (ty : Types.float_type) : [< T.sfloat ] ty =
  t_float (float_precision ty)

let t_tuple tys : [> T.tuple ] ty = R.TTuple tys
let t_array ty n : [> T.tuple ] ty = R.TArray (ty, n)

let t_enum adt : [> T.enum ] ty =
  assert (Common.Charon_util.tyref_is_substituted adt);
  R.TEnum adt

let t_union adt : [> T.union ] ty =
  assert (Common.Charon_util.tyref_is_substituted adt);
  R.TUnion adt

let cast_checked ~ty v =
  match cast_checked v ty with Some v -> v | None -> cast_error v ty

let as_any x = (x : [< T.any ] t :> [> T.any ] t)
let cast_nonzero (x : [< T.sint ] t) : [> T.nonzero ] t = x

let cast_lit ty (v : 'a t) : [> T.sint ] t =
  let size = 8 * size_of_literal_ty ty in
  cast_checked ~ty:(t_int size) v

let cast_i uty = cast_lit (TUInt uty)
let cast_f fty v = cast_checked ~ty:(t_float fty) v

let cast_float v =
  match cast_float v with Some v -> v | None -> cast_error v (t_float F64)

let cast_ptr_f v = cast_checked ~ty:(t_ptr_f ()) v
let cast_ptr_t v = cast_checked ~ty:(t_ptr_t ()) v

let cast_tuple v =
  match get_ty v with R.TTuple _ -> v | _ -> cast_error v (t_tuple [])

let cast_array v =
  match get_ty v with
  | R.TArray _ -> v
  | _ -> cast_error v (t_array (t_int 1) Z.zero)

(* The [adt] ref, when given, additionally checks the value is that precise
   enum/union; callers that only know the kind (e.g. the generic store
   navigation) may omit it. *)
let dummy_decl_ref =
  {
    Types.id = TypesUtils.unit_type_decl_id;
    generics = TypesUtils.empty_generic_args;
    builtin = None;
  }

let cast_enum ?adt v =
  match (get_ty v, adt) with
  | R.TEnum _, None -> v
  | R.TEnum adt', Some adt when Types.equal_type_decl_ref adt adt' -> v
  | _ -> cast_error v (t_enum (Option.value adt ~default:dummy_decl_ref))

let cast_union ?adt v =
  match (get_ty v, adt) with
  | R.TUnion _, None -> v
  | R.TUnion adt', Some adt when Types.equal_type_decl_ref adt adt' -> v
  | _ -> cast_error v (t_union (Option.value adt ~default:dummy_decl_ref))

module BitVec = struct
  include BitVec

  let bv_to_z (ity : Types.integer_type) =
    let signed = match ity with Signed _ -> true | Unsigned _ -> false in
    BitVec.bv_to_z signed (size_of_literal_ty (lit_of_int_ty ity) * 8)

  let mk_lit ty = BitVec.mk_masked (size_of_literal_ty ty * 8)
  let mk_lit_nz ty = BitVec.mk_nz (size_of_literal_ty ty * 8)
  let mki_lit ty = BitVec.mki_masked (size_of_literal_ty ty * 8)
  let mki_lit_nz ty = BitVec.mki_nz (size_of_literal_ty ty * 8)
  let u8 = mk_lit (TUInt U8)
  let u8i = mki_lit (TUInt U8)
  let u8nz = mk_lit_nz (TUInt U8)
  let u8inz = mki_lit_nz (TUInt U8)
  let u16 = mk_lit (TUInt U16)
  let u32 = mk_lit (TUInt U32)
  let u32i = mki_lit (TUInt U32)
  let u32nz = mk_lit_nz (TUInt U32)
  let u32inz = mki_lit_nz (TUInt U32)
  let u64 = mk_lit (TUInt U64)
  let u64i = mki_lit (TUInt U64)
  let u128 = mk_lit (TUInt U128)
  let u128i = mki_lit (TUInt U128)
  let usize z = mk_lit (TUInt Usize) z
  let usizei z = mki_lit (TUInt Usize) z
  let usizenz z = mk_lit_nz (TUInt Usize) z
  let usizeinz z = mki_lit_nz (TUInt Usize) z

  let of_bool : T.sbool t -> [> T.sint ] t =
    of_bool (size_of_literal_ty TBool * 8)

  let of_scalar : Values.scalar_value -> [> T.sint ] t = function
    | UnsignedScalar (Usize, v) | SignedScalar (Isize, v) -> usize v
    | UnsignedScalar (U8, v) | SignedScalar (I8, v) -> u8 v
    | UnsignedScalar (U16, v) | SignedScalar (I16, v) -> u16 v
    | UnsignedScalar (U32, v) | SignedScalar (I32, v) -> u32 v
    | UnsignedScalar (U64, v) | SignedScalar (I64, v) -> u64 v
    | UnsignedScalar (U128, v) | SignedScalar (I128, v) -> u128 v

  let of_literal : Values.literal -> [> T.sint ] t = function
    | VScalar s -> of_scalar s
    | VChar c -> u32i (Uchar.to_int c)
    | VBool b -> of_bool (Bool.of_bool b)
    | l ->
        Fmt.failwith "Cannot convert non-scalar literal %s to bitvector"
          (Print.literal_to_string l)

  let of_constant_expr : Types.constant_expr -> [> T.sint ] t = function
    | { kind = CLiteral lit; _ } -> of_literal lit
    | c ->
        Fmt.failwith "Cannot convert non-value const expr %a to bitvector"
          Types.pp_constant_expr c

  let of_constant_expr_opt : Types.constant_expr -> [> T.sint ] t option =
    function
    | { kind = CLiteral lit; _ } -> Some (of_literal lit)
    | _ -> None

  let max ~signed l r = ite (gt ~signed l r) l r
  let min ~signed l r = ite (lt ~signed l r) l r
  let sure_is_zero v = Option.is_some_and Z.(equal zero) (to_z v)

  let to_float ~rounding ~signed ~fp v =
    to_float ~rounding ~signed ~fp:(float_precision fp) v
end

module BV = BitVec

module FloatPrecision = struct
  include FloatPrecision

  let size fp = size (float_precision fp)
  let significand_bits fp = significand_bits (float_precision fp)
  let exponent_bits fp = exponent_bits (float_precision fp)
end

module Float = struct
  include Float

  let mk fty = mk (float_precision fty)
  let zero fp = zero (float_precision fp)
  let neg_zero fp = neg_zero (float_precision fp)
  let one fp = one (float_precision fp)
  let infinity fp = infinity (float_precision fp)
  let neg_infinity fp = neg_infinity (float_precision fp)
  let nan fp = nan (float_precision fp)
  let of_z fty = of_z (float_precision fty)
  let fp_of v = of_float_precision (fp_of v)
  let cast ~rounding ~fp v = cast ~rounding ~fp:(float_precision fp) v

  let rem_warning =
    let warn =
      String.Interned.intern
        "a symbolic remainder operation on floats was performed on two \
         symbolic operands. Solvers are typically very bad at reasoning about \
         this, and it may lead to time outs. See \
         https://github.com/soteria-tools/soteria/issues/476"
    in
    fun x y ->
      match (to_float_opt x, to_float_opt y) with
      | None, None -> Soteria.Terminal.Warn.warn_once warn
      | _ -> ()

  let rem x y =
    rem_warning x y;
    rem x y

  let fmod x y =
    rem_warning x y;
    fmod x y
end

(* This module exposes pointers as the two standalone embedded values, thin
   pointers ([sptr_t]) and full/wide pointers ([sptr_f]). The fact that a thin
   pointer wraps a "raw" [sptr] (a bare location+offset) is an implementation
   detail: the raw [Self.Ptr] operations are used only here, and are never
   re-exposed, so [sptr] never leaks into the rest of the interpreter. *)
module Ptr = struct
  (* {1 Locations} *)

  let null_loc () = Self.Ptr.null_loc (8 * size_of_uint_ty Usize)
  let loc_of_int i = Self.Ptr.loc_of_int (8 * size_of_uint_ty Usize) i
  let is_null_loc loc = Self.Ptr.is_null_loc loc

  (* {1 Internal raw-pointer plumbing (never exposed)} *)

  let _thin_part part ptr = K.thin_ptr_part part ptr

  let _set_ptr ptr f =
    let inner =
      match (ptr : R.t).kind with
      | R.ThinPtr inner -> inner
      | _ ->
          (* Symbolic thin pointer: rebuild it from its parts. As in [tag_of],
             we assume symbolic pointers have no tag. *)
          {
            R.ptr = _thin_part R.PtrInner ptr;
            psize = _thin_part R.PtrSize ptr;
            palign = _thin_part R.PtrAlign ptr;
            ptag = None;
          }
    in
    K.mk_thin_ptr (f inner)

  let _inner ptr = _thin_part R.PtrInner ptr

  let of_raw ~ptr ~size ~align ~tag =
    K.mk_thin_ptr { R.ptr; ptag = tag; psize = size; palign = align }

  let mk_ptr_t ~loc ~ofs ~size ~align ~tag =
    of_raw ~ptr:(Self.Ptr.mk loc ofs) ~size ~align ~tag

  let loc ptr = Self.Ptr.loc (_inner ptr)
  let ofs ptr = Self.Ptr.ofs (_inner ptr)
  let decompose ptr = Self.Ptr.decompose (_inner ptr)
  let is_null ptr = Self.Ptr.is_null (_inner ptr)
  let is_at_null_loc ptr = Self.Ptr.is_at_null_loc (_inner ptr)

  let add_ofs ptr o =
    _set_ptr ptr (fun inner ->
        { inner with ptr = Self.Ptr.add_ofs inner.ptr o })

  let set_ofs ptr o =
    _set_ptr ptr (fun inner ->
        { inner with ptr = Self.Ptr.mk (Self.Ptr.loc inner.ptr) o })

  let with_tag ptr tag = _set_ptr ptr (fun inner -> { inner with ptag = tag })
  let align_of ptr = _thin_part R.PtrAlign ptr
  let size_of ptr = _thin_part R.PtrSize ptr
  let allocation_info ptr = (size_of ptr, align_of ptr)

  let tag_of ptr =
    match (ptr : R.t).kind with
    | R.ThinPtr inner -> inner.ptag
    | _ ->
        (* HACK: we assume symbolic pointers have no tag *)
        None

  let has_provenance ptr = not (is_at_null_loc ptr)
  let have_same_provenance p1 p2 = sem_eq (loc p1) (loc p2)

  let in_bound ptr =
    let open Infix in
    BV.usizei 0 <=@ ofs ptr &&@ (ofs ptr <@ size_of ptr)

  (** For Miri: the allocation ID of this location, as a u64. *)
  let as_id ptr =
    (* the cast converts the location to a bitvector, which is safe because they
       have the same type, internally. *)
    let loc = cast (loc ptr) in
    let size = size_of_int loc in
    if size < 64 then BV.extend ~signed:false (64 - size) loc
    else (
      (* should basically always be the case but let's be cautious *)
      assert (size = 64);
      loc)

  (** The null pointer, which always decays to 0, and has no provenance.
      Equivalent to [of_address 0]. *)
  let null () =
    mk_ptr_t ~loc:(null_loc ()) ~ofs:(BV.usizei 0) ~size:(BV.usizei 0)
      ~align:(BV.usizeinz 1) ~tag:None

  (** Converts an address into a pointer, without provenance. *)
  let of_address ofs = add_ofs (null ()) ofs

  (* {1 Full/wide pointers ([sptr_f])} *)

  let of_ptr_t ptr = K.of_thin_ptr ptr
  let with_ptr fptr tptr = K.full_ptr_set_inner tptr fptr

  let mk_ptr_f ptr (meta : _ t) =
    let meta =
      match get_ty meta with
      | R.TBitVector _ -> K.mk_len_meta meta
      | R.TThinPtr -> K.mk_vtable_meta meta
      | ty -> L.failwith "mk_ptr_f: invalid metadata type %a" ppa_ty ty
    in
    K.mk_full_ptr ptr meta

  let mk_ptr_f_opt ptr meta_opt =
    match meta_opt with Some meta -> mk_ptr_f ptr meta | None -> of_ptr_t ptr

  (** The null full (wide) pointer: a {!null} thin pointer with no metadata. *)
  let null_f () = of_ptr_t (null ())

  (** Like {!of_address}, but produces a full pointer with no metadata. *)
  let of_address_f addr = of_ptr_t (of_address addr)

  let len_meta ptr = K.full_ptr_meta R.PartLen ptr
  let vtable_meta ptr = K.full_ptr_meta R.PartVTable ptr
  let ptr_of ptr = K.full_ptr_inner ptr
end

module Adt = struct
  (** {2 Tuples} *)

  let mk_tuple vs = K.mk_tuple vs
  let unit = mk_tuple []
  let as_tuple v = K.tuple_fields v

  let as_tuple1 v =
    match as_tuple v with [ a ] -> a | _ -> cast_error v (t_tuple [ t_int 1 ])

  let as_tuple2 v =
    match as_tuple v with
    | [ a; b ] -> (a, b)
    | _ -> cast_error v (t_tuple [ t_int 2 ])

  let as_tuple3 v =
    match as_tuple v with
    | [ a; b; c ] -> (a, b, c)
    | _ -> cast_error v (t_tuple [ t_int 3 ])

  let field_of idx v = K.field_of (Z.of_int idx) v
  let set_field idx f v = K.set_field (Z.of_int idx) f v
  let update_field idx f v = set_field idx (f (field_of idx v)) v

  (** {2 Enums} *)

  let mk_enum adt v_id vs = K.mk_enum adt v_id vs
  let as_enum_of_variant var v = K.as_enum_of_variant var v
  let field_of_variant var idx v = K.field_of_variant var (Z.of_int idx) v

  let set_field_of_variant var idx f v =
    K.set_field_of_variant var (Z.of_int idx) f v

  let update_field_of_variant var idx f v =
    set_field_of_variant var idx (f (field_of_variant var idx v)) v

  let is_variant var_id v = K.is_variant var_id v

  let discriminant_of (v : _ t) =
    let variants = Crate.as_enum (Rust_charon.t_as_enum (get_ty v)) in
    let rec aux : Types.variant list -> _ t = function
      | [] -> L.failwith "discriminant_of: empty enum"
      | [ var ] -> BV.of_literal var.discriminant
      | var :: rest ->
          ite (is_variant var.id v) (BV.of_literal var.discriminant) (aux rest)
    in
    aux variants

  (** {2 Arrays} *)

  let mk_array elem_ty arr = K.mk_array elem_ty arr
  let as_array v = K.array_elems v
  let array_field_of idx v = K.array_field_of (Z.of_int idx) v
  let set_array_field idx f v = K.set_array_field (Z.of_int idx) f v

  let update_array_field idx f v =
    set_array_field idx (f (array_field_of idx v)) v

  (** {2 Unions and PolyVal} *)

  let mk_union adt blocks = K.mk_union adt (List.map block_to_raw blocks)
  let mk_poly ty_id = K.mk_poly ty_id

  (* HACK: i have no idea what this really means or how to lift this for
     variables... *)
  let as_union v =
    match (v : R.t).kind with
    | R.Union blocks -> List.map block_of_raw blocks
    | _ -> todo_migration "as_union unop"

  let as_type_var v =
    match (v : R.t).kind with
    | R.PolyVal ty_id -> ty_id
    | _ -> todo_migration "as_type_var unop"

  module Checked = struct
    let mk_enum tref variant vs =
      let variant =
        Crate.as_enum tref
        |> List.find (fun (v : Types.variant) -> v.variant_name = variant)
      in
      assert (List.compare_lengths variant.fields vs = 0);
      mk_enum tref variant.id vs
  end
end

module Syntax = struct
  module U8 = struct
    module Sym_int_syntax = struct
      let mk_nonzero = BitVec.u8inz
      let zero () = BitVec.u8 Z.zero
      let one () = BitVec.u8nz Z.one
    end
  end

  module U32 = struct
    module Sym_int_syntax = struct
      let mk_nonzero = BitVec.u32inz
      let zero () = BitVec.u32 Z.zero
      let one () = BitVec.u32nz Z.one
    end
  end

  module Usize = struct
    module Sym_int_syntax = struct
      let mk_nonzero = BitVec.usizeinz
      let zero () = BitVec.usize Z.zero
      let one () = BitVec.usizenz Z.one
    end
  end
end
