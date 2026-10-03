(* The OLD stack (soteria-rust/lib/svalue: [Svalue.Make (Ext)] with the rust
   extension) to the neutral AST. Matches the constructors of [Svalue] and of
   [Ext_base]. *)

module Rust = Soteria_rust_lib
module Ty = Legacy_svalue.Typed
module Sv = Soteria.Bv_values.Svalue
module E = Legacy_svalue.Ext_base
module Ptr_tag = Rust.Svalue.Ptr_tag
module Types = Charon.Types
open Neutral

let rec sort (s : Ty.Svalue.ty) : Neutral.sort =
  match s with
  | TBool -> SBool
  | TBitVector n -> SBv n
  | TLoc n -> SLoc n
  | TPointer n -> SPtr n
  | TFloat p -> SFloat (Sv.FloatPrecision.show p)
  | TSeq s -> SSeq (sort s)
  | TExtension e -> (
      match e with
      | TEnum d -> SEnum (Neutral.decl_ref d)
      | TUnion d -> SUnion (Neutral.decl_ref d)
      | TTuple tys -> STuple (List.map sort tys)
      | TArray (ty, n) -> SArray (sort ty, Z.to_string n)
      | TThinPtr -> SThin
      | TFullPtr -> SFull
      | TPtrMeta -> SMeta
      | TPolyType -> SPoly)

let tag_str = function None -> "*" | Some t -> Ptr_tag.show t

let part_name : E.Unop.ptr_part -> string = function
  | PtrInner -> "ptr"
  | PtrSize -> "size"
  | PtrAlign -> "align"

let memo : (int, Neutral.t) Hashtbl.t = Hashtbl.create 1021
let reset () = Hashtbl.reset memo

(* The nodes converted, by kind (for the statistics of the test) *)
let kinds : (string, int) Hashtbl.t = Hashtbl.create 31

let count (x : Neutral.t) =
  let k = Neutral.kind_name x.n in
  Hashtbl.replace kinds k
    (1 + Option.value ~default:0 (Hashtbl.find_opt kinds k))

let to_nt : Ty.Svalue.t -> Neutral.t =
  let rec go (v : Ty.Svalue.t) : Neutral.t =
    match Hashtbl.find_opt memo v.tag with
    | Some x -> x
    | None ->
        let x = { s = sort v.node.ty; n = node v } in
        Hashtbl.add memo v.tag x;
        count x;
        x
  and node (v : Ty.Svalue.t) : Neutral.node =
    match v.node.kind with
    | Var x -> Var (Soteria.Symex.Var.to_int x)
    | Bool b -> Bool b
    | BitVec z -> (
        match v.node.ty with
        | TLoc _ -> Loc (Z.to_string z)
        | _ -> Bv (Z.to_string z))
    | Float f -> Flt (Z.to_string (Floatml.AnyFloat.to_z f))
    | Ptr (l, o) -> Op ("&", [ go l; go o ])
    | Seq l -> Seq (List.map go l)
    | Exists (bs, b) ->
        Exists
          ( List.map (fun (x, s) -> (Soteria.Symex.Var.to_int x, sort s)) bs,
            go b )
    | Unop (op, a) -> Op (Fmt.str "%a" Sv.Unop.pp op, [ go a ])
    | Binop (op, a, b) ->
        let a = go a in
        let b = go b in
        Op (Fmt.str "%a" Sv.Binop.pp op, [ a; b ])
    | Triop (op, a, b, c) ->
        let a = go a in
        let b = go b in
        let c = go c in
        Op (Fmt.str "%a" Sv.Triop.pp op, [ a; b; c ])
    | Nop (op, l) -> Op (Fmt.str "%a" Sv.Nop.pp op, List.map go l)
    | Extension e -> ext e
  and ext : _ E.ext_t -> Neutral.node = function
    | Ptr (p, m) ->
        let p = go p in
        let m = go m in
        Full (p, m)
    | PtrMeta MetaUnit -> MetaUnit
    | PtrMeta (MetaLen l) -> MetaLen (go l)
    | PtrMeta (MetaVTable l) -> MetaVTable (go l)
    | ThinPtr { ptr; tag; size; align } ->
        let ptr = go ptr in
        let size = go size in
        let align = go align in
        Thin (tag_str tag, ptr, size, align)
    | Enum (v, vs) -> Enum (Types.VariantId.to_int v, List.map go vs)
    | Tuple vs -> Tuple (List.map go vs)
    | Array vs -> Array (List.map go (Iarray.to_list vs))
    | Union bs ->
        Union
          (List.map
             (fun ({ value; offset; size } : _ E.block) ->
               let v, agg =
                 match value with
                 | Scalar v -> (go v, None)
                 | Aggregate (v, ty) -> (go v, Some (Neutral.rty ty))
               in
               let off = go offset in
               let sz = go size in
               { v; agg; off; sz })
             bs)
    | PolyVal id -> Poly (Types.TypeVarId.to_int id)
    | Unop (op, a) -> (
        let a = go a in
        match op with
        | ThinPtrPart p -> Thin_part (part_name p, a)
        | FullPtrInner -> Full_inner a
        | FullPtrMeta -> Full_meta a
        | PtrMetaAs MetaLen -> Meta_as ("len", a)
        | PtrMetaAs MetaVTable -> Meta_as ("vtable", a)
        | Field i -> Field (i, a)
        | VariantField (v, i) -> Variant_field (Types.VariantId.to_int v, i, a)
        | IsVariant v -> Is_variant (Types.VariantId.to_int v, a)
        | ArrayField i -> Array_field (i, a))
  in
  go

let dump (v : Ty.Svalue.t) : string =
  let x = to_nt v in
  Neutral.show x

let dump_ty (s : Ty.Svalue.ty) : string = Neutral.show_sort (sort s)
