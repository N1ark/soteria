(* The neutral AST of the Rust values, written once: both stacks convert their
   values to it (old_conv.ml, new_conv.ml), by matching their own constructors,
   and the test compares what they print ([show]), which is injective:
   constructor names, parameters, sorts and the order of the operands are all in
   the text (STRICT mode: the operands of the commutative operators are compared
   in the order of their tags, which depend on the order in which the two stacks
   created their nodes).

   The nodes of the shared C modules (bit-vector, float, bool and pointer
   operators) are [Op (name, operands)], the name being the head that the
   printer of the stack gives the operator, with its parameters (checked flags,
   widths, rounding modes): the C operators have their own differential test
   (soteria/tests/bv_diff); they only appear here as parts of the Rust
   values. *)

module Types = Charon.Types

(* A string on one line, with single spaces: the derived printers of Charon
   break lines *)
let flat s =
  String.split_on_char ' ' (String.map (function '\n' -> ' ' | c -> c) s)
  |> List.filter (fun w -> w <> "")
  |> String.concat " "

let decl_ref (d : Types.type_decl_ref) = flat (Types.show_type_decl_ref d)
let rty (t : Types.ty) = flat (Types.show_ty t)

type sort =
  | SBool
  | SBv of int
  | SLoc of int
  | SPtr of int
  | SFloat of string
  | SSeq of sort
  | SEnum of string
  | SUnion of string
  | STuple of sort list
  | SArray of sort * string
  | SThin
  | SFull
  | SMeta
  | SPoly

type t = { s : sort; n : node }

and node =
  | Var of int
  | Bool of bool
  | Bv of string
  | Loc of string
  | Flt of string
  | Seq of t list
  | Exists of (int * sort) list * t
  | Op of string * t list
  (* the rust module *)
  | Thin of string * t * t * t  (** tag, pointer, size, align *)
  | Full of t * t
  | MetaUnit
  | MetaLen of t
  | MetaVTable of t
  | Enum of int * t list
  | Tuple of t list
  | Array of t list
  | Union of blk list
  | Poly of int
  | Thin_part of string * t
  | Full_inner of t
  | Full_meta of t
  | Meta_as of string * t
  | Field of int * t
  | Variant_field of int * int * t
  | Is_variant of int * t
  | Array_field of int * t

and blk = { v : t; agg : string option; off : t; sz : t }

let rec show_sort = function
  | SBool -> "bool"
  | SBv n -> Printf.sprintf "bv%d" n
  | SLoc n -> Printf.sprintf "loc%d" n
  | SPtr n -> Printf.sprintf "ptr%d" n
  | SFloat p -> p
  | SSeq s -> Printf.sprintf "seq(%s)" (show_sort s)
  | SEnum s -> Printf.sprintf "enum<%s>" s
  | SUnion s -> Printf.sprintf "union<%s>" s
  | STuple l ->
      Printf.sprintf "tuple(%s)" (String.concat ", " (List.map show_sort l))
  | SArray (s, n) -> Printf.sprintf "array(%s; %s)" (show_sort s) n
  | SThin -> "thin"
  | SFull -> "full"
  | SMeta -> "meta"
  | SPoly -> "poly"

let rec show { s; n } =
  let l f xs = String.concat ", " (List.map f xs) in
  let body =
    match n with
    | Var i -> Printf.sprintf "var %d" i
    | Bool b -> string_of_bool b
    | Bv z -> "bv " ^ z
    | Loc z -> "loc " ^ z
    | Flt z -> "float " ^ z
    | Seq xs -> Printf.sprintf "seq[%s]" (l show xs)
    | Exists (bs, b) ->
        Printf.sprintf "exists(%s). %s"
          (l (fun (i, s) -> Printf.sprintf "%d:%s" i (show_sort s)) bs)
          (show b)
    | Op (name, xs) -> Printf.sprintf "%s{%s}" name (l show xs)
    | Thin (tag, p, size, align) ->
        Printf.sprintf "thin[%s](%s; %s; %s)" tag (show p) (show size)
          (show align)
    | Full (p, m) -> Printf.sprintf "full(%s; %s)" (show p) (show m)
    | MetaUnit -> "meta-unit"
    | MetaLen x -> Printf.sprintf "meta-len(%s)" (show x)
    | MetaVTable x -> Printf.sprintf "meta-vtable(%s)" (show x)
    | Enum (v, xs) -> Printf.sprintf "enum#%d(%s)" v (l show xs)
    | Tuple xs -> Printf.sprintf "tuple(%s)" (l show xs)
    | Array xs -> Printf.sprintf "array[%s]" (l show xs)
    | Union bs ->
        Printf.sprintf "union{%s}"
          (l
             (fun { v; agg; off; sz } ->
               Printf.sprintf "[%s@%s+%s%s]" (show v) (show off) (show sz)
                 (match agg with None -> "" | Some t -> " : " ^ t))
             bs)
    | Poly i -> Printf.sprintf "poly#%d" i
    | Thin_part (p, x) -> Printf.sprintf "thin-part-%s(%s)" p (show x)
    | Full_inner x -> Printf.sprintf "full-inner(%s)" (show x)
    | Full_meta x -> Printf.sprintf "full-meta(%s)" (show x)
    | Meta_as (p, x) -> Printf.sprintf "meta-as-%s(%s)" p (show x)
    | Field (i, x) -> Printf.sprintf "field-%d(%s)" i (show x)
    | Variant_field (v, i, x) ->
        Printf.sprintf "variant-field-%d-%d(%s)" v i (show x)
    | Is_variant (v, x) -> Printf.sprintf "is-variant-%d(%s)" v (show x)
    | Array_field (i, x) -> Printf.sprintf "array-field-%d(%s)" i (show x)
  in
  Printf.sprintf "(%s : %s)" body (show_sort s)

(* The kind of a node, for the statistics of the test *)
let kind_name = function
  | Var _ -> "Var"
  | Bool _ -> "Bool"
  | Bv _ -> "BitVec"
  | Loc _ -> "LocLit"
  | Flt _ -> "Float"
  | Seq _ -> "Seq"
  | Exists _ -> "Exists"
  | Op _ -> "Op"
  | Thin _ -> "ThinPtr"
  | Full _ -> "FullPtr"
  | MetaUnit | MetaLen _ | MetaVTable _ -> "PtrMeta"
  | Enum _ -> "Enum"
  | Tuple _ -> "Tuple"
  | Array _ -> "Array"
  | Union _ -> "Union"
  | Poly _ -> "PolyVal"
  | Thin_part _ -> "ThinPtrPart"
  | Full_inner _ -> "FullPtrInner"
  | Full_meta _ -> "FullPtrMeta"
  | Meta_as _ -> "PtrMetaAs"
  | Field _ -> "Field"
  | Variant_field _ -> "VariantField"
  | Is_variant _ -> "IsVariant"
  | Array_field _ -> "ArrayField"

let rec iter_nodes f ({ n; _ } as x) =
  f x;
  let go = iter_nodes f in
  match n with
  | Var _ | Bool _ | Bv _ | Loc _ | Flt _ | MetaUnit | Poly _ -> ()
  | Seq xs | Op (_, xs) | Enum (_, xs) | Tuple xs | Array xs -> List.iter go xs
  | Exists (_, b) -> go b
  | Thin (_, a, b, c) ->
      go a;
      go b;
      go c
  | Full (a, b) ->
      go a;
      go b
  | MetaLen a
  | MetaVTable a
  | Thin_part (_, a)
  | Full_inner a
  | Full_meta a
  | Meta_as (_, a)
  | Field (_, a)
  | Variant_field (_, _, a)
  | Is_variant (_, a)
  | Array_field (_, a) ->
      go a
  | Union bs ->
      List.iter
        (fun { v; off; sz; _ } ->
          go v;
          go off;
          go sz)
        bs

(* The tags of the provenance of pointers that the generators draw from, shared
   by both stacks (a tag is printed by its number) *)
let tag_pool : Soteria_rust_lib.Svalue.Ptr_tag.t array =
  Array.init 6 (fun _ -> Soteria_rust_lib.Svalue.Ptr_tag.fresh_tag ())
