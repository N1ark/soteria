(* Golden dump of the Rust value language, written against the public
   [Svalue.Typed] interface of soteria-rust only: it must compile and print the
   same bytes before and after the value language is regenerated.

   Everything that is not reachable through [Typed] (or its siblings [Ptr_tag]
   and [Soteria.*]) goes through [Shim], which is the only part to re-implement
   in a port: [Shim.with_crate] / [Shim.mk_crate] (installing a synthetic
   [Crate] for enum and union operations, and a target pointer size). *)

open Charon
module Rust = Soteria_rust_lib
module Ty = Rust_new.Rust_typed
module Ptr_tag = Rust.Svalue.Ptr_tag
module Var = Soteria.Symex.Var
module Smt = Soteria.Smt
module Decls = Soteria.Solvers.Decls
module BV = Ty.BV
module Fl = Ty.Float
module Ptr = Ty.Ptr
module Adt = Ty.Adt
module Eval = Ty.Eval
module Expr = Ty.Expr
module L = Ty.Lang
module T = Ty.T

type v = T.any Ty.t

(* {1 Output} *)

let out = Buffer.create (1 lsl 20)

let pr fmt =
  Format.kasprintf
    (fun s ->
      Buffer.add_string out s;
      Buffer.add_char out '\n')
    fmt

let to_s pp x =
  let b = Buffer.create 64 in
  let f = Format.formatter_of_buffer b in
  Format.pp_set_margin f 1_000_000;
  pp f x;
  Format.pp_print_flush f ();
  String.map (function '\n' -> ' ' | c -> c) (Buffer.contents b)

let ppa v = to_s Ty.ppa v
let ppty ty = to_s Ty.ppa_ty ty
let ppu (u : Ty.Svalue.t) = ppa (Ty.type_ u : v)

let lit_name : Types.literal_type -> string = function
  | TInt I8 -> "i8"
  | TInt I16 -> "i16"
  | TInt I32 -> "i32"
  | TInt I64 -> "i64"
  | TInt I128 -> "i128"
  | TInt Isize -> "isize"
  | TUInt U8 -> "u8"
  | TUInt U16 -> "u16"
  | TUInt U32 -> "u32"
  | TUInt U64 -> "u64"
  | TUInt U128 -> "u128"
  | TUInt Usize -> "usize"
  | TBool -> "bool"
  | TChar -> "char"
  | TFloat F16 -> "f16"
  | TFloat F32 -> "f32"
  | TFloat F64 -> "f64"
  | TFloat F128 -> "f128"

let exn_str = function
  | Assert_failure _ -> "Assert_failure"
  | Failure s -> "Failure " ^ s
  | Invalid_argument s -> "Invalid_argument " ^ s
  | Stack_overflow -> "Stack_overflow"
  | Not_found -> "Not_found"
  | Division_by_zero -> "Division_by_zero"
  | e -> Printexc.to_string e

let squash s =
  String.concat " "
    (List.filter
       (fun w -> w <> "")
       (String.split_on_char ' '
          (String.map (function '\n' -> ' ' | c -> c) s)))

let guard f = try f () with e -> "EXN " ^ squash (exn_str e)
let keep : Obj.t list ref = ref []
let retain x = keep := Obj.repr x :: !keep
let gc_mode = ref false
let maybe_gc () = if !gc_mode then Gc.compact ()

(* {1 Shim} *)

module Shim = struct
  type crate = Rust.Crate.t

  let with_crate (c : crate) f = Rust.Crate.with_crate c f

  let span : Meta.span =
    let loc : Meta.loc = { line = 1; col = 0 } in
    let file : Meta.file =
      { name = NotReal "synthetic"; crate_name = "synthetic"; contents = None }
    in
    {
      data = { file; beg_loc = loc; end_loc = loc };
      generated_from_span = None;
    }

  let attr_info : Meta.attr_info =
    { attributes = []; inline = None; rename = None; public = true }

  let item_meta name : Types.item_meta =
    {
      name = [ PeIdent (name, Types.Disambiguator.of_int 0) ];
      span;
      source_text = None;
      attr_info;
      is_local = true;
      opacity = Transparent;
      lang_item = None;
      diagnostic_item = None;
    }

  let mk_decl id name kind : Types.type_decl =
    {
      def_id = Types.TypeDeclId.of_int id;
      item_meta = item_meta name;
      generics = TypesUtils.empty_generic_params;
      src = NormalType;
      kind;
      layout = [];
      ptr_metadata = NoMetadata;
    }

  let mk_field name field_ty : Types.field =
    { span; attr_info; field_name = name; is_positional = false; field_ty }

  let mk_variant i name fields disc : Types.variant =
    {
      id = Types.VariantId.of_int i;
      span;
      attr_info;
      variant_name = name;
      fields;
      discriminant = disc;
    }

  let options : GAst.cli_options =
    {
      ullbc = true;
      precise_drops = false;
      mir = None;
      rustc_args = [];
      targets = [];
      sysroot = None;
      monomorphize = false;
      monomorphize_mut = None;
      start_from = [];
      start_from_if_exists = [];
      start_from_attribute = [];
      start_from_pub = false;
      included = [];
      opaque = [];
      exclude = [];
      extract_opaque_bodies = false;
      translate_all_methods = false;
      duplicate_defaulted_methods = false;
      lift_associated_types = [];
      hide_marker_traits = false;
      hide_allocator = false;
      remove_unused_clauses = false;
      remove_unused_self_clauses = false;
      remove_adt_clauses = false;
      desugar_drops = false;
      ops_to_function_calls = false;
      index_to_function_calls = false;
      treat_box_as_builtin = false;
      raw_consts = false;
      consts = None;
      unsized_strings = false;
      reconstruct_fallible_operations = false;
      reconstruct_asserts = false;
      deallocate_all_locals = false;
      unbind_item_vars = false;
      print_original_ullbc = false;
      print_ullbc = false;
      print_built_llbc = false;
      print_llbc = false;
      dest_dir = None;
      dest_file = None;
      no_dedup_serialized_ast = false;
      format = None;
      no_serialize = true;
      skip_borrowck = false;
      no_typecheck = false;
      no_normalize = false;
      no_reorder_decls = false;
      abort_on_error = false;
      error_on_warnings = false;
      preset = None;
    }

  (** A crate with the given type declarations and target pointer size. *)
  let mk_crate ~pointer_size (decls : Types.type_decl list) : crate =
    let type_decls =
      List.fold_left
        (fun m (d : Types.type_decl) -> Types.TypeDeclId.Map.add d.def_id d m)
        Types.TypeDeclId.Map.empty decls
    in
    {
      name = "synthetic";
      options;
      target_information =
        [
          ( "synthetic-target",
            {
              GAst.target_pointer_size = pointer_size;
              is_little_endian = true;
              c_enum_min_size = 4;
              primitive_alignments = [];
            } );
        ];
      item_names =
        List.map
          (fun (d : Types.type_decl) ->
            (Types.IdType d.def_id, d.item_meta.name))
          decls;
      assoc_item_names = Types.TraitDeclId.Map.empty;
      short_names = [];
      declarations = [];
      type_decls;
      fun_decls = Types.FunDeclId.Map.empty;
      global_decls = Types.GlobalDeclId.Map.empty;
      trait_decls = Types.TraitDeclId.Map.empty;
      trait_impls = Types.TraitImplId.Map.empty;
    }
end

(* {1 Shapes} *)

type shape =
  | Int of Types.literal_type
  | Flt of Types.float_type
  | Thin
  | Full
  | Poly of int
  | Tup of shape list
  | Arr of shape * int
  | Enm of int
  | Uni of int

let u8 = Int (TUInt U8)
let u32 = Int (TUInt U32)
let usz = Int (TUInt Usize)
let i32 = Int (TInt I32)
let i64 = Int (TInt I64)
let f32 = Flt F32
let f64 = Flt F64

(* synthetic ADTs: enums (decl ids 1..), structs (11..), unions (21..) *)
let structs = [| [ u8; f64 ]; [ u32; Full; Int TBool ]; [ i64 ] |]

let enums =
  [|
    ("Opt", [ ("None", []); ("Some", [ u32 ]); ("Pair", [ u8; Full ]) ]);
    ( "Shape",
      [
        ("Circle", [ f32 ]);
        ("Rect", [ u32; u32 ]);
        ("Nest", [ Tup [ u8; f64 ] ]);
        ("Arr", [ Arr (u8, 3) ]);
      ] );
    ("Unit", [ ("A", []); ("B", []); ("C", []) ]);
    ("Outer", [ ("Wrap", [ Enm 0 ]); ("Bare", [ Int TBool; i64 ]) ]);
  |]

let unions = [| [ u32; f32 ]; [ u8; Tup [ u32; Full; Int TBool ] ] |]

let decl_ref id : Types.type_decl_ref =
  {
    id = Types.TypeDeclId.of_int id;
    generics = TypesUtils.empty_generic_args;
    builtin = None;
  }

let enum_ref k = decl_ref (1 + k)
let struct_ref j = decl_ref (11 + j)
let union_ref k = decl_ref (21 + k)

let struct_index s =
  let rec go j =
    if j >= Array.length structs then failwith "no such struct"
    else if Tup structs.(j) = s then j
    else go (j + 1)
  in
  go 0

let rec rty : shape -> Types.ty = function
  | Int l -> TLiteral l
  | Flt f -> TLiteral (TFloat f)
  | Full -> TRawPtr (TLiteral (TUInt U8), RMut)
  | Tup _ as s -> TAdt (struct_ref (struct_index s))
  | Arr (s, n) ->
      TArray
        ( rty s,
          {
            kind = CLiteral (VScalar (UnsignedScalar (Usize, Z.of_int n)));
            ty = TLiteral (TUInt Usize);
          } )
  | Enm k -> TAdt (enum_ref k)
  | Uni k -> TAdt (union_ref k)
  | Poly k -> TVar (Free (Types.TypeVarId.of_int k))
  | Thin -> failwith "rty: thin pointer"

let synthetic_decls () =
  let fields l =
    List.mapi (fun i s -> Shim.mk_field (Printf.sprintf "f%d" i) (rty s)) l
  in
  let structs =
    Array.to_list
      (Array.mapi
         (fun j s ->
           Shim.mk_decl (11 + j) (Printf.sprintf "S%d" j) (Struct (fields s)))
         structs)
  in
  let enums =
    Array.to_list
      (Array.mapi
         (fun k (name, vars) ->
           let variants =
             List.mapi
               (fun i (vn, fs) ->
                 let disc : Values.literal =
                   if k mod 2 = 0 then
                     VScalar (UnsignedScalar (U32, Z.of_int (i * 7)))
                   else VScalar (SignedScalar (Isize, Z.of_int ((i * 3) - 1)))
                 in
                 Shim.mk_variant i vn (fields fs) disc)
               vars
           in
           Shim.mk_decl (1 + k) name (Enum variants))
         enums)
  in
  let unions =
    Array.to_list
      (Array.mapi
         (fun k s ->
           Shim.mk_decl (21 + k) (Printf.sprintf "U%d" k) (Union (fields s)))
         unions)
  in
  enums @ structs @ unions

let crate64 = lazy (Shim.mk_crate ~pointer_size:8 (synthetic_decls ()))
let crate32 = lazy (Shim.mk_crate ~pointer_size:4 (synthetic_decls ()))

(* {1 Random generation} *)

let rng = ref (Random.State.make [| 0 |])
let rint n = Random.State.int !rng n
let pick a = a.(rint (Array.length a))
let chance n = rint 100 < n

let zs =
  [|
    0;
    1;
    2;
    3;
    7;
    42;
    100;
    127;
    128;
    255;
    256;
    1000;
    65535;
    -1;
    -2;
    -128;
    1000000;
  |]

let floats = [| "0.0"; "1.5"; "-2.25"; "3.0e10"; "0.1"; "1.0"; "-0.5" |]

let lits : Types.literal_type array =
  [|
    TInt I8;
    TInt I16;
    TInt I32;
    TInt I64;
    TInt I128;
    TInt Isize;
    TUInt U8;
    TUInt U16;
    TUInt U32;
    TUInt U64;
    TUInt U128;
    TUInt Usize;
    TBool;
    TChar;
  |]

let next_var = ref 0

(* replacement value of each variable, for eval/subst *)
let repl : (int, Ty.Svalue.t) Hashtbl.t = Hashtbl.create 97

let rtag () =
  match rint 3 with
  | 0 -> None
  | 1 -> Some Ptr_tag.zero
  | _ -> Some (Ptr_tag.fresh_tag ())

let rec gen_conc : shape -> v = function
  | Int l -> Ty.cast (BV.mki_lit l (pick zs))
  | Flt f -> Ty.cast (Fl.mk f (pick floats))
  | Thin -> Ty.cast (gen_thin_conc ())
  | Full -> Ty.cast (gen_full_conc ())
  | Poly k -> Ty.cast (Adt.mk_poly (Types.TypeVarId.of_int k))
  | Tup ss -> Ty.cast (Adt.mk_tuple (List.map gen_conc ss))
  | Arr (s, n) ->
      Ty.cast (Adt.mk_array (rty_opt s) (Iarray.init n (fun _ -> gen_conc s)))
  | Enm k -> gen_enum gen_conc k
  | Uni k -> gen_union gen_conc k

and rty_opt s = try rty s with _ -> TLiteral (TUInt U8)

and gen_thin_conc () =
  Ptr.mk_ptr_t
    ~loc:(Ptr.loc_of_int (rint 5))
    ~ofs:(BV.usizei (pick [| 0; 4; 8 |]))
    ~size:(BV.usizei (pick [| 8; 16; 64 |]))
    ~align:(BV.usizeinz (pick [| 1; 2; 4; 8 |]))
    ~tag:(rtag ())

and gen_full_conc () =
  match rint 3 with
  | 0 -> Ptr.mk_ptr_f_opt (gen_thin_conc ()) None
  | 1 ->
      Ptr.mk_ptr_f_opt (gen_thin_conc ())
        (Some (BV.usizei (pick [| 0; 3; 10 |])))
  | _ -> Ptr.mk_ptr_f_opt (gen_thin_conc ()) (Some (gen_thin_conc ()))

and gen_enum : (shape -> v) -> int -> v =
 fun g k ->
  let _, vars = enums.(k) in
  let vi = rint (List.length vars) in
  let _, fs = List.nth vars vi in
  Ty.cast (Adt.mk_enum (enum_ref k) (Types.VariantId.of_int vi) (List.map g fs))

and gen_union : (shape -> v) -> int -> v =
 fun g k ->
  let fs = unions.(k) in
  let blocks =
    List.mapi
      (fun i s ->
        let value =
          match s with
          | Tup _ -> Ty.Aggregate (Ty.cast (g s), rty s)
          | _ -> Ty.Scalar (Ty.cast (g s))
        in
        {
          Ty.value;
          offset = BV.usizei (4 * i);
          size = BV.usizeinz (4 * (i + 1));
        })
      fs
  in
  Ty.cast (Adt.mk_union (union_ref k) blocks)

let rec uty : shape -> Ty.Svalue.ty = function
  | Int l -> Ty.untype_type (Ty.t_lit l)
  | Flt f -> Ty.untype_type (Ty.t_float f)
  | Thin -> Ty.untype_type (Ty.t_ptr_t ())
  | Full -> Ty.untype_type (Ty.t_ptr_f ())
  | Enm k -> Ty.untype_type (Ty.t_enum (enum_ref k))
  | s -> Ty.get_ty (gen_conc s)

and fresh_var (s : shape) : v =
  let id = !next_var in
  incr next_var;
  let var = Ty.mk_var (Var.of_int id) (Ty.type_type (uty s)) in
  Hashtbl.replace repl id (Ty.untyped (gen_conc s));
  var

let rec gen ?(p = 40) (s : shape) : v =
  let sym = chance p in
  match s with
  | Int l ->
      if sym then
        let x = fresh_var s in
        match rint 4 with
        | 0 -> x
        | 1 -> Ty.cast (BV.add (Ty.cast x) (BV.mki_lit l 1))
        | 2 ->
            Ty.cast
              (BV.mul ~checked:Ty.checked_both (Ty.cast x)
                 (Ty.cast (gen_conc s)))
        | _ -> Ty.cast (BV.and_ (Ty.cast x) (Ty.cast (gen_conc s)))
      else gen_conc s
  | Flt _ ->
      if sym then
        let x = fresh_var s in
        match rint 3 with
        | 0 -> x
        | 1 -> Ty.cast (Fl.add (Ty.cast x) (Ty.cast (gen_conc s)))
        | _ -> Ty.cast (Fl.neg (Ty.cast x))
      else gen_conc s
  | Thin ->
      if sym then
        match rint 4 with
        | 0 -> fresh_var s
        | 1 -> Ty.cast (Ptr.add_ofs (Ty.cast (fresh_var s)) (BV.usizei 4))
        | 2 ->
            (* concrete location, symbolic offset *)
            Ty.cast
              (Ptr.mk_ptr_t ~loc:(Ptr.loc_of_int 1)
                 ~ofs:(Ty.cast (fresh_var usz))
                 ~size:(BV.usizei 16) ~align:(BV.usizeinz 4) ~tag:(rtag ()))
        | _ ->
            Ty.cast
              (Ptr.mk_ptr_t ~loc:(Ptr.loc_of_int 2) ~ofs:(BV.usizei 0)
                 ~size:(Ty.cast (fresh_var usz))
                 ~align:(BV.usizeinz 8) ~tag:None)
      else gen_conc s
  | Full ->
      if sym && chance 50 then fresh_var s
      else
        let thin = Ty.cast (gen ~p Thin) in
        Ty.cast
          (match rint 3 with
          | 0 -> Ptr.mk_ptr_f_opt thin None
          | 1 -> Ptr.mk_ptr_f_opt thin (Some (Ty.cast (gen ~p usz)))
          | _ -> Ptr.mk_ptr_f_opt thin (Some (Ty.cast (gen ~p Thin))))
  | Poly _ -> gen_conc s
  | Tup ss ->
      if sym && chance 30 then fresh_var s
      else Ty.cast (Adt.mk_tuple (List.map (gen ~p) ss))
  | Arr (e, n) ->
      if sym && chance 30 then fresh_var s
      else
        Ty.cast (Adt.mk_array (rty_opt e) (Iarray.init n (fun _ -> gen ~p e)))
  | Enm k -> if sym && chance 30 then fresh_var s else gen_enum (gen ~p) k
  | Uni k -> gen_union (gen ~p) k

let rec rand_shape ~crate depth : shape =
  let leaf () =
    match rint 5 with
    | 0 -> Int (pick lits)
    | 1 -> Flt (pick [| Values.F16; F32; F64; F128 |])
    | 2 -> Thin
    | 3 -> Full
    | _ -> u32
  in
  if depth = 0 then leaf ()
  else
    match rint (if crate then 8 else 6) with
    | 0 | 1 -> leaf ()
    | 2 | 3 -> Tup (List.init (rint 4) (fun _ -> rand_shape ~crate (depth - 1)))
    | 4 ->
        let e = rand_shape ~crate (depth - 1) in
        Arr ((if e = Thin then u8 else e), 1 + rint 3)
    | 5 -> Poly (rint 3)
    | 6 -> Enm (rint (Array.length enums))
    | _ -> Uni (rint (Array.length unions))

(* {1 Encoding} *)

let decl_log : string list ref = ref []
let decl_seen : (string, unit) Hashtbl.t = Hashtbl.create 17
let decl_defs : (string * string list) list ref = ref []

let rec with_log : 'a. (unit -> 'a) -> 'a =
 fun f ->
  match f () with
  | r -> r
  | effect Decls.Declare d, k ->
      record d;
      Effect.Deep.continue k ()

and record (d : Decls.t) =
  if not (Hashtbl.mem decl_seen d.key) then begin
    Hashtbl.add decl_seen d.key ();
    let cmds = with_log (fun () -> Iter.to_list d.commands) in
    decl_defs := (d.key, List.map Smt.to_string cmds) :: !decl_defs
  end;
  decl_log := d.key :: !decl_log

let rec sort_of_ty ty = L.encode_ty ~sort_of_ty ty
let memo : (Smt.sexp * Decls.t list) L.Hashtbl.t = L.Hashtbl.create 1023

let rec encode_value (v : L.t) =
  L.encode_node ~sort_of_ty ~encode_child:encode_value_memo v

and encode_value_memo v =
  match L.Hashtbl.find_opt memo v with
  | Some (k, decls) ->
      List.iter (fun d -> Effect.perform (Decls.Declare d)) decls;
      k
  | None ->
      let decls = ref [] in
      let k =
        try encode_value v
        with effect Decls.Declare d, cont ->
          decls := d :: !decls;
          Effect.perform (Decls.Declare d);
          Effect.Deep.continue cont ()
      in
      L.Hashtbl.add memo v (k, List.rev !decls);
      k

let encode (v : _ Ty.t) =
  decl_log := [];
  let k = with_log (fun () -> encode_value_memo (Ty.untyped v)) in
  (Smt.to_string k, List.rev !decl_log)

(* {1 Observation} *)

let vars_of v =
  let acc = ref [] in
  Ty.iter_vars v (fun (x, ty) ->
      acc := Fmt.str "%a:%s" Var.pp x (ppty ty) :: !acc);
  List.rev !acc

let eval_with ~force v =
  Eval.eval ~force
    ~eval_var:(fun sv x _ ->
      if Var.to_int x mod 2 = 0 then
        match Hashtbl.find_opt repl (Var.to_int x) with
        | Some r -> r
        | None -> sv
      else sv)
    (Ty.untyped v)

let subst_apply v =
  let s = ref Expr.Subst.empty in
  Ty.iter_vars v (fun (x, ty) ->
      if Var.to_int x mod 3 = 0 then
        match Hashtbl.find_opt repl (Var.to_int x) with
        | Some r -> (
            match
              Expr.Subst.learn !s (Ty.untyped (Ty.mk_var x ty)) (Ty.type_ r)
            with
            | Some s' -> s := s'
            | None -> ())
        | None -> ());
  let r, _ =
    Expr.Subst.apply
      ~missing_var:(fun x ty ->
        Ty.mk_var (Var.of_int (Var.to_int x + 100000)) ty)
      !s (Ty.untyped v)
  in
  ppa r

let learn_line (e : _ Ty.t) (target : _ Ty.t) =
  match Expr.Subst.learn Expr.Subst.empty (Ty.untyped e) target with
  | None -> "None"
  | Some s ->
      let r, _ =
        Expr.Subst.apply
          ~missing_var:(fun _ _ -> raise Not_found)
          s (Ty.untyped e)
      in
      "Some -> " ^ ppa r

let op name f = pr "  %s: %s" name (guard f)

let observe label (v : _ Ty.t) =
  retain v;
  pr "== %s" label;
  pr "  v: %s" (ppa v);
  op "ty" (fun () -> ppty (Ty.type_type (Ty.get_ty v)));
  (match vars_of v with [] -> () | l -> pr "  vars: %s" (String.concat " " l));
  op "cost" (fun () -> string_of_int (L.cost (Ty.untyped v)));
  let same r = if Ty.Svalue.equal r (Ty.untyped v) then "=" else ppu r in
  if vars_of v <> [] then op "eval" (fun () -> same (eval_with ~force:false v));
  op "evalf" (fun () -> same (eval_with ~force:true v));
  (match vars_of v with [] -> () | _ -> op "subst" (fun () -> subst_apply v));
  op "smt" (fun () ->
      let s, ds = encode v in
      Printf.sprintf "%s  decls=[%s]" s (String.concat "," ds))

(* shape-directed operations *)

let show_list l = "[" ^ String.concat "; " l ^ "]"
let show_block (b : Ty.block) = to_s Ty.pp_block b

let ops (s : shape) (v : v) =
  match s with
  | Tup ss ->
      let n = List.length ss in
      op "as_tuple" (fun () ->
          show_list (List.map ppa (Adt.as_tuple (Ty.cast v))));
      List.iteri
        (fun i s' ->
          op (Printf.sprintf "field_of %d" i) (fun () ->
              ppa (Adt.field_of i (Ty.cast v)));
          op (Printf.sprintf "set_field %d" i) (fun () ->
              ppa (Adt.set_field i (gen_conc s') (Ty.cast v)));
          if i = 0 then
            op "update_field 0 (fun x -> x)" (fun () ->
                ppa (Adt.update_field 0 (fun x -> x) (Ty.cast v))))
        ss;
      op (Printf.sprintf "field_of %d (out of range)" n) (fun () ->
          ppa (Adt.field_of n (Ty.cast v)));
      op "set_field -1 (out of range)" (fun () ->
          ppa (Adt.set_field (-1) (gen_conc u8) (Ty.cast v)));
      (match n with
      | 1 -> op "as_tuple1" (fun () -> ppa (Adt.as_tuple1 (Ty.cast v)))
      | 2 ->
          op "as_tuple2" (fun () ->
              let a, b = Adt.as_tuple2 (Ty.cast v) in
              ppa a ^ " , " ^ ppa b)
      | 3 ->
          op "as_tuple3" (fun () ->
              let a, b, c = Adt.as_tuple3 (Ty.cast v) in
              ppa a ^ " , " ^ ppa b ^ " , " ^ ppa c)
      | _ ->
          op "as_tuple1 (wrong arity)" (fun () ->
              ppa (Adt.as_tuple1 (Ty.cast v))));
      op "cast_tuple" (fun () -> ppa (Ty.cast_tuple v));
      op "cast_array (wrong kind)" (fun () -> ppa (Ty.cast_array v))
  | Arr (e, n) ->
      op "as_array" (fun () ->
          show_list (List.map ppa (Iarray.to_list (Adt.as_array (Ty.cast v)))));
      for i = 0 to min n 3 - 1 do
        op (Printf.sprintf "array_field_of %d" i) (fun () ->
            ppa (Adt.array_field_of i (Ty.cast v)));
        op (Printf.sprintf "set_array_field %d" i) (fun () ->
            ppa (Adt.set_array_field i (gen_conc e) (Ty.cast v)))
      done;
      op (Printf.sprintf "array_field_of %d (out of range)" n) (fun () ->
          ppa (Adt.array_field_of n (Ty.cast v)));
      op "set_array_field out of range" (fun () ->
          ppa (Adt.set_array_field n (gen_conc e) (Ty.cast v)));
      op "update_array_field 0" (fun () ->
          ppa (Adt.update_array_field 0 (fun x -> x) (Ty.cast v)));
      op "cast_array" (fun () -> ppa (Ty.cast_array v));
      op "cast_tuple" (fun () -> ppa (Ty.cast_tuple v))
  | Thin ->
      let p : T.sptr_t Ty.t = Ty.cast v in
      op "loc" (fun () -> ppa (Ptr.loc p));
      op "ofs" (fun () -> ppa (Ptr.ofs p));
      op "decompose" (fun () ->
          let l, o = Ptr.decompose p in
          ppa l ^ " , " ^ ppa o);
      op "size_of" (fun () -> ppa (Ptr.size_of p));
      op "align_of" (fun () -> ppa (Ptr.align_of p));
      op "allocation_info" (fun () ->
          let a, b = Ptr.allocation_info p in
          ppa a ^ " , " ^ ppa b);
      op "tag_of" (fun () ->
          match Ptr.tag_of p with
          | None -> "None"
          | Some t -> "Some " ^ Ptr_tag.show t);
      op "is_null" (fun () -> ppa (Ptr.is_null p));
      op "is_at_null_loc" (fun () -> ppa (Ptr.is_at_null_loc p));
      op "has_provenance" (fun () -> ppa (Ptr.has_provenance p));
      op "in_bound" (fun () -> ppa (Ptr.in_bound p));
      op "as_id" (fun () -> ppa (Ptr.as_id p));
      op "add_ofs 4" (fun () -> ppa (Ptr.add_ofs p (BV.usizei 4)));
      op "set_ofs 12" (fun () -> ppa (Ptr.set_ofs p (BV.usizei 12)));
      op "with_tag zero" (fun () -> ppa (Ptr.with_tag p (Some Ptr_tag.zero)));
      op "with_tag none" (fun () -> ppa (Ptr.with_tag p None));
      op "same_prov self" (fun () -> ppa (Ptr.have_same_provenance p p));
      op "of_ptr_t" (fun () -> ppa (Ptr.of_ptr_t p));
      op "cast_ptr_t" (fun () -> ppa (Ty.cast_ptr_t v));
      op "cast_ptr_f (wrong kind)" (fun () -> ppa (Ty.cast_ptr_f v))
  | Full ->
      let p : T.sptr_f Ty.t = Ty.cast v in
      op "ptr_of" (fun () -> ppa (Ptr.ptr_of p));
      op "len_meta" (fun () -> ppa (Ptr.len_meta p));
      op "vtable_meta" (fun () -> ppa (Ptr.vtable_meta p));
      op "with_ptr null" (fun () -> ppa (Ptr.with_ptr p (Ptr.null ())));
      op "with_ptr self" (fun () -> ppa (Ptr.with_ptr p (Ptr.ptr_of p)));
      op "cast_ptr_f" (fun () -> ppa (Ty.cast_ptr_f v));
      op "cast_ptr_t (wrong kind)" (fun () -> ppa (Ty.cast_ptr_t v))
  | Poly _ ->
      op "as_type_var" (fun () ->
          Fmt.str "%a" Types.pp_type_var_id (Adt.as_type_var (Ty.cast v)))
  | Enm k ->
      let name, vars = enums.(k) in
      ignore name;
      List.iteri
        (fun vi (_, fs) ->
          let vid = Types.VariantId.of_int vi in
          op (Printf.sprintf "is_variant %d" vi) (fun () ->
              ppa (Adt.is_variant vid (Ty.cast v)));
          op (Printf.sprintf "as_enum_of_variant %d" vi) (fun () ->
              show_list (List.map ppa (Adt.as_enum_of_variant vid (Ty.cast v))));
          List.iteri
            (fun i s' ->
              op (Printf.sprintf "field_of_variant %d %d" vi i) (fun () ->
                  ppa (Adt.field_of_variant vid i (Ty.cast v)));
              op (Printf.sprintf "set_field_of_variant %d %d" vi i) (fun () ->
                  ppa (Adt.set_field_of_variant vid i (gen_conc s') (Ty.cast v))))
            fs)
        vars;
      op "discriminant_of" (fun () -> ppa (Adt.discriminant_of (Ty.cast v)));
      op "cast_enum" (fun () -> ppa (Ty.cast_enum v));
      op "cast_enum ~adt" (fun () -> ppa (Ty.cast_enum ~adt:(enum_ref k) v));
      op "cast_enum ~adt (wrong adt)" (fun () ->
          ppa (Ty.cast_enum ~adt:(enum_ref ((k + 1) mod Array.length enums)) v));
      op "cast_union (wrong kind)" (fun () -> ppa (Ty.cast_union v))
  | Uni k ->
      op "as_union" (fun () ->
          show_list (List.map show_block (Adt.as_union (Ty.cast v))));
      op "cast_union ~adt" (fun () -> ppa (Ty.cast_union ~adt:(union_ref k) v));
      op "cast_enum (wrong kind)" (fun () -> ppa (Ty.cast_enum v))
  | Int _ | Flt _ -> ()

(* learn *)
let learn_ops (s : shape) (v : v) =
  match s with
  | Tup _ | Arr _ | Full | Thin | Enm _ ->
      op "learn vs concrete" (fun () -> learn_line v (gen_conc s));
      op "learn vs symbolic" (fun () -> learn_line v (fresh_var s))
  | _ -> ()

let ops_enabled = ref true

let full ?(learn = true) ?(with_ops = true) label (s : shape) (v : v) =
  observe label v;
  if with_ops && !ops_enabled then ops s v;
  if learn then learn_ops s v

let section name = pr "\n##### %s" name

(* {1 Stanzas} *)

let scalars () =
  section "scalars";
  Array.iter
    (fun l ->
      let c = gen_conc (Int l) in
      full ("conc " ^ lit_name l) (Int l) c;
      let x = fresh_var (Int l) in
      full ("var " ^ lit_name l) (Int l) x)
    lits;
  List.iter
    (fun f ->
      let name = lit_name (TFloat f) in
      List.iter
        (fun s -> observe (Printf.sprintf "float %s %s" name s) (Fl.mk f s))
        (Array.to_list floats);
      observe ("zero " ^ name) (Fl.zero f);
      observe ("neg_zero " ^ name) (Fl.neg_zero f);
      observe ("one " ^ name) (Fl.one f);
      observe ("infinity " ^ name) (Fl.infinity f);
      observe ("neg_infinity " ^ name) (Fl.neg_infinity f);
      observe ("nan " ^ name) (Fl.nan f);
      observe ("of_z 7 " ^ name) (Fl.of_z f (Z.of_int 7));
      full ("var " ^ name) (Flt f) (fresh_var (Flt f));
      op "fp_of" (fun () ->
          name ^ " -> " ^ lit_name (TFloat (Fl.fp_of (Fl.one f)))))
    [ Values.F16; F32; F64; F128 ]

let arithmetic () =
  section "bit-vector and float arithmetic (shared part)";
  let x : T.sint Ty.t = Ty.cast (fresh_var u32) in
  let y : T.sint Ty.t = Ty.cast (fresh_var u32) in
  let z : T.sint Ty.t = Ty.cast (fresh_var u32) in
  let s : T.sint Ty.t = Ty.cast (fresh_var i32) in
  let a : T.sint Ty.t = Ty.cast (fresh_var u8) in
  let b : T.sbool Ty.t = Ty.cast (fresh_var (Int TBool)) in
  let b2 : T.sbool Ty.t = BV.to_bool (Ty.cast (fresh_var (Int TBool))) in
  let fx : T.sfloat Ty.t = Ty.cast (fresh_var f32) in
  let fy : T.sfloat Ty.t = Ty.cast (fresh_var f32) in
  let fd : T.sfloat Ty.t = Ty.cast (fresh_var f64) in
  let c n : T.sint Ty.t = BV.mki 32 n in
  let nz n : T.nonzero Ty.t = BV.mki_nz 32 n in
  let rne = Ty.RoundingMode.NearestTiesToEven in
  let items : (string * (unit -> v)) list =
    [
      ("x + y", fun () -> Ty.cast (BV.add x y));
      ("y + x", fun () -> Ty.cast (BV.add y x));
      ("x + y checked", fun () -> Ty.cast (BV.add ~checked:Ty.checked_both x y));
      ("x - y", fun () -> Ty.cast (BV.sub x y));
      ("x - x", fun () -> Ty.cast (BV.sub x x));
      ("x * y", fun () -> Ty.cast (BV.mul x y));
      ("x * 1", fun () -> Ty.cast (BV.mul x (c 1)));
      ("x * 0", fun () -> Ty.cast (BV.mul x (c 0)));
      ("x + 0", fun () -> Ty.cast (BV.add x (c 0)));
      ( "(x + 3) + 4",
        fun () -> Ty.cast (BV.add (Ty.cast (BV.add x (c 3))) (c 4)) );
      ("5 + 7", fun () -> Ty.cast (BV.add (c 5) (c 7)));
      ("x / 3", fun () -> Ty.cast (BV.div ~signed:false x (nz 3)));
      ("s /$ 3", fun () -> Ty.cast (BV.div ~signed:true s (BV.mki_nz 32 3)));
      ("x % 3", fun () -> Ty.cast (BV.rem ~signed:false x (nz 3)));
      ("x mod y", fun () -> Ty.cast (BV.mod_ x y));
      ("neg x", fun () -> Ty.cast (BV.neg x));
      ("neg s checked", fun () -> Ty.cast (BV.neg ~checked:true s));
      ( "add_overflows x y",
        fun () -> Ty.cast (BV.add_overflows ~signed:false x y) );
      ( "mul_overflows s y",
        fun () -> Ty.cast (BV.mul_overflows ~signed:true s y) );
      ( "sub_overflows x x",
        fun () -> Ty.cast (BV.sub_overflows ~signed:false x x) );
      ("neg_overflows s", fun () -> Ty.cast (BV.neg_overflows s));
      ( "add_checked x y",
        fun () ->
          let r, o = BV.add_checked ~signed:false x y in
          Ty.cast (Adt.mk_tuple [ Ty.cast r; Ty.cast o ]) );
      ("x < y", fun () -> Ty.cast (BV.lt ~signed:false x y));
      ("x <= y signed", fun () -> Ty.cast (BV.leq ~signed:true x y));
      ("x < x", fun () -> Ty.cast (BV.lt ~signed:false x x));
      ("x > y", fun () -> Ty.cast (BV.gt ~signed:false x y));
      ("x >= 0", fun () -> Ty.cast (BV.geq ~signed:false x (c 0)));
      ("concat x y", fun () -> Ty.cast (BV.concat x y));
      ("extend 32 x", fun () -> Ty.cast (BV.extend ~signed:false 32 x));
      ("extend 32 s signed", fun () -> Ty.cast (BV.extend ~signed:true 32 s));
      ("extract 0 7 x", fun () -> Ty.cast (BV.extract 0 7 x));
      ( "extract 8 15 (concat x y)",
        fun () -> Ty.cast (BV.extract 8 15 (BV.concat x y)) );
      ("x & y", fun () -> Ty.cast (BV.and_ x y));
      ("x & x", fun () -> Ty.cast (BV.and_ x x));
      ("x | y", fun () -> Ty.cast (BV.or_ x y));
      ("x ^ y", fun () -> Ty.cast (BV.xor x y));
      ("x ^ x", fun () -> Ty.cast (BV.xor x x));
      ("x << 3", fun () -> Ty.cast (BV.shl x (c 3)));
      ("x >> y", fun () -> Ty.cast (BV.lshr x y));
      ("s >>> 2", fun () -> Ty.cast (BV.ashr s (c 2)));
      ("!x", fun () -> Ty.cast (BV.not x));
      ("!!x", fun () -> Ty.cast (BV.not (BV.not x)));
      ("of_bool 8 b", fun () -> Ty.cast (BV.of_bool b));
      ("to_bool a", fun () -> Ty.cast (BV.to_bool a));
      ("not_bool a", fun () -> Ty.cast (BV.not_bool a));
      ("ite b x y", fun () -> Ty.cast (Ty.ite b x y));
      ("ite b x x", fun () -> Ty.cast (Ty.ite b x x));
      ("ite true x y", fun () -> Ty.cast (Ty.ite Ty.v_true x y));
      ("x == y", fun () -> Ty.cast (Ty.sem_eq x y));
      ("x == x", fun () -> Ty.cast (Ty.sem_eq x x));
      ("x == 3", fun () -> Ty.cast (Ty.sem_eq x (c 3)));
      ("b && b2", fun () -> Ty.cast (Ty.and_ b b2));
      ("b && !b", fun () -> Ty.cast (Ty.and_ b (Ty.not b)));
      ("b || !b", fun () -> Ty.cast (Ty.or_ b (Ty.not b)));
      ("conj [b; b2; b]", fun () -> Ty.cast (Ty.conj [ b; b2; b ]));
      ("distinct [x;y;z]", fun () -> Ty.cast (Ty.distinct [ x; y; z ]));
      ("distinct [x;y;x]", fun () -> Ty.cast (Ty.distinct [ x; y; x ]));
      ( "exists z. z < x",
        fun () ->
          Ty.cast
            (Ty.exists_1 ~not_in:x (Ty.t_int 32) (fun z' ->
                 BV.lt ~signed:false z' x)) );
      ( "exists z w. z < w && w < y",
        fun () ->
          Ty.cast
            (Ty.exists_2 ~not_in:y (Ty.t_int 32) (Ty.t_int 32) (fun z' w' ->
                 Ty.and_ (BV.lt ~signed:false z' w') (BV.lt ~signed:false w' y)))
      );
      ("fx + fy", fun () -> Ty.cast (Fl.add fx fy));
      ("fx + fx", fun () -> Ty.cast (Fl.add fx fx));
      ("fx - fy", fun () -> Ty.cast (Fl.sub fx fy));
      ("fx * 2.0", fun () -> Ty.cast (Fl.mul fx (Fl.mk F32 "2.0")));
      ("fx / fy", fun () -> Ty.cast (Fl.div fx fy));
      ("fx + nan", fun () -> Ty.cast (Fl.add fx (Fl.nan F32)));
      ( "1.5 + 2.25",
        fun () -> Ty.cast (Fl.add (Fl.mk F32 "1.5") (Fl.mk F32 "2.25")) );
      ("1.0 / 0.0", fun () -> Ty.cast (Fl.div (Fl.one F64) (Fl.zero F64)));
      ("-fx", fun () -> Ty.cast (Fl.neg fx));
      ("--fx", fun () -> Ty.cast (Fl.neg (Fl.neg fx)));
      ("abs fx", fun () -> Ty.cast (Fl.abs fx));
      ("sqrt fx", fun () -> Ty.cast (Fl.sqrt fx));
      ("sqrt 4.0", fun () -> Ty.cast (Fl.sqrt (Fl.mk F64 "4.0")));
      ("fma fx fy fx", fun () -> Ty.cast (Fl.fma fx fy fx));
      ("min fx fy", fun () -> Ty.cast (Fl.min fx fy));
      ("maximum fx fy", fun () -> Ty.cast (Fl.maximum fx fy));
      ("round fx", fun () -> Ty.cast (Fl.round Ty.RoundingMode.Ceil fx));
      ("fx == fy", fun () -> Ty.cast (Fl.eq fx fy));
      ("fx < fy", fun () -> Ty.cast (Fl.lt fx fy));
      ("fx <= fx", fun () -> Ty.cast (Fl.leq fx fx));
      ("is_nan fx", fun () -> Ty.cast (Fl.is_nan fx));
      ("is_nan nan", fun () -> Ty.cast (Fl.is_nan (Fl.nan F32)));
      ("is_zero fx", fun () -> Ty.cast (Fl.is_zero fx));
      ("is_negative -0.0", fun () -> Ty.cast (Fl.is_negative (Fl.neg_zero F32)));
      ("cast f32->f64", fun () -> Ty.cast (Fl.cast ~rounding:rne ~fp:F64 fx));
      ("cast f64->f32", fun () -> Ty.cast (Fl.cast ~rounding:rne ~fp:F32 fd));
      ( "to_float x f32",
        fun () -> Ty.cast (BV.to_float ~rounding:rne ~signed:false ~fp:F32 x) );
      ( "of_float fx i32",
        fun () ->
          Ty.cast (BV.of_float ~rounding:Truncate ~signed:true ~size:32 fx) );
      ("to_float_raw x", fun () -> Ty.cast (BV.to_float_raw x));
      ( "to_bits 1.5",
        fun () -> Ty.cast (Option.get (Fl.to_bits_opt (Fl.mk F32 "1.5"))) );
    ]
  in
  List.iter
    (fun (name, f) ->
      match f () with
      | v -> observe name v
      | exception e -> pr "== %s\n  EXN %s" name (squash (exn_str e)))
    items

let thin_pointers () =
  section "thin pointers";
  let tagA = Ptr_tag.fresh_tag () in
  let tagB = Ptr_tag.fresh_tag () in
  pr "tags: %s %s %s (zero)" (Ptr_tag.show tagA) (Ptr_tag.show tagB)
    (Ptr_tag.show Ptr_tag.zero);
  let mk ?(loc = Ptr.loc_of_int 3) ?(ofs = BV.usizei 8) ?(size = BV.usizei 32)
      ?(align = BV.usizeinz 4) tag =
    Ptr.mk_ptr_t ~loc ~ofs ~size ~align ~tag
  in
  let items =
    [
      ("no tag", mk None);
      ("tag A", mk (Some tagA));
      ("tag B", mk (Some tagB));
      ("tag zero", mk (Some Ptr_tag.zero));
      ("null", Ptr.null ());
      ("of_address 16", Ptr.of_address (BV.usizei 16));
      ("null_loc ptr", mk ~loc:(Ptr.null_loc ()) None);
      ("symbolic ofs", mk (Some tagA) ~ofs:(Ty.cast (fresh_var usz)));
      ("symbolic loc", mk None ~loc:(Ty.cast (fresh_var (Int (TUInt Usize)))));
      ( "symbolic size+align",
        mk None
          ~size:(Ty.cast (fresh_var usz))
          ~align:(BV.cast_nonzero (Ty.cast (fresh_var usz))) );
      ("var", Ty.cast (fresh_var Thin));
      ("var + 4", Ptr.add_ofs (Ty.cast (fresh_var Thin)) (BV.usizei 4));
      ( "tagged + 4 + 4",
        Ptr.add_ofs (Ptr.add_ofs (mk (Some tagA)) (BV.usizei 4)) (BV.usizei 4)
      );
      ( "of_raw",
        Ptr.of_raw
          ~ptr:
            (Ty.type_
               (Ty.Svalue.Ptr.mk
                  (Ty.untyped (Ptr.loc_of_int 0))
                  (Ty.untyped (BV.usizei 0))))
          ~size:(BV.usizei 1) ~align:(BV.usizeinz 1) ~tag:(Some tagB) );
    ]
  in
  List.iteri
    (fun i (n, p) -> full ~with_ops:(i mod 3 = 1) n Thin (Ty.cast p))
    items;
  op "same object twice" (fun () ->
      string_of_bool (mk (Some tagA) == mk (Some tagA)));
  op "same object different tag" (fun () ->
      string_of_bool (mk (Some tagA) == mk (Some tagB)));
  op "equal tag A / tag A" (fun () ->
      string_of_bool (Ty.equal (mk (Some tagA)) (mk (Some tagA))));
  op "equal tag A / tag B" (fun () ->
      string_of_bool (Ty.equal (mk (Some tagA)) (mk (Some tagB))));
  op "equal none / tag zero" (fun () ->
      string_of_bool (Ty.equal (mk None) (mk (Some Ptr_tag.zero))));
  op "sem_eq tag A / tag B" (fun () ->
      ppa (Ty.sem_eq (mk (Some tagA)) (mk (Some tagB))));
  op "sem_eq none / tag A" (fun () ->
      ppa (Ty.sem_eq (mk None) (mk (Some tagA))));
  op "sem_eq var / var" (fun () ->
      let p = fresh_var Thin in
      ppa (Ty.sem_eq p p));
  op "sem_eq var / conc" (fun () -> ppa (Ty.sem_eq (fresh_var Thin) (mk None)));
  op "ite b p q" (fun () ->
      let b = Ty.cast (fresh_var (Int TBool)) |> BV.to_bool in
      ppa (Ty.ite b (mk (Some tagA)) (mk None)))

let full_pointers_and_meta () =
  section "full pointers and metadata";
  let thin tag =
    Ptr.mk_ptr_t ~loc:(Ptr.loc_of_int 2) ~ofs:(BV.usizei 0) ~size:(BV.usizei 24)
      ~align:(BV.usizeinz 8) ~tag
  in
  let tg = Some (Ptr_tag.fresh_tag ()) in
  let len = BV.usizei 3 in
  let vt = thin None in
  let items =
    [
      ("full, unit meta", Ptr.of_ptr_t (thin tg));
      ("full, unit meta (no tag)", Ptr.of_ptr_t (thin None));
      ("full, len 3", Ptr.mk_ptr_f (thin tg) len);
      ("full, len symbolic", Ptr.mk_ptr_f (thin None) (Ty.cast (fresh_var usz)));
      ("full, vtable", Ptr.mk_ptr_f (thin tg) vt);
      ( "full, vtable symbolic",
        Ptr.mk_ptr_f (thin tg) (Ty.cast (fresh_var Thin)) );
      ("full opt None", Ptr.mk_ptr_f_opt (thin tg) None);
      ("full opt Some len", Ptr.mk_ptr_f_opt (thin tg) (Some len));
      ("full, symbolic thin, len", Ptr.mk_ptr_f (Ty.cast (fresh_var Thin)) len);
      ("full var", Ty.cast (fresh_var Full));
      ("null_f", Ptr.null_f ());
      ("of_address_f 32", Ptr.of_address_f (BV.usizei 32));
      ( "with_ptr (len 3) null",
        Ptr.with_ptr (Ptr.mk_ptr_f (thin tg) len) (Ptr.null ()) );
      ("with_ptr var thin", Ptr.with_ptr (Ty.cast (fresh_var Full)) (thin tg));
    ]
  in
  List.iteri
    (fun i (n, p) -> full ~with_ops:(i mod 3 = 0) n Full (Ty.cast p))
    items;
  (* metadata of full pointers *)
  List.iter
    (fun (n, p) ->
      op (n ^ ": len_meta") (fun () -> ppa (Ptr.len_meta p));
      op (n ^ ": vtable_meta") (fun () -> ppa (Ptr.vtable_meta p)))
    [
      ("unit", Ptr.of_ptr_t (thin tg));
      ("len", Ptr.mk_ptr_f (thin tg) len);
      ("vtable", Ptr.mk_ptr_f (thin tg) vt);
    ];
  op "mk_ptr_f with bool meta (invalid)" (fun () ->
      ppa (Ptr.mk_ptr_f (thin tg) (Ty.cast (fresh_var (Int TBool)))));
  op "mk_ptr_f len 8-bit meta" (fun () ->
      ppa (Ptr.mk_ptr_f (thin tg) (BV.u8i 3)));
  op "mk_ptr_f_opt on symbolic with meta var" (fun () ->
      ppa
        (Ptr.mk_ptr_f_opt
           (Ty.cast (fresh_var Thin))
           (Some (Ty.cast (fresh_var Thin)))));
  op "same object twice" (fun () ->
      string_of_bool (Ptr.mk_ptr_f (thin tg) len == Ptr.mk_ptr_f (thin tg) len));
  op "sem_eq len3 / len4" (fun () ->
      ppa
        (Ty.sem_eq
           (Ptr.mk_ptr_f (thin tg) len)
           (Ptr.mk_ptr_f (thin tg) (BV.usizei 4))))

let tuples () =
  section "tuples";
  let handmade =
    [
      ("unit", Tup [], Adt.unit);
      ("(u32)", Tup [ u32 ], Adt.mk_tuple [ BV.u32i 1 ]);
      ( "(u8, u32, usize)",
        Tup [ u8; u32; usz ],
        Adt.mk_tuple [ BV.u8i 1; BV.u32i 2; BV.usizei 3 ] );
      ( "(u32, f32, thin)",
        Tup [ u32; f32; Thin ],
        Adt.mk_tuple
          [
            Ty.cast (BV.u32i 9);
            Ty.cast (Fl.mk F32 "1.5");
            Ty.cast (Ptr.null ());
          ] );
      ( "(full, f64, bool)",
        Tup [ Full; f64; Int TBool ],
        Adt.mk_tuple
          [
            Ty.cast (Ptr.null_f ());
            Ty.cast (Fl.mk F64 "-2.25");
            Ty.cast (BV.of_bool Ty.v_true);
          ] );
      ( "((u8,u8),(u32,(f32,full)))",
        Tup [ Tup [ u8; u8 ]; Tup [ u32; Tup [ f32; Full ] ] ],
        Adt.mk_tuple
          [
            Ty.cast (Adt.mk_tuple [ BV.u8i 1; BV.u8i 2 ]);
            Ty.cast
              (Adt.mk_tuple
                 [
                   Ty.cast (BV.u32i 3);
                   Ty.cast
                     (Adt.mk_tuple
                        [
                          Ty.cast (Fl.mk F32 "0.5");
                          Ty.cast (Ptr.of_address_f (BV.usizei 8));
                        ]);
                 ]);
          ] );
      ( "(var, var + 1)",
        Tup [ u32; u32 ],
        let x : T.sint Ty.t = Ty.cast (fresh_var u32) in
        Adt.mk_tuple [ x; Ty.cast (BV.add x (BV.mki 32 1)) ] );
      ( "(poly, u8)",
        Tup [ Poly 0; u8 ],
        Adt.mk_tuple
          [
            Ty.cast (Adt.mk_poly (Types.TypeVarId.of_int 0)); Ty.cast (BV.u8i 1);
          ] );
    ]
  in
  List.iter (fun (n, s, t) -> full n s (Ty.cast t)) handmade;
  (* symbolic tuples *)
  List.iter
    (fun (n, s) -> full ("var " ^ n) s (fresh_var s))
    [
      ("(u32)", Tup [ u32 ]);
      ("(u8, u32, usize)", Tup [ u8; u32; usz ]);
      ("(f64, full)", Tup [ f64; Full ]);
      ("((u8,u8),(u32,u32))", Tup [ Tup [ u8; u8 ]; Tup [ u32; u32 ] ]);
      ("(thin, thin)", Tup [ Thin; Thin ]);
      ("()", Tup []);
    ];
  (* identities *)
  let tup = gen ~p:0 (Tup [ u32; f32 ]) in
  op "mk_tuple of as_tuple is physically equal" (fun () ->
      string_of_bool (Ty.cast (Adt.mk_tuple (Adt.as_tuple (Ty.cast tup))) == tup));
  let x = fresh_var (Tup [ u32; u8 ]) in
  op "mk_tuple of as_tuple of a variable" (fun () ->
      ppa (Adt.mk_tuple (Adt.as_tuple (Ty.cast x))));
  op "field_of 1 (set_field 1 y x)" (fun () ->
      ppa (Adt.field_of 1 (Adt.set_field 1 (BV.u8i 5) (Ty.cast x))));
  op "field_of 0 (set_field 1 y x)" (fun () ->
      ppa (Adt.field_of 0 (Adt.set_field 1 (BV.u8i 5) (Ty.cast x))));
  op "sem_eq tuples (conc)" (fun () ->
      ppa
        (Ty.sem_eq
           (Adt.mk_tuple [ BV.u8i 1; BV.u8i 2 ])
           (Adt.mk_tuple [ BV.u8i 1; BV.u8i 3 ])));
  op "sem_eq tuple vars" (fun () ->
      let a = fresh_var (Tup [ u8; u8 ]) in
      ppa (Ty.sem_eq a a));
  op "sem_eq tuple var / tuple" (fun () ->
      ppa
        (Ty.sem_eq
           (fresh_var (Tup [ u8; u8 ]))
           (Adt.mk_tuple [ BV.u8i 1; BV.u8i 2 ])));
  op "ite on tuples" (fun () ->
      let b = BV.to_bool (Ty.cast (fresh_var (Int TBool))) in
      ppa
        (Ty.ite b
           (Adt.mk_tuple [ BV.u8i 1; BV.u8i 2 ])
           (Adt.mk_tuple [ BV.u8i 3; BV.u8i 4 ])));
  op "field_of 0 (ite b t1 t2)" (fun () ->
      let b = BV.to_bool (Ty.cast (fresh_var (Int TBool))) in
      ppa
        (Adt.field_of 0
           (Ty.ite b
              (Adt.mk_tuple [ BV.u8i 1; BV.u8i 2 ])
              (Adt.mk_tuple [ BV.u8i 3; BV.u8i 4 ]))))

let arrays () =
  section "arrays";
  let u8t : Types.ty = TLiteral (TUInt U8) in
  let handmade =
    [
      ("[] : u8", Arr (u8, 0), Adt.mk_array u8t (Iarray.of_list []));
      ( "[1; 2; 3] : u8",
        Arr (u8, 3),
        Adt.mk_array u8t (Iarray.of_list [ BV.u8i 1; BV.u8i 2; BV.u8i 3 ]) );
      ( "[var; var+1] : u32",
        Arr (u32, 2),
        let x : T.sint Ty.t = Ty.cast (fresh_var u32) in
        Adt.mk_array (TLiteral (TUInt U32))
          (Iarray.of_list [ x; Ty.cast (BV.add x (BV.mki 32 1)) ]) );
      ( "[(1,2.5); (3,4.5)]",
        Arr (Tup [ u32; f32 ], 2),
        let t a b =
          Ty.cast (Adt.mk_tuple [ Ty.cast (BV.u32i a); Ty.cast (Fl.mk F32 b) ])
        in
        Adt.mk_array u8t (Iarray.of_list [ t 1 "2.5"; t 3 "4.5" ]) );
      ( "[(var,var); (1, 2.5)]",
        Arr (Tup [ u32; f32 ], 2),
        let t a b = Ty.cast (Adt.mk_tuple [ a; b ]) in
        Adt.mk_array u8t
          (Iarray.of_list
             [
               t (fresh_var u32) (fresh_var f32);
               t (Ty.cast (BV.u32i 1)) (Ty.cast (Fl.mk F32 "2.5"));
             ]) );
      ( "[full; full]",
        Arr (Full, 2),
        Adt.mk_array u8t
          (Iarray.of_list
             [
               Ty.cast (Ptr.null_f ()); Ty.cast (Ptr.of_address_f (BV.usizei 4));
             ]) );
      ( "[[1;2];[3;4]]",
        Arr (Arr (u8, 2), 2),
        let r a b =
          Ty.cast (Adt.mk_array u8t (Iarray.of_list [ BV.u8i a; BV.u8i b ]))
        in
        Adt.mk_array u8t (Iarray.of_list [ r 1 2; r 3 4 ]) );
      ( "[thin; thin]",
        Arr (Thin, 2),
        Adt.mk_array u8t
          (Iarray.of_list
             [ Ty.cast (Ptr.null ()); Ty.cast (Ptr.of_address (BV.usizei 4)) ])
      );
    ]
  in
  List.iter (fun (n, s, a) -> full n s (Ty.cast a)) handmade;
  List.iter
    (fun (n, s) -> full ("var " ^ n) s (fresh_var s))
    [
      ("[u8; 3]", Arr (u8, 3));
      ("[u32; 0]", Arr (u32, 0));
      ("[(u32, f32); 2]", Arr (Tup [ u32; f32 ], 2));
      ("[full; 1]", Arr (Full, 1));
      ("[[u8; 2]; 2]", Arr (Arr (u8, 2), 2));
    ];
  let big = Arr (u8, 40) in
  let a = fresh_var big in
  op "as_array of a 40-element variable (length)" (fun () ->
      string_of_int (Iarray.length (Adt.as_array (Ty.cast a))));
  op "array_field_of 39 var" (fun () -> ppa (Adt.array_field_of 39 (Ty.cast a)));
  op "set_array_field 39 then field 39" (fun () ->
      ppa
        (Adt.array_field_of 39 (Adt.set_array_field 39 (BV.u8i 7) (Ty.cast a))));
  op "set_array_field 39 then field 38" (fun () ->
      ppa
        (Adt.array_field_of 38 (Adt.set_array_field 39 (BV.u8i 7) (Ty.cast a))));
  op "mk_array of as_array of a var" (fun () ->
      ppa (Adt.mk_array u8t (Adt.as_array (Ty.cast (fresh_var (Arr (u8, 3)))))))

let polys () =
  section "poly values";
  List.iter
    (fun k ->
      let p = Adt.mk_poly (Types.TypeVarId.of_int k) in
      full (Printf.sprintf "poly %d" k) (Poly k) (Ty.cast p))
    [ 0; 1; 5 ];
  op "poly twice is physically equal" (fun () ->
      string_of_bool
        (Adt.mk_poly (Types.TypeVarId.of_int 1)
        == Adt.mk_poly (Types.TypeVarId.of_int 1)));
  op "poly sem_eq" (fun () ->
      ppa
        (Ty.sem_eq
           (Adt.mk_poly (Types.TypeVarId.of_int 1))
           (Adt.mk_poly (Types.TypeVarId.of_int 2))));
  ()

let unions () =
  section "unions (synthetic crate)";
  let blk value off sz =
    { Ty.value; offset = BV.usizei off; size = BV.usizeinz sz }
  in
  let sc v = Ty.Scalar (Ty.cast v) in
  let ag v ty = Ty.Aggregate (Ty.cast v, ty) in
  let cases =
    [
      ("union U0 [u32@0]", 0, [ blk (sc (BV.u32i 1)) 0 4 ]);
      ("union U0 [f32@0]", 0, [ blk (sc (Fl.mk F32 "1.5")) 0 4 ]);
      ( "union U0 [u32@0; f32@4]",
        0,
        [ blk (sc (BV.u32i 1)) 0 4; blk (sc (Fl.mk F32 "2.5")) 4 4 ] );
      ("union U0 [var@0]", 0, [ blk (sc (fresh_var u32)) 0 4 ]);
      ( "union U0 [var@var]",
        0,
        [
          {
            Ty.value = sc (fresh_var u32);
            offset = Ty.cast (fresh_var usz);
            size = BV.usizeinz 4;
          };
        ] );
      ("union U0 []", 0, []);
      ( "union U1 [agg]",
        1,
        [
          blk
            (ag
               (Adt.mk_tuple
                  [
                    BV.u32i 1;
                    Ty.cast (Ptr.null_f ());
                    Ty.cast (BV.of_bool Ty.v_true);
                  ])
               (rty (Tup structs.(1))))
            0 16;
        ] );
      ( "union U1 [u8; agg]",
        1,
        [
          blk (sc (BV.u8i 3)) 0 1;
          blk
            (ag
               (Adt.mk_tuple
                  [
                    BV.u32i 1;
                    Ty.cast (Ptr.null_f ());
                    Ty.cast (BV.of_bool Ty.v_true);
                  ])
               (rty (Tup structs.(1))))
            8 16;
        ] );
    ]
  in
  List.iter
    (fun (n, k, blocks) ->
      match Adt.mk_union (union_ref k) blocks with
      | u -> full ~learn:false n (Uni k) (Ty.cast u)
      | exception e -> pr "== %s\n  EXN %s" n (squash (exn_str e)))
    cases

let enum_stanza () =
  section "enums (synthetic crate)";
  let ok = Types.VariantId.of_int in
  let opt = enum_ref 0
  and shape = enum_ref 1
  and unit_ = enum_ref 2
  and outer = enum_ref 3 in
  let handmade =
    [
      ("Opt::None", 0, Adt.mk_enum opt (ok 0) []);
      ("Opt::Some(5)", 0, Adt.mk_enum opt (ok 1) [ BV.u32i 5 ]);
      ("Opt::Some(var)", 0, Adt.mk_enum opt (ok 1) [ Ty.cast (fresh_var u32) ]);
      ( "Opt::Pair(1, null)",
        0,
        Adt.mk_enum opt (ok 2) [ Ty.cast (BV.u8i 1); Ty.cast (Ptr.null_f ()) ]
      );
      ( "Shape::Circle(1.5)",
        1,
        Adt.mk_enum shape (ok 0) [ Ty.cast (Fl.mk F32 "1.5") ] );
      ( "Shape::Rect(2,3)",
        1,
        Adt.mk_enum shape (ok 1) [ Ty.cast (BV.u32i 2); Ty.cast (BV.u32i 3) ] );
      ( "Shape::Nest((1, 2.5))",
        1,
        Adt.mk_enum shape (ok 2)
          [
            Ty.cast
              (Adt.mk_tuple [ Ty.cast (BV.u8i 1); Ty.cast (Fl.mk F64 "2.5") ]);
          ] );
      ( "Shape::Arr([1,2,3])",
        1,
        Adt.mk_enum shape (ok 3)
          [
            Ty.cast
              (Adt.mk_array (TLiteral (TUInt U8))
                 (Iarray.of_list [ BV.u8i 1; BV.u8i 2; BV.u8i 3 ]));
          ] );
      ("Unit::B", 2, Adt.mk_enum unit_ (ok 1) []);
      ( "Outer::Wrap(Opt::Some(1))",
        3,
        Adt.mk_enum outer (ok 0)
          [ Ty.cast (Adt.mk_enum opt (ok 1) [ BV.u32i 1 ]) ] );
      ( "Outer::Wrap(var)",
        3,
        Adt.mk_enum outer (ok 0) [ Ty.cast (fresh_var (Enm 0)) ] );
      ( "Outer::Bare(true, -1)",
        3,
        Adt.mk_enum outer (ok 1)
          [
            Ty.cast (BV.of_bool Ty.v_true); Ty.cast (BV.mki_lit (TInt I64) (-1));
          ] );
    ]
  in
  List.iter (fun (n, k, e) -> full n (Enm k) (Ty.cast e)) handmade;
  Array.iteri
    (fun k _ ->
      full (Printf.sprintf "var enum %d" k) (Enm k) (fresh_var (Enm k)))
    enums;
  op "Checked.mk_enum Opt Some" (fun () ->
      ppa (Adt.Checked.mk_enum opt "Some" [ BV.u32i 1 ]));
  op "Checked.mk_enum Opt Nope" (fun () ->
      ppa (Adt.Checked.mk_enum opt "Nope" [ BV.u32i 1 ]));
  op "Checked.mk_enum Opt Some (wrong arity)" (fun () ->
      ppa (Adt.Checked.mk_enum opt "Some" []));
  op "t_enum Opt" (fun () -> ppty (Ty.t_enum opt));
  op "mk_enum twice is physically equal" (fun () ->
      string_of_bool
        (Adt.mk_enum opt (ok 1) [ BV.u32i 5 ]
        == Adt.mk_enum opt (ok 1) [ BV.u32i 5 ]));
  let e = fresh_var (Enm 0) in
  op "is_variant 1 (set_field_of_variant 1 0 5 e)" (fun () ->
      ppa
        (Adt.is_variant (ok 1)
           (Adt.set_field_of_variant (ok 1) 0 (BV.u32i 5) (Ty.cast e))));
  op "sem_eq e e" (fun () -> ppa (Ty.sem_eq e e));
  op "sem_eq Some(1) Some(2)" (fun () ->
      ppa
        (Ty.sem_eq
           (Adt.mk_enum opt (ok 1) [ BV.u32i 1 ])
           (Adt.mk_enum opt (ok 1) [ BV.u32i 2 ])));
  op "sem_eq None Some(2)" (fun () ->
      ppa
        (Ty.sem_eq
           (Adt.mk_enum opt (ok 0) [])
           (Adt.mk_enum opt (ok 1) [ BV.u32i 2 ])));
  op "ite b None Some" (fun () ->
      ppa
        (Ty.ite
           (BV.to_bool (Ty.cast (fresh_var (Int TBool))))
           (Adt.mk_enum opt (ok 0) [])
           (Adt.mk_enum opt (ok 1) [ BV.u32i 2 ])));
  op "update_field_of_variant" (fun () ->
      ppa (Adt.update_field_of_variant (ok 1) 0 (fun x -> x) (Ty.cast e)))

let random_stanza ~crate ~seed ~n ~depth name =
  section name;
  rng := Random.State.make [| seed |];
  for i = 1 to n do
    let s = rand_shape ~crate depth in
    let v = gen ~p:35 s in
    full (Printf.sprintf "%s #%d" name i) s v;
    maybe_gc ()
  done

let print_decls () =
  section "declarations (first-seen order)";
  List.iter
    (fun (k, cmds) ->
      pr "decl %s" k;
      List.iter (fun c -> pr "  %s" c) cmds)
    (List.rev !decl_defs)

let pass_a () =
  section "PASS A: no crate (default pointer size)";
  rng := Random.State.make [| 1 |];
  scalars ();
  maybe_gc ();
  arithmetic ();
  maybe_gc ();
  thin_pointers ();
  maybe_gc ();
  full_pointers_and_meta ();
  maybe_gc ();
  tuples ();
  maybe_gc ();
  arrays ();
  maybe_gc ();
  polys ();
  random_stanza ~crate:false ~seed:11 ~n:20 ~depth:3 "random (no crate)";
  maybe_gc ()

let pass_b () =
  section "PASS B: synthetic crate, 8-byte pointers";
  Shim.with_crate (Lazy.force crate64) @@ fun () ->
  rng := Random.State.make [| 2 |];
  unions ();
  maybe_gc ();
  enum_stanza ();
  maybe_gc ();
  random_stanza ~crate:true ~seed:22 ~n:12 ~depth:3 "random (crate)";
  maybe_gc ()

let pass_c () =
  section "PASS C: synthetic crate, 4-byte pointers";
  Shim.with_crate (Lazy.force crate32) @@ fun () ->
  rng := Random.State.make [| 3 |];
  ops_enabled := false;
  thin_pointers ();
  full_pointers_and_meta ();
  tuples ();
  enum_stanza ();
  ops_enabled := true;
  random_stanza ~crate:true ~seed:33 ~n:8 ~depth:2 "random (crate32)"

let () =
  if Array.exists (String.equal "--gc") Sys.argv then gc_mode := true;
  pass_a ();
  pass_b ();
  pass_c ();
  print_decls ();
  print_string (Buffer.contents out)
