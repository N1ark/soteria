(* Compile-check of the frozen interfaces, and tests of the generic layers
   against the OLD stack.

   Part A (compile time): the generated [Soteria.Bv_values.Lang.Types] satisfies
   [Value_lang.Term]; the reference [Kanon_ref] satisfies [Kanon_fns] over the
   generated types; the language composed by [Lang_v.Make] is a [Solver_lang.S]
   (so [Analyses] and [Encoding] apply to it unchanged) and [Typed_v.Make] gives
   a [Typed_intf_v.S] and a [Typed_intf_v.Solver_value].

   Part B (run time): on random well-typed terms, the generic [pp], [cost],
   [encode_node]/[encode_ty], [as_range], [iter_vars], [implies_or_contradicts],
   [sure_neq], [eval], [Subst.apply] and [Subst.learn] over [Kanon_ref] give
   what the old stack gives on the same term (converted into raw old nodes). *)

open Soteria.Bv_values
module Types = Soteria.Bv_values.Lang.Types

(* {1 Part A} *)

module _ : Value_lang.Term = Types

module K : Kanon_fns.Kanon_fns with type t = Types.t and type ty = Types.ty =
  Kanon_ref

module L = Lang_v.Make (Types) (K)
module V = L.V
module Typed = Typed_v.Make (L)

module _ :
  Soteria.Bv_values.Solver_lang.S with type t = Types.t and type ty = Types.ty =
  L.V

module _ : Typed_intf_v.Solver_value = Typed
module _ = Soteria.Bv_values.Analyses.Make (L.V)
module _ = Soteria.Bv_values.Encoding.Make (L.V)

(* {1 Part B} *)

module G = Gen.Make (L.Svalue)
module Old = Soteria.Bv_values.Svalue
module OS = Conv.OS
module OL = Conv.OT.Lang
module OT = Conv.OT
module OE = Conv.OT.Expr
module Smt = Soteria.Smt
module Decls = Soteria.Solvers.Decls
module Var = Soteria.Symex.Var

let str pp x = Format.asprintf "%a" pp x

(* The encoding with the order of the declarations, as the golden dump does *)
module Enc_log (L : Soteria.Bv_values.Solver_lang.S) = struct
  let encode (x : L.t) : string =
    let log = Buffer.create 64 in
    let rec collect : 'a. depth:int -> (unit -> 'a) -> 'a =
     fun ~depth f ->
      try f ()
      with effect Decls.Declare d, k ->
        Buffer.add_string log
          (Printf.sprintf "%sdecl key=%s\n" (String.make depth ' ') d.key);
        let cmds = ref [] in
        collect ~depth:(depth + 2) (fun () ->
            d.commands (fun s -> cmds := s :: !cmds));
        List.iter
          (fun s ->
            Buffer.add_string log
              (Printf.sprintf "%s  cmd %s\n" (String.make depth ' ')
                 (str Smt.pp_sexp s)))
          (List.rev !cmds);
        Effect.Deep.continue k ()
    in
    let memo = L.Hashtbl.create 16 in
    let rec sort_of_ty ty = L.encode_ty ~sort_of_ty ty in
    let rec enc t =
      match L.Hashtbl.find_opt memo t with
      | Some k -> k
      | None ->
          let k = L.encode_node ~sort_of_ty ~encode_child:enc t in
          L.Hashtbl.add memo t k;
          k
    in
    match collect ~depth:0 (fun () -> enc x) with
    | k -> Buffer.contents log ^ "sexp " ^ str Smt.pp_sexp k
    | exception Failure m -> "failure " ^ m
end

module NEnc = Enc_log (L.V)
module OEnc = Enc_log (OL)

let subterms (roots : Types.t list) : Types.t list =
  let seen = Hashtbl.create 256 in
  let acc = ref [] in
  let rec go (v : Types.t) =
    if not (Hashtbl.mem seen v.tag) then (
      Hashtbl.add seen v.tag ();
      List.iter go (K.operands v);
      acc := v :: !acc)
  in
  List.iter go roots;
  List.rev !acc

let corpus ~seed ~n ~depth : Types.t list =
  let rng = Random.State.make [| seed |] in
  let roots =
    List.init n (fun _ ->
        let s = G.sorts.(Random.State.int rng (Array.length G.sorts)) in
        G.gen rng depth s)
  in
  subterms roots

let seeds = [ 1; 2; 3 ]

(* The two stacks have independent tag counters, and the printers order the
   operands of commutative operators by tag: convert in the order of creation of
   the new terms, so that the tags of the old stack are monotone with them. *)
let corpora =
  lazy
    (let cs = List.map (fun seed -> corpus ~seed ~n:700 ~depth:5) seeds in
     List.concat cs
     |> List.sort (fun (a : Types.t) b -> Int.compare a.tag b.tag)
     |> List.iter (fun v -> ignore (Conv.conv v));
     cs)

let each f = List.iter (List.iter f) (Lazy.force corpora)

(* every kind of node must occur, or the comparison below proves little *)
let kind_name (v : Types.t) =
  match v.kind with
  | Var _ -> "Var"
  | Seq _ -> "Seq"
  | Bool _ -> "Bool"
  | Exists _ -> "Exists"
  | BitVec _ -> "BitVec"
  | LocLit _ -> "LocLit"
  | Float _ -> "Float"
  | Op1 (op, _) -> (
      match Kanon_ref.old_unop op with
      | op -> Format.asprintf "%a" Old.Unop.pp op)
  | Op2 (Ptr, _, _) -> "&"
  | Op2 (op, _, _) -> Format.asprintf "%a" Old.Binop.pp (Kanon_ref.old_binop op)
  | Op3 (Ite, _, _, _) -> "ite"
  | Op3 (Fma, _, _, _) -> "fma"
  | OpN (Distinct, _) -> "distinct"

let check_eq ~what ~show a b (v : Types.t) =
  if a <> b then
    Alcotest.failf "%s differs on %s@.  generic: %s@.  old:     %s" what
      (str V.pp v) (show a) (show b)

let coverage () =
  let tbl = Hashtbl.create 64 in
  each (fun v ->
      let k = kind_name v in
      Hashtbl.replace tbl k
        (1 + Option.value ~default:0 (Hashtbl.find_opt tbl k)));
  let missing =
    [
      "Var";
      "Seq";
      "Bool";
      "Exists";
      "BitVec";
      "LocLit";
      "Float";
      "&";
      "ite";
      "fma";
      "distinct";
      "+";
      "&&";
      "==";
      "!";
      "extract[0-7]";
    ]
    |> List.filter (fun k -> not (Hashtbl.mem tbl k))
  in
  Printf.printf "node kinds in the corpus: %d\n%!" (Hashtbl.length tbl);
  Alcotest.(check (list string)) "no missing kind" [] missing

let pp_oracle () =
  each (fun v ->
      let ov = Conv.conv v in
      check_eq ~what:"pp" ~show:Fun.id (str V.pp v) (str OS.pp ov) v)

let pp_ty_oracle () =
  each (fun v ->
      let ov = Conv.conv v in
      check_eq ~what:"pp_ty" ~show:Fun.id (str K.pp_ty v.ty)
        (str OS.pp_ty ov.node.ty) v)

let cost_oracle () =
  each (fun v ->
      let ov = Conv.conv v in
      check_eq ~what:"cost" ~show:string_of_int (V.cost v) (OL.cost ov) v)

let encode_oracle () =
  each (fun v ->
      let ov = Conv.conv v in
      check_eq ~what:"encode" ~show:Fun.id (NEnc.encode v) (OEnc.encode ov) v)

let range_str = function
  | None -> "None"
  | Some (x, size, (sign, (lo, hi))) ->
      Printf.sprintf "Some (%d, %d, (%s, (%s, %s)))" (Var.to_int x) size sign
        (Z.to_string lo) (Z.to_string hi)

let range_oracle () =
  let n_some = ref 0 in
  each (fun v ->
      let ov = Conv.conv v in
      let a =
        V.as_range v
        |> Option.map (fun (x, s, (sg, r)) ->
            (x, s, ((match sg with V.Pos -> "Pos" | Neg -> "Neg"), r)))
      in
      let b =
        OL.as_range ov
        |> Option.map (fun (x, s, (sg, r)) ->
            (x, s, ((match sg with OL.Pos -> "Pos" | Neg -> "Neg"), r)))
      in
      if Option.is_some a then incr n_some;
      let show = function
        | None -> "None"
        | Some (x, s, (sg, (lo, hi))) -> range_str (Some (x, s, (sg, (lo, hi))))
      in
      check_eq ~what:"as_range" ~show a b v);
  Printf.printf "as_range: %d terms with a range\n%!" !n_some;
  Alcotest.(check bool) "some ranges exercised" true (!n_some > 20)

let shape_oracle () =
  let b x = if x then "Some" else "None" in
  each (fun v ->
      let ov = Conv.conv v in
      let chk what a c = check_eq ~what ~show:Fun.id (b a) (b c) v in
      chk "is_literal" (V.is_literal v) (OL.is_literal ov);
      chk "is_bool" (V.is_bool v) (OL.is_bool ov);
      chk "as_var" (Option.is_some (V.as_var v)) (Option.is_some (OL.as_var ov));
      chk "as_not" (Option.is_some (V.as_not v)) (Option.is_some (OL.as_not ov));
      chk "as_eq" (Option.is_some (V.as_eq v)) (Option.is_some (OL.as_eq ov));
      chk "as_and" (Option.is_some (V.as_and v)) (Option.is_some (OL.as_and ov));
      chk "as_or" (Option.is_some (V.as_or v)) (Option.is_some (OL.as_or ov));
      chk "as_ite" (Option.is_some (V.as_ite v)) (Option.is_some (OL.as_ite ov));
      chk "as_lt" (Option.is_some (V.as_lt v)) (Option.is_some (OL.as_lt ov));
      chk "as_leq" (Option.is_some (V.as_leq v)) (Option.is_some (OL.as_leq ov));
      chk "as_distinct"
        (Option.is_some (V.as_distinct v))
        (Option.is_some (OL.as_distinct ov));
      chk "as_bv_ty"
        (Option.is_some (V.as_bv_ty v.ty))
        (Option.is_some (OL.as_bv_ty ov.node.ty)))

let vars_oracle () =
  let collect iter x =
    let l = ref [] in
    iter x (fun (var, ty) -> l := Var.to_int var :: !l);
    List.rev !l
  in
  each (fun v ->
      let ov = Conv.conv v in
      check_eq ~what:"iter_vars"
        ~show:(fun l -> String.concat "," (List.map string_of_int l))
        (collect V.iter_vars v) (collect OL.iter_vars ov) v)

let pair_oracle () =
  let all = List.concat (Lazy.force corpora) in
  let bools = List.filter (fun (v : Types.t) -> v.ty = TBool) all in
  let arr = Array.of_list bools in
  let n = Array.length arr in
  let show = function None -> "None" | Some b -> string_of_bool b in
  let hits = ref 0 in
  for i = 0 to n - 1 do
    for d = 1 to 3 do
      let q = arr.(i) and pc = arr.((i + (d * 7919)) mod n) in
      let oq = Conv.conv q and opc = Conv.conv pc in
      let a = V.implies_or_contradicts ~q ~neg_q:(V.not_ q) pc in
      let b = OL.implies_or_contradicts ~q:oq ~neg_q:(OL.not_ oq) opc in
      if a <> None then incr hits;
      check_eq ~what:"implies_or_contradicts" ~show a b q
    done
  done;
  let same_sort = Hashtbl.create 16 in
  List.iter
    (fun (v : Types.t) ->
      let l = Option.value ~default:[] (Hashtbl.find_opt same_sort v.ty) in
      Hashtbl.replace same_sort v.ty (v :: l))
    all;
  Hashtbl.iter
    (fun _ l ->
      let arr = Array.of_list l in
      let n = Array.length arr in
      if n > 1 then
        for i = 0 to min (n - 1) 300 do
          let a = arr.(i) and b = arr.(((i * 31) + 7) mod n) in
          check_eq ~what:"sure_neq" ~show:string_of_bool (V.sure_neq a b)
            (OL.sure_neq (Conv.conv a) (Conv.conv b))
            a
        done)
    same_sort;
  Printf.printf "implies_or_contradicts: %d decided pairs\n%!" !hits

(* the variable environment: even variables of sort bv8/bool get a value *)
let new_eval_var sv v (ty : Types.ty) : Types.t =
  if Var.to_int v mod 2 = 0 then
    match ty with
    | TBitVector n -> K.mk_bv n (Z.of_int 5)
    | TBool -> K.v_true
    | _ -> sv
  else sv

let old_eval_var sv v (ty : OS.ty) : OS.t =
  if Var.to_int v mod 2 = 0 then
    match ty with
    | Old.TBitVector n -> OS.BitVec.mk n (Z.of_int 5)
    | Old.TBool -> OS.Bool.v_true
    | _ -> sv
  else sv

let eval_oracle () =
  let diffs = ref 0 and n = ref 0 in
  each (fun v ->
      let ov = Conv.conv v in
      let try_ name a b =
        incr n;
        if str V.pp a <> str OS.pp b then (
          incr diffs;
          if !diffs <= 5 then
            Printf.printf
              "eval (%s) differs on %s\n  generic: %s\n  old:     %s\n%!" name
              (str V.pp v) (str V.pp a) (str OS.pp b))
      in
      try_ "force" (V.eval ~force:true v) (OL.eval ~force:true ov);
      try_ "env"
        (V.eval ~eval_var:new_eval_var v)
        (OL.eval ~eval_var:old_eval_var ov);
      try_ "force+env"
        (V.eval ~force:true ~eval_var:new_eval_var v)
        (OL.eval ~force:true ~eval_var:old_eval_var ov));
  Printf.printf "eval: %d comparisons, %d differences\n%!" !n !diffs;
  Alcotest.(check int) "eval agrees with the old Eval" 0 !diffs

let subst_oracle () =
  let diffs = ref 0 and n = ref 0 in
  let module NS = L.Expr.Subst in
  let module OSb = OE.Subst in
  each (fun v ->
      let ov = Conv.conv v in
      let missing_var x ty = K.mk_var (Var.of_int (1000 + Var.to_int x)) ty in
      let omissing_var x ty =
        OT.type_
          (OS.mk_var (Var.of_int (1000 + Var.to_int x)) (OT.untype_type ty))
      in
      let a, _ = NS.apply ~missing_var NS.empty v in
      let b, _ = OSb.apply ~missing_var:omissing_var OSb.empty ov in
      incr n;
      if str V.pp a <> str OS.pp (OT.untyped b) then (
        incr diffs;
        if !diffs <= 5 then
          Printf.printf "subst differs on %s\n  generic: %s\n  old:     %s\n%!"
            (str V.pp v) (str V.pp a)
            (str OS.pp (OT.untyped b))));
  Printf.printf "Subst.apply: %d comparisons, %d differences\n%!" !n !diffs;
  Alcotest.(check int) "Subst.apply agrees with the old one" 0 !diffs

let learn_oracle () =
  let diffs = ref 0 and n = ref 0 and learnt = ref 0 in
  let module NS = L.Expr.Subst in
  let module OSb = OE.Subst in
  let rng = Random.State.make [| 99 |] in
  each (fun e ->
      let target : Types.t =
        match e.ty with
        | TBitVector w -> K.mk_masked w (Z.of_int (Random.State.int rng 256))
        | TBool -> K.v_true
        | TPointer w ->
            K.mk_ptr (K.mk_loc w (Z.of_int 3)) (K.mk_bv w (Z.of_int 4))
        | _ -> e
      in
      if not (target == e) then (
        let oe = Conv.conv e and ot = Conv.conv target in
        let a = NS.learn NS.empty e target in
        let b = OSb.learn OSb.empty oe (OT.type_ ot) in
        incr n;
        let render_new s =
          match s with
          | None -> "None"
          | Some s ->
              let l = ref [] in
              V.iter_vars e (fun (x, ty) ->
                  let r, _ =
                    NS.apply
                      ~missing_var:(fun x ty ->
                        K.mk_var (Var.of_int (5000 + Var.to_int x)) ty)
                      s (K.mk_var x ty)
                  in
                  l := (Var.to_int x, str V.pp r) :: !l);
              incr learnt;
              String.concat ";"
                (List.map
                   (fun (x, r) -> Printf.sprintf "%d:%s" x r)
                   (List.sort compare !l))
        in
        let render_old s =
          match s with
          | None -> "None"
          | Some s ->
              let l = ref [] in
              OL.iter_vars oe (fun (x, ty) ->
                  let r, _ =
                    OSb.apply
                      ~missing_var:(fun x ty ->
                        OT.type_
                          (OS.mk_var
                             (Var.of_int (5000 + Var.to_int x))
                             (OT.untype_type ty)))
                      s (OS.mk_var x ty)
                  in
                  l := (Var.to_int x, str OS.pp (OT.untyped r)) :: !l);
              String.concat ";"
                (List.map
                   (fun (x, r) -> Printf.sprintf "%d:%s" x r)
                   (List.sort compare !l))
        in
        let ra = render_new a and rb = render_old b in
        if ra <> rb then (
          incr diffs;
          if !diffs <= 5 then
            Printf.printf
              "learn differs on %s = %s\n  generic: %s\n  old:     %s\n%!"
              (str V.pp e) (str V.pp target) ra rb)));
  Printf.printf "Subst.learn: %d comparisons (%d learnt), %d differences\n%!" !n
    !learnt !diffs;
  Alcotest.(check int) "Subst.learn agrees with the old one" 0 !diffs

let rebuild_property () =
  let bad = ref 0 and n = ref 0 in
  each (fun v ->
      incr n;
      let r = K.rebuild v (K.operands v) in
      if not (Types.equal_t r v) then (
        incr bad;
        if !bad <= 5 then
          Printf.printf "rebuild (operands v) <> v on %s\n  got %s\n%!"
            (str V.pp v) (str V.pp r)));
  Printf.printf "rebuild v (operands v) == v: %d terms, %d differences\n%!" !n
    !bad

let eval_idempotent () =
  each (fun v ->
      let e = V.eval v in
      if not (Types.equal_t e v) then
        Alcotest.failf
          "eval changes a term built by the smart constructors: %s -> %s"
          (str V.pp v) (str V.pp e))

let () =
  Alcotest.run "check"
    [
      ( "generic layers vs the old stack",
        [
          Alcotest.test_case "coverage" `Quick coverage;
          Alcotest.test_case "pp" `Quick pp_oracle;
          Alcotest.test_case "pp_ty" `Quick pp_ty_oracle;
          Alcotest.test_case "cost" `Quick cost_oracle;
          Alcotest.test_case "encode_node, encode_ty" `Quick encode_oracle;
          Alcotest.test_case "as_range" `Quick range_oracle;
          Alcotest.test_case "recognisers" `Quick shape_oracle;
          Alcotest.test_case "iter_vars" `Quick vars_oracle;
          Alcotest.test_case "implies_or_contradicts, sure_neq" `Quick
            pair_oracle;
          Alcotest.test_case "eval" `Quick eval_oracle;
          Alcotest.test_case "Subst.apply" `Quick subst_oracle;
          Alcotest.test_case "Subst.learn" `Quick learn_oracle;
          Alcotest.test_case "rebuild . operands" `Quick rebuild_property;
          Alcotest.test_case "eval is idempotent" `Quick eval_idempotent;
        ] );
    ]
