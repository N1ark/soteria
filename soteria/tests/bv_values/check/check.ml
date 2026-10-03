(* Compile-check of the interfaces of the generic code, and tests of the generic
   layers over a [Kanon_fns] implementation.

   Part A (compile time): the generated [Soteria.Bv_values.Lang.Types] satisfies
   [Value_lang.Term]; the reference [Kanon_ref] satisfies [Kanon_fns] over the
   generated types; the language composed by [Lang_make.Make] is a
   [Solver_lang.S] (so [Analyses] and [Encoding] apply to it unchanged) and
   [Typed.Make] gives a [Typed_intf.S] and a [Typed_intf.Solver_value].

   Part B (run time): on random well-typed terms, [eval] does not change a term
   that the smart constructors built, and [rebuild v (operands v)] is [v].
   (Until the first generation of the value language was deleted, Part B also
   compared the generic [pp], [cost], [encode_node]/[encode_ty], [as_range],
   [iter_vars], [implies_or_contradicts], [sure_neq], [eval], [Subst.apply] and
   [Subst.learn] with that generation's, on the same terms: they agreed on all
   of them.) *)

open Soteria.Bv_values
module Types = Soteria.Bv_values.Lang.Types

(* {1 Part A} *)

module _ : Value_lang.Term = Types

module K : Kanon_fns.Kanon_fns with type t = Types.t and type ty = Types.ty =
  Kanon_ref

module L = Lang_make.Make (Types) (K)
module V = L.V
module Typed = Typed.Make (L)

module _ :
  Soteria.Bv_values.Solver_lang.S with type t = Types.t and type ty = Types.ty =
  L.V

module _ : Typed_intf.Solver_value = Typed
module _ = Soteria.Bv_values.Analyses.Make (L.V)
module _ = Soteria.Bv_values.Encoding.Make (L.V)

(* {1 Part B} *)

module G = Gen.Make (L.Svalue)

let str pp x = Format.asprintf "%a" pp x

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
let corpora = lazy (List.map (fun seed -> corpus ~seed ~n:700 ~depth:5) seeds)
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
  | Op1 (op, _) -> Format.asprintf "%a" Kanon_ref.pp_op1 op
  | Op2 (Ptr, _, _) -> "&"
  | Op2 (op, _, _) -> Format.asprintf "%a" Kanon_ref.pp_op2 op
  | Op3 (Ite, _, _, _) -> "ite"
  | Op3 (Fma, _, _, _) -> "fma"
  | OpN (Distinct, _) -> "distinct"

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
      ( "generic layers",
        [
          Alcotest.test_case "coverage" `Quick coverage;
          Alcotest.test_case "rebuild . operands" `Quick rebuild_property;
          Alcotest.test_case "eval is idempotent" `Quick eval_idempotent;
        ] );
    ]
