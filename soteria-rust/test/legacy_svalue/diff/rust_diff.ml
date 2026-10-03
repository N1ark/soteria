(* The differential test of the Rust value language, old stack against new:
   [rust_diff.exe [--chunks N] [--n M] [--seed S] [--quiet]].

   Every chunk runs the generator and the observer of body.ml on both stacks, in
   lock step, with the same seed: the same random Rust values are built through
   the public interface of each ([Typed]), and every observation (the values,
   their sorts, costs, evaluation, substitution, learning, SMT encoding, the
   operations of the interface on each shape, and the exceptions) is printed
   through the neutral AST, then the outputs are compared line by line: STRICT,
   the order of the operands counts. Exit status 0 iff no chunk differs.

   [--self-test] runs the same comparison between the old stack and MUTANTS of
   the new one (rules/rust.kn and the generated rules with one deliberate error
   each, see mutants/), and succeeds iff every mutant is detected. *)

open Compare

let () =
  Arg.parse
    [
      ("--chunks", Arg.Set_int chunks, "N number of chunks (default 20)");
      ("--n", Arg.Set_int n, "M random values per chunk and pass (default 100)");
      ("--seed", Arg.Set_int seed0, "S first seed (default 1)");
      ("--quiet", Arg.Set quiet, " only print the summary line, not the tables");
      ("--self-test", Arg.Set self_test, " check that the mutants are detected");
    ]
    (fun _ -> ())
    "rust_diff"

(* The hash-consing tables are weak: if a node dies and is built again, it gets
   a greater tag, which can change the order of the operands of a commutative
   operator. A collection that happens in one stack and not in the other would
   then be a false difference. So there is no major collection inside a chunk
   (an enormous space overhead), and a full one between chunks. *)
let () = Gc.set { (Gc.get ()) with Gc.space_overhead = 1_000_000_000 }

let kinds_table name tbl =
  Printf.printf "nodes converted on the %s side, by kind:" name;
  List.iter
    (fun (k, c) -> Printf.printf " %s=%d" k c)
    (List.sort compare (Hashtbl.fold (fun k c acc -> (k, c) :: acc) tbl []));
  print_newline ()

(* The operations of the interface that every run must exercise *)
let required =
  [
    "as_tuple";
    "field_of #";
    "set_field #";
    "update_field # (fun x -> x)";
    "as_tuple#";
    "as_array";
    "array_field_of #";
    "set_array_field #";
    "update_array_field #";
    "loc";
    "ofs";
    "decompose";
    "size_of";
    "align_of";
    "allocation_info";
    "tag_of";
    "is_null";
    "is_at_null_loc";
    "has_provenance";
    "in_bound";
    "as_id";
    "add_ofs #";
    "set_ofs ##";
    "with_tag zero";
    "with_tag none";
    "same_prov self";
    "of_ptr_t";
    "ptr_of";
    "len_meta";
    "vtable_meta";
    "with_ptr null";
    "with_ptr self";
    "is_variant #";
    "as_enum_of_variant #";
    "field_of_variant # #";
    "set_field_of_variant # #";
    "discriminant_of";
    "as_union";
    "as_type_var";
    "learn vs concrete";
    "learn vs symbolic";
    "evalf";
    "subst";
    "smt";
    "cost";
    "pp";
    "ty";
    "pp_ty";
    "cast_tuple";
    "cast_array";
    "cast_ptr_t";
    "cast_ptr_f";
    "cast_enum";
    "cast_union ~adt";
  ]

let () =
  if !self_test then (
    Mutants.self_test ();
    exit 0);
  let o =
    run_pair ~old_run:Old_side.run ~new_run:New_side.run ~stop_at_first:false
      ~report:true
  in
  Printf.printf "chunks: %d  lines compared: %d  chunks with a difference: %d\n"
    o.compared_chunks o.compared_lines o.diffs;
  if not !quiet then (
    kinds_table "old" Old_conv.kinds;
    kinds_table "new" New_conv.kinds);
  let missing =
    List.filter
      (fun l ->
        match Hashtbl.find_opt o.ops l with
        | Some (v, e) -> v + e = 0
        | None -> true)
      required
  in
  if not !quiet then (
    Printf.printf "operations observed (values / exceptions):\n";
    List.iter
      (fun (l, (v, e)) -> Printf.printf "  %-34s %7d %7d\n" l v e)
      (List.sort compare (Hashtbl.fold (fun k c acc -> (k, c) :: acc) o.ops [])));
  if missing <> [] then (
    Printf.printf "NOT EXERCISED: %s\n" (String.concat "; " missing);
    exit 2);
  if o.diffs > 0 then exit 1
