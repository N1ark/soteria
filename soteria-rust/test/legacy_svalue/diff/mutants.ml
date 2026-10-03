(* The self-test of the differential test: the old stack is compared to MUTANTS
   of the new one, which are the same stack with one deliberate error in the
   generated rules ([mutations.ml]). The test succeeds iff the unmutated copy
   agrees with the old stack (the comparison itself produces no differences) and
   every mutant is detected. *)

open Compare

let self_test () =
  let ok = ref true in
  Rust_mut.Mut.current := 0;
  let o0 =
    run_pair ~old_run:Old_side.run ~new_run:Mut_side.run ~stop_at_first:true
      ~report:true
  in
  Printf.printf "no mutation: %s (%d chunks, %d lines compared)\n%!"
    (if o0.diffs = 0 then "no difference, as it must be" else "DIFFERENCES")
    o0.compared_chunks o0.compared_lines;
  if o0.diffs <> 0 then ok := false;
  List.iter
    (fun (m : Mutations.t) ->
      Rust_mut.Mut.current := m.k;
      let o =
        run_pair ~old_run:Old_side.run ~new_run:Mut_side.run ~stop_at_first:true
          ~report:false
      in
      if o.diffs > 0 then
        Printf.printf "mutant %d (%s): detected after %d chunk(s)\n%!" m.k
          m.name o.compared_chunks
      else (
        Printf.printf "mutant %d (%s): NOT DETECTED\n%!" m.k m.name;
        ok := false))
    Mutations.all;
  Rust_mut.Mut.current := 0;
  if not !ok then exit 1
