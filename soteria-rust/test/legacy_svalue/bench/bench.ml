(* [bench.exe [N [REPS]]]: the arrays of N elements (default 4096), old stack
   and new, see body.ml *)
let () =
  let n =
    if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 4096
  in
  let reps =
    if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 20
  in
  (* warm up both *)
  ignore (Old_side.run ~n:64 ~reps:1);
  ignore (New_side.run ~n:64 ~reps:1);
  let o = Old_side.run ~n ~reps in
  let w = New_side.run ~n ~reps in
  Printf.printf "arrays of %d elements; seconds per call (CPU time)\n" n;
  Printf.printf "%-52s %12s %12s %8s\n" "operation" "old (Iarray)" "new (list)"
    "new/old";
  List.iter2
    (fun (name, a) (_, b) ->
      Printf.printf "%-52s %12.3e %12.3e %8.2f\n" name a b (b /. a))
    o w
