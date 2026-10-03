(* The comparison of the outputs of two stacks, chunk by chunk (see
   rust_diff.ml) *)

let chunks = ref 20
let n = ref 100
let seed0 = ref 1
let quiet = ref false
let self_test = ref false
let lines s = String.split_on_char '\n' s

(* The operation of a line of the output, without numbers, for the statistics:
   [" field_of 2: ..."] is ["field_of #"], ["== name"] is a value header *)
let label line =
  let t = String.trim line in
  if String.length t > 2 && String.sub t 0 2 = "==" then "== (value)"
  else
    match String.index_opt t ':' with
    | None -> t
    | Some i ->
        String.map (function '0' .. '9' -> '#' | c -> c) (String.sub t 0 i)

let first_diff (a : string list) (b : string list) =
  let rec go i a b =
    match (a, b) with
    | [], [] -> None
    | x :: a', y :: b' ->
        if String.equal x y then go (i + 1) a' b' else Some (i, x, y)
    | x :: _, [] -> Some (i, x, "<end>")
    | [], y :: _ -> Some (i, "<end>", y)
  in
  go 0 a b

type outcome = {
  mutable compared_chunks : int;
  mutable compared_lines : int;
  mutable diffs : int;
  ops : (string, int * int) Hashtbl.t;  (** label -> (values, exceptions) *)
}

let skip line =
  let t = String.trim line in
  t = ""
  || t.[0] = '('
  || t.[0] = '#'
  || (String.length t >= 5 && String.sub t 0 5 = "decl ")
  || (String.length t >= 5 && String.sub t 0 5 = "tags:")

let record_ops o (l : string list) =
  List.iter
    (fun line ->
      if not (skip line) then
        let lab = label line in
        let is_exn =
          let t = String.trim line in
          match String.index_opt t ':' with
          | Some i ->
              let rest =
                String.trim (String.sub t (i + 1) (String.length t - i - 1))
              in
              String.length rest >= 3 && String.sub rest 0 3 = "EXN"
          | None -> false
        in
        let v, e = Option.value ~default:(0, 0) (Hashtbl.find_opt o.ops lab) in
        Hashtbl.replace o.ops lab (if is_exn then (v, e + 1) else (v + 1, e)))
    l

(* [run_pair ~old_run ~new_run] runs [chunks] chunks and compares *)
let run_pair ~(old_run : handmade:bool -> seed:int -> n:int -> string)
    ~(new_run : handmade:bool -> seed:int -> n:int -> string) ~stop_at_first
    ~(report : bool) =
  let o =
    {
      compared_chunks = 0;
      compared_lines = 0;
      diffs = 0;
      ops = Hashtbl.create 97;
    }
  in
  (try
     for c = 0 to !chunks - 1 do
       let seed = !seed0 + c in
       let handmade = c = 0 in
       Gc.full_major ();
       let a = old_run ~handmade ~seed ~n:!n in
       Gc.full_major ();
       let b = new_run ~handmade ~seed ~n:!n in
       let la = lines a and lb = lines b in
       o.compared_chunks <- o.compared_chunks + 1;
       o.compared_lines <- o.compared_lines + List.length la;
       record_ops o la;
       match first_diff la lb with
       | None -> ()
       | Some (i, x, y) ->
           o.diffs <- o.diffs + 1;
           if report then (
             Printf.printf
               "DIFF in chunk %d (seed %d), line %d\n  old: %s\n  new: %s\n" c
               seed i x y;
             (* some context: the header of the value *)
             let rec hdr k =
               if k < 0 then ""
               else
                 let l = List.nth la k in
                 if String.length l > 2 && String.sub l 0 2 = "==" then l
                 else hdr (k - 1)
             in
             Printf.printf "  in: %s\n%!" (hdr i));
           if stop_at_first then raise Exit
     done
   with Exit -> ());
  o
