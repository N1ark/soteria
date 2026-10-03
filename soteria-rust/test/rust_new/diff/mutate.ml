(* [mutate.exe FILE] prints FILE with every mutation of {!Mutations} applied
   (each guarded by [Mut.on k]). Fails if a text to replace does not occur
   exactly once: the self-test must not silently test nothing. *)

let read f = In_channel.with_open_bin f In_channel.input_all

let count s sub =
  let n = String.length sub in
  let rec go i acc =
    if i + n > String.length s then acc
    else if String.sub s i n = sub then go (i + n) (acc + 1)
    else go (i + 1) acc
  in
  go 0 0

let replace s sub by =
  let n = String.length sub in
  let rec find i = if String.sub s i n = sub then i else find (i + 1) in
  let i = find 0 in
  String.sub s 0 i ^ by ^ String.sub s (i + n) (String.length s - i - n)

let () =
  let s = ref (read Sys.argv.(1)) in
  List.iter
    (fun (m : Mutations.t) ->
      if count !s m.find <> 1 then (
        Printf.eprintf "mutation %d (%s): the text to replace occurs %d times\n"
          m.k m.name (count !s m.find);
        exit 1);
      s := replace !s m.find m.replace)
    Mutations.all;
  print_string !s
