(** [bvr ocaml FILE...]: generates the OCaml implementation of the BVR rules in
    [FILE...], on standard output. *)

let () =
  match Array.to_list Sys.argv with
  | _ :: backend :: (_ :: _ as files) -> (
      try
        let str = List.concat_map Check.parse_file files in
        let prog = Check.program str in
        let sources = List.map Filename.basename files in
        match backend with
        | "ocaml" -> Gen_ocaml.program ~sources Format.std_formatter prog
        | "lean-model" -> Gen_lean.model ~sources Format.std_formatter prog
        | "lean-statements" ->
            Gen_lean.statements ~sources Format.std_formatter prog
        | _ ->
            prerr_endline "unknown backend";
            exit 2
      with Check.Error (loc, msg) ->
        Format.eprintf "%a: %s@." Check.pp_loc loc msg;
        exit 1)
  | _ ->
      prerr_endline "usage: bvr (ocaml | lean-model | lean-statements) FILE...";
      exit 2
