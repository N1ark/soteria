(** [bvr (lean-types | lean-syntax) LANG]: generates the Lean definitions of the
    types of the language declared in [LANG].

    [bvr (ocaml | lean-model | lean-statements | lean-lifts | lean-soundness)
     LANG FILE...]: generates the OCaml implementation or the Lean model of the
    BVR rules in [FILE...], written in that language.

    The output is written on standard output. *)

let () =
  match Array.to_list Sys.argv with
  | _ :: backend :: lang :: files -> (
      try
        Check.language (Check.parse_file lang);
        let ft = Format.std_formatter in
        match (backend, files) with
        | "lean-types", [] ->
            Gen_lean.types ~sources:[ Filename.basename lang ] ft
        | "lean-syntax", [] ->
            Gen_lean.syntax ~sources:[ Filename.basename lang ] ft
        | _, _ :: _ -> (
            let str = List.concat_map Check.parse_file files in
            let prog = Check.program str in
            let sources = List.map Filename.basename files in
            match backend with
            | "ocaml" -> Gen_ocaml.program ~sources ft prog
            | "lean-model" -> Gen_lean.model ~sources ft prog
            | "lean-statements" -> Gen_lean.statements ~sources ft prog
            | "lean-lifts" -> Gen_lean.lifts ~sources ft prog
            | "lean-soundness" ->
                Gen_lean.soundness ~sources ~proofs:[ "Bvr.Proofs" ] ft prog
            | _ ->
                prerr_endline "unknown backend";
                exit 2)
        | _ ->
            prerr_endline "unknown backend, or wrong number of files";
            exit 2
      with Check.Error (loc, msg) ->
        Format.eprintf "%a: %s@." Check.pp_loc loc msg;
        exit 1)
  | _ ->
      prerr_endline
        "usage: bvr (lean-types | lean-syntax) LANG\n\
        \       bvr (ocaml | lean-model | lean-statements | lean-lifts | \
         lean-soundness) LANG FILE...";
      exit 2
