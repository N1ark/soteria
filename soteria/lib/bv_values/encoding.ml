open Soteria_std
open Smt
module Ptr_sort = Ptr_sort

(** Lowers the values of a language [L] into SMT terms and sorts for the Z3
    backend, memoising the encoding of values. *)
module Make (L : Solver_lang.S) = struct
  type t = L.t
  type ty = L.ty

  let rec sort_of_ty ty = L.encode_ty ~sort_of_ty ty

  let memo_encode_value_tbl : (sexp * Solvers.Decls.t list) L.Hashtbl.t =
    L.Hashtbl.create 1023

  let rec encode_value (v : L.t) =
    L.encode_node ~sort_of_ty ~encode_child:encode_value_memo v

  and encode_value_memo v =
    match L.Hashtbl.find_opt memo_encode_value_tbl v with
    | Some (k, decls) ->
        List.iter (fun d -> Effect.perform (Solvers.Decls.Declare d)) decls;
        k
    | None ->
        let decls = ref [] in
        let k =
          try encode_value v
          with effect Solvers.Decls.Declare d, cont ->
            decls := d :: !decls;
            (* forward to the solver's own handler *)
            Effect.perform (Solvers.Decls.Declare d);
            Effect.Deep.continue cont ()
        in
        L.Hashtbl.add memo_encode_value_tbl v (k, List.rev !decls);
        k

  let encode_value (v : L.t) =
    L.split_ands v |> Iter.map encode_value_memo |> Iter.to_list |> bool_ands

  let init_commands = []
end
