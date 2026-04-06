(** Concrete implementation of tree borrows, for testing and debugging. Does not
    support compositionality, just lifts {!Raw} to fit the state model shape. *)

open Soteria.Symex.Compo_res

module Make (Symex : Tree_borrows_intf.Rust_symex) :
  Tree_borrows_intf.M(Symex).S = struct
  open Symex
  include Raw

  module SM =
    Soteria.Sym_states.State_monad.Make
      (Symex)
      (struct
        type nonrec t = t option
      end)

  (* Lift operations symbolically *)

  let nondet_tag () = return None
  let init () = return (init ())
  let init_st _ = return empty_state
  let unwrap x = Option.get ~msg:"missing state in concrete TB" x

  let borrow ?protector parent ~state st =
    let st = unwrap st in
    let st', tag = borrow ?protector parent ~state st in
    return (Ok tag, Some st')

  let unprotect tag st = return (Ok (), Some (unwrap st |> unprotect tag))

  let access accessed e root st =
    match access accessed e (unwrap root) (unwrap st) with
    | Ok st' -> Symex.Result.ok (Some st')
    | Error e -> Symex.Result.error e

  let set_protector ~protected tag t st =
    Result.ok (Some (set_protector ~protected tag (unwrap t) (unwrap st)))

  let strong_protector_exists st = strong_protector_exists (unwrap st)
  let merge l r = return (merge l r)
  let equal_state = Option.equal equal_state

  (* Compositionality *)

  type syn = | [@@deriving show]
  type syn_state = | [@@deriving show]
  type syn_full = Structure of syn | State of syn_state

  let to_syn _ = []
  let ins_outs (s : syn) = match s with _ -> .
  let consume (s : syn) _ = match s with _ -> .
  let produce (s : syn) _ = match s with _ -> .
  let to_syn_state _ = []
  let ins_outs_state (s : syn_state) = match s with _ -> .
  let consume_state (s : syn_state) _ = match s with _ -> .
  let produce_state (s : syn_state) _ = match s with _ -> .
  let fix_empty_state () = []
end
