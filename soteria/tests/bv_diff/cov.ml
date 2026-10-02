(** Coverage by "shape".

    Rule names cannot be observed from outside the generated code, so, as the
    design allows, the coverage of an entry point is the pair (entry point,
    shape of its result), where the shape is:
    - [lit]: a literal;
    - [arg]: one of the (forced) arguments, returned as is;
    - [raw:N]: a node [N] over exactly the arguments (what a plain constructor
      would build: no rule rewrote the call);
    - [rewrite:N]: any other node (a rule rewrote the call into [N]), [N] being
      the constructor of the result's head ([ptr], [seq], [exists] included);
    - [other].

    Every [apply] of every term replayed is recorded, so a term of size [k]
    contributes about [k] samples. Both sides record, and the harness compares
    the sequences call by call. *)

open Tm

type key = string * string

module Instrument
    (S : Side.SIDE)
    (L : sig
      val log : key list ref
      val retain : S.t -> unit
    end) : Side.SIDE with type t = S.t = struct
  include (S : Side.BASE with type t = S.t)

  let shape (r : S.t) (args : S.t list) : string =
    let tags = List.sort compare (List.map S.tag args) in
    match S.view r with
    | VBool _ | VBv _ | VLoc _ | VFloat _ -> "lit"
    | _ when List.exists (fun a -> S.tag a = S.tag r) args -> "arg"
    | VNode (n, l) ->
        let same = List.sort compare (List.map S.tag l) = tags in
        (if same then "raw:" else "rewrite:") ^ node_name n
    | VPtr (l, o) ->
        let same = List.sort compare [ S.tag l; S.tag o ] = tags in
        if same then "raw:ptr" else "rewrite:ptr"
    | VSeq l ->
        let same = List.sort compare (List.map S.tag l) = tags in
        if same then "raw:seq" else "rewrite:seq"
    | VExists _ -> "rewrite:exists"
    | VVar _ -> "other"

  (* every node built through the front is kept alive (see [Bv_diff]) *)
  let keep x =
    L.retain x;
    x

  let mk_var i s = keep (S.mk_var i s)
  let mk_bool b = keep (S.mk_bool b)
  let mk_bv n z = keep (S.mk_bv n z)
  let mk_loc n z = keep (S.mk_loc n z)
  let mk_float p z = keep (S.mk_float p z)
  let mk_ptr l o = keep (S.mk_ptr l o)
  let mk_seq s l = keep (S.mk_seq s l)

  let exists_1 ~not_in s mk =
    let r = S.exists_1 ~not_in s mk in
    L.log := ("exists_1", shape r []) :: !L.log;
    keep r

  let apply op args =
    let forced = ref [] in
    let args' =
      List.map
        (fun a ->
          lazy
            (let v = Lazy.force a in
             forced := v :: !forced;
             v))
        args
    in
    let r = S.apply op args' in
    L.log := (op_name op, shape r (List.rev !forced)) :: !L.log;
    keep r
end
