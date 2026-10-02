(** Structural isomorphism between a term of side [A] and a term of side [B],
    through {!Tm.view}.

    The terms are equal when they have the same shape, the same literals (floats
    bit for bit), the same parameters (checked flags, signedness, rounding
    modes, precisions, extract bounds) and the same sorts; variables are the
    same when they have the same id. Comparison is memoised on the pair of tags.

    - [Strict]: the operands of every node are compared in order.
    - [Comm]: the operands of the nodes that are [@comm] in the rules
      ({!Tm.is_comm}) are compared as unordered pairs, and those of [Distinct]
      as a multiset. *)

open Tm

type mode = Strict | Comm

module Make (A : Side.BASE) (B : Side.BASE) = struct
  let memo_strict : (int * int, bool) Hashtbl.t = Hashtbl.create 4096
  let memo_comm : (int * int, bool) Hashtbl.t = Hashtbl.create 4096

  let clear () =
    Hashtbl.reset memo_strict;
    Hashtbl.reset memo_comm

  let rec iso mode (a : A.t) (b : B.t) : bool =
    let memo = match mode with Strict -> memo_strict | Comm -> memo_comm in
    let key = (A.tag a, B.tag b) in
    match Hashtbl.find_opt memo key with
    | Some r -> r
    | None ->
        let r = compute mode a b in
        Hashtbl.replace memo key r;
        r

  and compute mode a b =
    A.sort_of a = B.sort_of b
    &&
    match (A.view a, B.view b) with
    | VVar (i, s), VVar (j, s') -> i = j && s = s'
    | VBool x, VBool y -> x = y
    | VBv (n, z), VBv (m, z') | VLoc (n, z), VLoc (m, z') ->
        n = m && Z.equal z z'
    | VFloat (p, z), VFloat (q, z') -> p = q && Z.equal z z'
    | VPtr (l, o), VPtr (l', o') -> iso mode l l' && iso mode o o'
    | VSeq l, VSeq l' -> iso_list mode l l'
    | VNode (n, l), VNode (n', l') -> (
        n = n'
        &&
        match (mode, l, l') with
        | Comm, [ x; y ], [ x'; y' ] when is_comm n ->
            (iso mode x x' && iso mode y y') || (iso mode x y' && iso mode y x')
        | Comm, _, _ when n = N_distinct -> iso_multiset mode l l'
        | _ -> iso_list mode l l')
    | VExists (bs, x), VExists (bs', x') -> bs = bs' && iso mode x x'
    | _ -> false

  and iso_list mode l l' =
    List.compare_lengths l l' = 0 && List.for_all2 (iso mode) l l'

  and iso_multiset mode l l' =
    List.compare_lengths l l' = 0
    &&
    let rec go l rest =
      match l with
      | [] -> rest = []
      | x :: tl -> (
          let rec take acc = function
            | [] -> None
            | y :: r ->
                if iso mode x y then Some (List.rev_append acc r)
                else take (y :: acc) r
          in
          match take [] rest with Some rest -> go tl rest | None -> false)
    in
    go l l'
end
