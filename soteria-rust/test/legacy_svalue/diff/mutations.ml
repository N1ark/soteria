(* The deliberate errors of the self-test: each replaces ONE piece of text of
   the generated rules (rust_rules.gen.ml) by a wrong one, active only when
   [Mut.current] is its number (see mutate.ml, mut/dune). The text to replace
   must occur exactly once. *)

type t = { k : int; name : string; find : string; replace : string }

let all =
  [
    {
      k = 1;
      name = "field_of of a tuple reads the next field";
      find = "| { kind = Tuple (vs); _ } -> (Rust_prims.nth_term vs idx)";
      replace =
        "| { kind = Tuple (vs); _ } -> (Rust_prims.nth_term vs (if Mut.on 1 \
         then Z.succ idx else idx))";
    };
    {
      k = 2;
      name = "the size of a thin pointer is its alignment";
      find = "      | (PtrSize) -> s\n";
      replace = "      | (PtrSize) -> (if Mut.on 2 then a else s)\n";
    };
    {
      k = 3;
      name = "is_variant of an enum is negated";
      find = "-> (of_bool ((equal_variant_id var cur)))";
      replace =
        "-> (of_bool ((if Mut.on 3 then not else Fun.id) (equal_variant_id var \
         cur)))";
    };
    {
      k = 4;
      name = "the length of the metadata of a full pointer is its own node";
      find = "| ((PartLen), (MetaLen (len))) -> len";
      replace =
        "| ((PartLen), (MetaLen (len))) -> (if Mut.on 4 then v else len)";
    };
    {
      k = 5;
      name = "array_field_of of an array reads the next element";
      find = "| { kind = Array (vs); _ } -> (Rust_prims.iarray_get vs idx)";
      replace =
        "| { kind = Array (vs); _ } -> (Rust_prims.iarray_get vs (if Mut.on 5 \
         then Z.succ idx else idx))";
    };
    {
      k = 6;
      name = "set_field sets the next field";
      find = "(mk_tuple (Rust_prims.set_nth (as_tuple v) idx x))";
      replace =
        "(mk_tuple (Rust_prims.set_nth (as_tuple v) (if Mut.on 6 then Z.succ \
         idx else idx) x))";
    };
    {
      k = 7;
      name = "an array is built with a wrong length in its sort";
      find = "(TArray (elem, (Rust_prims.iarray_length vs)))";
      replace =
        "(TArray (elem, (if Mut.on 7 then Z.succ (Rust_prims.iarray_length vs) \
         else Rust_prims.iarray_length vs)))";
    };
    {
      k = 8;
      name =
        "the operands of a thin pointer have the size and the alignment swapped";
      find = "palign = a; _ }); _ } ->\n      (p :: (s :: (a :: [])))";
      replace =
        "palign = a; _ }); _ } ->\n\
        \      (if Mut.on 8 then (p :: (a :: (s :: []))) else (p :: (s :: (a \
         :: []))))";
    };
    {
      k = 9;
      name = "rebuild of a tuple reverses its fields";
      find = "| { kind = Tuple (_); _ } -> (mk_tuple cs)";
      replace =
        "| { kind = Tuple (_); _ } -> (mk_tuple (if Mut.on 9 then List.rev cs \
         else cs))";
    };
    {
      k = 10;
      name = "a tuple learns each field from the next field of the value";
      find = "(Some (field_of k v))";
      replace = "(Some (field_of (if Mut.on 10 then Z.succ k else k) v))";
    };
  ]
