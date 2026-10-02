(** Stand-in for the new side (used when [bv_new] is not available, or on
    request with [--new standin]): a SECOND, independent instantiation of the
    old simplifier (its own hash-cons table), driven through the raw rule
    functions and {!Side.Compose}, with the {!Mutate} layer on top. Old versus
    this must show zero differences: that validates {!Iso}, the generators and
    the compositions of {!Side.Compose} against the public typed API of the
    other instantiation. *)

module Raw =
  Old_side.Raw_of_typed
    (Old_side.B_typed)
    (struct
      let name = "old#2 (stand-in for bv_new)"
    end)

module Mut = Mutate.Make (Raw)
include Side.Compose (Mut)

let available = false
let label = "old#2 (stand-in: a second instantiation of the old simplifier)"
