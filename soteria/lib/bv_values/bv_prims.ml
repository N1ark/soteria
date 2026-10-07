(* The host primitives of the rules ([rules/*.kn]) of the C language, over the
   types that Kanon generates ([Bv_types]): those that the value languages share
   ({!Prim}), applied to the few things that they need of this language. The
   rule functions ([Bv_rules]) call this module and check it against the
   declarations of the rules. *)

include Prim.Make (struct
  include Bv_types
  module L = Logs.Import.L

  let t_bool = TBool
  let t_bv n = TBitVector n
  let t_ptr n = TPointer n
  let k_bool b = Bool b
  let k_bitvec z = BitVec z
  let k_ptr l o = Op2 (Ptr, l, o)
  let k_seq l = Seq l

  let size_of = function
    | TBitVector n | TPointer n | TLoc n -> n
    | _ -> L.failwith "Not a bit value"

  let fp_of_ty = function
    | TFloat fp -> fp
    | _ -> L.failwith "Unsupported float type"

  let as_var (t : t) = match t.kind with Var v -> Some v | _ -> None

  let as_exists (t : t) =
    match t.kind with Exists (vs, body) -> Some (vs, body) | _ -> None
end)
