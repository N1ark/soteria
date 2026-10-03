(* The host primitives of the rules ([rules/*.kn]) of the C language, over the
   types that Kanon generates ([Bv_types]): those that the value languages share
   ({!Prim}), applied to the few things that they need of this language. The
   rule functions ([Bv_rules]) call this module and check it against the
   declarations of the rules. *)

include Prim.Make (struct
  include Bv_types
  module L = Logs.Import.L
  module Var = Symex.Var

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

  let used_binders_iter_vars (sv : t) (f : Var.t * ty -> unit) : unit =
    let rec aux ~ignore (sv : t) : unit =
      let aux' = aux ~ignore in
      match sv.kind with
      | Var v -> if Var.Set.mem v ignore then () else f (v, sv.ty)
      | Bool _ | Float _ | BitVec _ | LocLit _ -> ()
      | Op2 (_, l, r) ->
          aux' l;
          aux' r
      | Op1 (_, sv) -> aux' sv
      | Op3 (_, a, b, c) ->
          aux' a;
          aux' b;
          aux' c
      | OpN (_, l) | Seq l -> List.iter aux' l
      | Exists (vs, sv) ->
          let ignore =
            List.fold_left (fun ignore (v, _) -> Var.Set.add v ignore) ignore vs
          in
          aux ~ignore sv
    in
    aux ~ignore:Var.Set.empty sv
end)
