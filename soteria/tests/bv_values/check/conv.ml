(* The OLD stack ([Typed.Make (Dummy_ext) ()]) and the conversion of a term of
   the new language into a RAW node of the old one: same structure, no
   simplification. The old printers and solver functions applied to the
   converted term are the oracles of the generic layers. *)

open Soteria.Bv_values.Lang.Types
module Old = Soteria.Bv_values.Svalue
module OT = Soteria.Bv_values.Typed.Make (Old.Dummy_ext) ()
module OS = OT.Svalue

let rec conv_ty : ty -> OS.ty = function
  | TBool -> Old.TBool
  | TBitVector n -> Old.TBitVector n
  | TFloat p -> Old.TFloat p
  | TLoc n -> Old.TLoc n
  | TPointer n -> Old.TPointer n
  | TSeq s -> Old.TSeq (conv_ty s)

let tbl : (int, OS.t) Hashtbl.t = Hashtbl.create 1024

let rec conv (v : t) : OS.t =
  match Hashtbl.find_opt tbl v.tag with
  | Some o -> o
  | None ->
      let ty = conv_ty v.ty in
      let ( <| ) = OS.( <| ) in
      let o =
        match v.kind with
        | Var x -> Old.Var x <| ty
        | Seq l -> Old.Seq (List.map conv l) <| ty
        | Bool b -> Old.Bool b <| ty
        | Exists (bs, b) ->
            Old.Exists (List.map (fun (x, s) -> (x, conv_ty s)) bs, conv b)
            <| ty
        | BitVec z | LocLit z -> Old.BitVec z <| ty
        | Float f -> Old.Float f <| ty
        | Op1 (op, a) -> Old.Unop (Kanon_ref.old_unop op, conv a) <| ty
        | Op2 (Ptr, l, o) -> Old.Ptr (conv l, conv o) <| ty
        | Op2 (op, a, b) ->
            Old.Binop (Kanon_ref.old_binop op, conv a, conv b) <| ty
        | Op3 (Ite, a, b, c) ->
            Old.Triop (Old.Triop.Ite, conv a, conv b, conv c) <| ty
        | Op3 (Fma, a, b, c) ->
            Old.Triop (Old.Triop.Fma, conv a, conv b, conv c) <| ty
        | OpN (Distinct, l) -> Old.Nop (Old.Nop.Distinct, List.map conv l) <| ty
      in
      Hashtbl.add tbl v.tag o;
      o
