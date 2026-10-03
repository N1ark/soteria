(* The cost of the arrays, the one place where the new language is expected to
   be slower: an array is an [Iarray] in the old one (O(1) access, O(1) length)
   and a list in the new one (O(i) access, O(n) length, conversions at the
   interface). Same code for both stacks ([Ty] is defined by the file that
   precedes it). Returns [(operation, seconds per run)]. *)

open Charon
module Adt = Ty.Adt
module BV = Ty.BV
module T = Ty.T

let u8t : Types.ty = TLiteral (TUInt U8)

let time ~reps f =
  Gc.full_major ();
  let t0 = Sys.time () in
  for _ = 1 to reps do
    ignore (Sys.opaque_identity (f ()))
  done;
  (Sys.time () -. t0) /. float_of_int reps

let next_var = ref 0

let fresh_array_var n =
  incr next_var;
  Ty.mk_var
    (Soteria.Symex.Var.of_int !next_var)
    (Ty.type_type
       (Ty.get_ty
          (Adt.mk_array u8t (Iarray.init n (fun i -> BV.u8i (i land 255))))))

let run ~n ~reps =
  let elems = Iarray.init n (fun i -> BV.u8i (i land 255)) in
  let conc = Adt.mk_array u8t elems in
  let all_fields v () =
    let s = ref 0 in
    for i = 0 to n - 1 do
      ignore (Sys.opaque_identity (Adt.array_field_of i v));
      incr s
    done;
    !s
  in
  [
    ( "mk_array (concrete, " ^ string_of_int n ^ " elements)",
      time ~reps:(reps * 10) (fun () -> Adt.mk_array u8t elems) );
    ( "array_field_of, last element (concrete)",
      time ~reps:(reps * 100) (fun () -> Adt.array_field_of (n - 1) conc) );
    ( "array_field_of, first element (concrete)",
      time ~reps:(reps * 100) (fun () -> Adt.array_field_of 0 conc) );
    ( "array_field_of, every element in turn (concrete)",
      time ~reps (all_fields conc) );
    ("as_array (concrete)", time ~reps:(reps * 10) (fun () -> Adt.as_array conc));
    ( "as_array (symbolic: creates n ArrayField nodes)",
      time ~reps (fun () -> Adt.as_array (fresh_array_var n)) );
    ( "array_field_of, last element (symbolic)",
      let v = fresh_array_var n in
      time ~reps:(reps * 100) (fun () -> Adt.array_field_of (n - 1) v) );
    ( "set_array_field, middle (concrete)",
      time ~reps:(reps * 10) (fun () ->
          Adt.set_array_field (n / 2) (BV.u8i 7) conc) );
    ( "set_array_field, middle (symbolic)",
      let v = fresh_array_var n in
      time ~reps (fun () -> Adt.set_array_field (n / 2) (BV.u8i 7) v) );
  ]
