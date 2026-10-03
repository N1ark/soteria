(* Raised by the stubs of the interface files that no work package has
   implemented yet. *)

exception Not_implemented of string

let not_implemented what = raise (Not_implemented what)
