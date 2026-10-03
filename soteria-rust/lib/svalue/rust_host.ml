(* The host types of the rust module that must exist before the generated types
   (rules/rust.knl declares them with [@ocaml "Rust_host.X"]); the others are
   the types of Charon. *)

module Ptr_tag = Ptr_tag

(* The tag of the provenance of a pointer, if it has one *)
type ptag = Ptr_tag.t option

let equal_ptag = Option.equal Ptr_tag.equal
let hash_ptag = function None -> 0 | Some t -> 1 + Ptr_tag.hash t
