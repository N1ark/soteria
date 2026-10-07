open Smt

(** Raw pointers are encoded as a pair datatype of location and offset, declared
    on the fly through {!Solvers.Decls}. Exposed to allow extensions to depend
    on it.

    A pointer of width [n] is encoded as a datatype with two fields, both
    bitvectors of width [n]: the location and the offset. *)

(** The SMT-LIB sort for [n]-bit pointers. *)
let name n = quote (Fmt.str "@ptr<%d>" n)

(** The SMT-LIB constructor for [n]-bit pointers; receives the location and
    offset as arguments. *)
let con n = quote (Fmt.str "@mk-ptr<%d>" n)

(** The SMT-LIB constructor for [n]-bit pointers, applied to the location and
    offset terms. *)
let mk_ptr n loc ofs = con n $$. [ loc; ofs ]

(** The SMT-LIB selector for the location of [n]-bit pointers. *)
let loc_sel n = quote (Fmt.str "@ptr<%d>.loc" n)

(** The SMT-LIB selector for the location of [n]-bit pointers, applied to a
    pointer term. *)
let get_loc n ptr = loc_sel n $. ptr

(** The SMT-LIB selector for the offset of [n]-bit pointers. *)
let ofs_sel n = quote (Fmt.str "@ptr<%d>.ofs" n)

(** The SMT-LIB selector for the offset of [n]-bit pointers, applied to a
    pointer term. *)
let get_ofs n ptr = atom (ofs_sel n) $ ptr

(* Declares (at most once) the datatype for [n]-bit pointers; returns its
   sort. *)
let sort n =
  let name = name n in
  Solvers.Decls.declare ~key:name (fun yield ->
      yield
        (declare_datatype name []
           [ (con n, [ (loc_sel n, t_bits n); (ofs_sel n, t_bits n) ]) ]));
  Atom name
