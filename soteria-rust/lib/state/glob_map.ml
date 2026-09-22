open Svalue
open Charon
module SM_Base = Rustsymex

(* HACK: do we need to normalise the generics in some way? e.g. so
   STATIC::<usize> and STATIC::<Id::<usize>> point to the same thing, where
   [type Id<T> = T] *)

(* NOTE: globals are lazily initialised: [load] returns [None] when a global is
   absent, and the interpreter then evaluates the initialiser and allocates a
   block for it. For statics this is not frame preserving: the binding (and its
   block) may be in the frame, so in compositional mode [load] should miss
   instead. For consts and string literals, Rust does not guarantee address
   identity, so allocating a fresh block per use is sound. *)

type global = String of string | Global of Types.global_decl_ref
[@@deriving show { with_path = false }, ord, eq]

module Key = struct
  type t = global [@@deriving show { with_path = false }, ord]
end

module Abstr = Soteria.Data.Abstr.M (SM_Base)

module Entry =
  Soteria.Sym_states.Agree.Make
    (SM_Base)
    (Abstr.With_syn_of_value (struct
      type ty = Typed.T.sptr_f

      let ty () = Typed.t_ptr_f ()
    end))

include Soteria.Sym_states.Pmap.Concrete (SM_Base) (Key) (Entry)

(** Loads a global from the global map; if it doesn't exist, will invoke
    [f () super_st], which must return the pointer the global will point to.
    Returns the pointer, along with a flag indicating whether the entry existed.
    Using that flag may break the frame if used incorrectly. *)
let load g f super_st =
  wrap_with_lift_fixes ~lift_fixes:Fun.id g
    (let open Entry.SM in
     let open Syntax in
     (* Whether this global is a constant, i.e. it can never be mutated. If that
        is the case, then we can freely use [f] to generate the pointer, as we
        are guaranteed that it will be frame preserving. Put differently, for
        constant globals, we treat the pointed-to value as a [Pure_fun], where
        [f] is the [fresh] function. *)
     let is_const =
       match g with
       | String _ -> true
       | Global g ->
           Common.Alloc_kind.global_kind_is_const
             (Crate.get_global g).global_kind
     in
     let* st = get_state () in
     match (Config.get_mode (), is_const, st) with
     (* we have the state -- nothing to do! *)
     | _, _, Some curr -> Result.ok (curr, `Present, super_st)
     (* we have a constant; this behaves like a [Pure_fun] *)
     | _, true, None
     (* we have a static, but are in whole program mode: we can use [f], there
        is no frame *)
     | Whole_program, false, None ->
         let*^ res, super_st = f () super_st in
         let** ptr = return res in
         let* () = set_state (Some ptr) in
         Result.ok (ptr, `Fresh, super_st)
     (* we have a static, and are in compositional mode; this behaves like a
        [Ag] and this must miss *)
     | Compositional, false, None ->
         Result.miss_no_fix ~reason:"missing static" ())
