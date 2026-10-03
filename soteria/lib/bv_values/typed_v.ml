(** The typed layer over any language, successor of [typed.ml]: the phantom tags
    [T], the identity layer ([type +'a t = t], [cast] = identity) and the
    [Bool]/[BitVec]/[Infix] sugar of [typed.ml:33-166], in content unchanged.
    There is no constructor matching in it: [get_ty], [cast_float], [cast_int]
    go through the term record and {!Kanon_fns.Kanon_fns.as_float_ty}/[as_bv_ty]
    (via {!Svalue_sugar_v}). Written by the architect as the reference
    implementation; WP3b owns it from now on.

    [Make_transparent] exposes [t] and [ty] as the underlying untyped terms,
    like the old [Typed.Make_transparent]: Rust writes its extension helpers on
    top of it. The [Value_ext] hooks of Rust ([Ext.mk/eval/apply_subst/learn],
    [Ext.pp/encode_*]) are not here any more: they are the [extend fn] cases of
    its language ({!Kanon_fns.Kanon_fns}). *)

open Deps

module Make_transparent (L : Typed_intf_v.Language) : sig
  include
    Typed_intf_v.S
      with module Svalue = L.Svalue
       and module Eval = L.Eval
       and type 'a t = L.V.t
       and type 'a ty = L.V.ty
end = struct
  module L_logs = Soteria.Logs.Import.L
  module Svalue = L.Svalue
  module Eval = L.Eval
  module Lang : Solver_lang.S with type t = L.V.t and type ty = L.V.ty = L.V
  module Expr = L.Expr
  include Svalue

  module T = struct
    type sint = [ `NonZero | `Zero ]
    type sint_ovf = [ `NonZero | `Zero | `Overflowed ]
    type nonzero = [ `NonZero ]
    type zero = [ `Zero ]
    type sfloat = [ `Float ]
    type sbool = [ `Bool ]
    type sptr = [ `Ptr ]
    type sloc = [ `Loc ]
    type 'a sseq = [ `List of 'a ]
    type cval = [ sint | sptr | sfloat ]
    type any = [ sint_ovf | sfloat | sbool | sptr | sloc | any sseq ]

    let pp_sint _ _ = ()
    let pp_sint_ovf _ _ = ()
    let pp_nonzero _ _ = ()
    let pp_zero _ _ = ()
    let pp_sfloat _ _ = ()
    let pp_sbool _ _ = ()
    let pp_sptr _ _ = ()
    let pp_sloc _ _ = ()
    let pp_sseq _ _ _ = ()
    let pp_any _ _ = ()
    let pp_cval _ _ = ()
    let hash_sint _ = 0
    let hash_sint_ovf _ = 0
    let hash_nonzero _ = 0
    let hash_zero _ = 0
    let hash_sfloat _ = 0
    let hash_sbool _ = 0
    let hash_sptr _ = 0
    let hash_sloc _ = 0
    let hash_sseq _ = 0
    let hash_any _ = 0
    let hash_cval _ = 0
  end

  type nonrec +'a t = Svalue.t
  type nonrec +'a ty = Svalue.ty
  type sbool = T.sbool

  let t_int = t_bv

  include Bool

  let[@inline] get_ty x = L.V.type_of x
  let[@inline] type_type x = x
  let[@inline] untype_type x = x
  let ppa = pp
  let pp _ = pp
  let ppa_ty = pp_ty
  let pp_ty _ = pp_ty
  let hasha = hash
  let hash _ = hash
  let[@inline] cast x = x
  let[@inline] untyped x = x
  let[@inline] untyped_list l = l
  let[@inline] type_ x = x
  let type_checked x ty = if equal_ty (L.V.type_of x) ty then Some x else None
  let cast_checked = type_checked
  let cast_float x = if is_float (L.V.type_of x) then Some x else None

  let cast_int x =
    if is_bv (L.V.type_of x) then Some (x, size_of (L.V.type_of x)) else None

  let size_of_int x = size_of (L.V.type_of x)

  let cast_checked2 x y =
    if equal_ty (L.V.type_of x) (L.V.type_of y) then Some (x, y, L.V.type_of x)
    else None

  module Bool = struct
    include Bool

    type t = sbool
  end

  module BitVec = struct
    include BitVec

    let mk_nz n z =
      if Z.equal z Z.zero then L_logs.failwith "Zero value in mk_nonzero"
      else mk n z

    let mki_masked n i = mk_masked n (Z.of_int i)

    let mki_nz n i =
      if i = 0 then L_logs.failwith "Zero value in mki_nonzero"
      else mki_masked n i

    let no_ovf_unsafe x = x
    let cast_nonzero x = x

    let add_checked ~signed l r =
      (add ~checked:(checked_of_signed signed) l r, add_overflows ~signed l r)

    let sub_checked ~signed l r =
      (sub ~checked:(checked_of_signed signed) l r, sub_overflows ~signed l r)

    let mul_checked ~signed l r =
      (mul ~checked:(checked_of_signed signed) l r, mul_overflows ~signed l r)

    let neg_checked x = (neg ~checked:true x, neg_overflows x)
  end

  module Infix = struct
    include Infix

    let ( +!@ ) = ( +@ )
    let ( +!!@ ) = BitVec.add ~checked:checked_both
    let ( -!@ ) = ( -@ )
    let ( -!!@ ) = BitVec.sub ~checked:checked_both
    let ( *!@ ) = ( *@ )
    let ( *!!@ ) = BitVec.mul ~checked:checked_both
    let ( ~-! ) = ( ~- )
    let ( ~-!! ) = BitVec.neg ~checked:true
    let ( +?@ ) = BitVec.add_checked ~signed:false
    let ( +$?@ ) = BitVec.add_checked ~signed:true
    let ( -?@ ) = BitVec.sub_checked ~signed:false
    let ( -$?@ ) = BitVec.sub_checked ~signed:true
    let ( *?@ ) = BitVec.mul_checked ~signed:false
    let ( *$?@ ) = BitVec.mul_checked ~signed:true
    let ( ~-? ) = BitVec.neg_checked
  end
end

(** Like {!Make_transparent}, with [t] and [ty] kept abstract. *)
module Make (L : Typed_intf_v.Language) :
  Typed_intf_v.S with module Svalue = L.Svalue and module Eval = L.Eval =
  Make_transparent (L)
