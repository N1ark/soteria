(** The items of a typed layer that Kanon does not generate, over the untyped
    layer of a language: the leaves of the terms and the helpers written by
    hand, which {!Typed} (and [Typed_base] of soteria-rust) add to the typed
    interface that Kanon generates for the language. The terms are untyped here;
    the signature of the typed layer ({!Typed_intf}) gives them their tags. The
    operations on the hot path ([sem_eq], [Infix]) are in the typed layer of
    each language, where they call the generated rules directly. *)

module Make (L : Lang_make.S) = struct
  module L_logs = Logs.Import.L
  module Svalue = L.Svalue

  (** The items at the top of the typed layer *)
  module Common = struct
    module Svalue = L.Svalue
    module Eval = L.Eval
    module Expr = L.Expr
    module Lang = L.V
    module FloatPrecision = Svalue.FloatPrecision
    module FloatClass = Svalue.FloatClass
    module RoundingMode = Svalue.RoundingMode

    module T = struct
      type sint = Bv_typed.Tag.tbitvector
      type nonzero = Bv_typed.Tag.tnonzero
      type zero = Bv_typed.Tag.tzero
      type sfloat = Bv_typed.Tag.tfloat
      type sbool = Bv_typed.Tag.tbool
      type sptr = Bv_typed.Tag.tpointer
      type sloc = Bv_typed.Tag.tloc
      type cval = [ sint | sptr | sfloat ]
      type any = [ sint | sfloat | sbool | sptr | sloc ]

      let pp_sint _ _ = ()
      let pp_nonzero _ _ = ()
      let pp_zero _ _ = ()
      let pp_sfloat _ _ = ()
      let pp_sbool _ _ = ()
      let pp_sptr _ _ = ()
      let pp_sloc _ _ = ()
      let pp_any _ _ = ()
      let pp_cval _ _ = ()
      let hash_sint _ = 0
      let hash_nonzero _ = 0
      let hash_zero _ = 0
      let hash_sfloat _ = 0
      let hash_sbool _ = 0
      let hash_sptr _ = 0
      let hash_sloc _ = 0
      let hash_any _ = 0
      let hash_cval _ = 0
    end

    type sbool = T.sbool
    type checked = Bv_base.checked = { signed : bool; unsigned : bool }

    let checked_both = Svalue.checked_both
    let unchecked = Svalue.unchecked
    let checked_of_signed = Svalue.checked_of_signed
    let is_bool_ty = Svalue.is_bool_ty
    let[@inline] get_ty x = Lang.type_of x
    let mk_var = Svalue.mk_var
    let iter_vars = Svalue.iter_vars
    let ppa = Svalue.pp
    let pp _ = Svalue.pp
    let ppa_ty = Svalue.pp_ty
    let pp_ty _ = Svalue.pp_ty
    let equal_ty = Svalue.equal_ty
    let equal = Svalue.equal
    let compare = Svalue.compare
    let hasha = Svalue.hash
    let hash _ = Svalue.hash
    let unique_tag = Svalue.unique_tag
    let[@inline] untyped_list l = l

    let type_checked x ty =
      if Svalue.equal_ty (Lang.type_of x) ty then Some x else None

    let cast_checked = type_checked
    let cast_float x = if Svalue.is_float (Lang.type_of x) then Some x else None

    let cast_int x =
      Option.map (fun n -> (x, n)) (Lang.as_bv_ty (Lang.type_of x))

    let size_of_int x = Svalue.size_of (Lang.type_of x)

    let cast_checked2 x y =
      if Svalue.equal_ty (Lang.type_of x) (Lang.type_of y) then
        Some (x, y, Lang.type_of x)
      else None
  end

  open Common

  module Bool = struct
    let v_true = Svalue.Bool.v_true
    let v_false = Svalue.Bool.v_false
    let of_bool = Svalue.Bool.of_bool
    let to_bool = Svalue.Bool.to_bool
    let and_lazy = Svalue.Bool.and_lazy
    let or_lazy = Svalue.Bool.or_lazy
    let conj = Svalue.Bool.conj
    let split_ands = Svalue.Bool.split_ands
    let distinct_seq = Svalue.Bool.distinct_seq
    let exists_1 = Svalue.Bool.exists_1
    let exists_2 = Svalue.Bool.exists_2
    let exists_3 = Svalue.Bool.exists_3
  end

  module Bitvec = struct
    let mk = Svalue.BitVec.mk
    let mk_masked = Svalue.BitVec.mk_masked
    let mki = Svalue.BitVec.mki
    let zero = Svalue.BitVec.zero
    let one = Svalue.BitVec.one
    let bv_to_z = Svalue.BitVec.bv_to_z
    let to_z = Svalue.BitVec.to_z
    let msb_of = Svalue.BitVec.msb_of

    let mk_nz n z =
      if Z.equal z Z.zero then L_logs.failwith "Zero value in mk_nonzero"
      else mk n z

    let mki_masked n i = mk_masked n (Z.of_int i)

    let mki_nz n i =
      if i = 0 then L_logs.failwith "Zero value in mki_nonzero"
      else mki_masked n i

    let cast_nonzero x = x

    let add_checked ~signed l r =
      ( Svalue.BitVec.add ~checked:(checked_of_signed signed) l r,
        Svalue.BitVec.add_overflows ~signed l r )

    let sub_checked ~signed l r =
      ( Svalue.BitVec.sub ~checked:(checked_of_signed signed) l r,
        Svalue.BitVec.sub_overflows ~signed l r )

    let mul_checked ~signed l r =
      ( Svalue.BitVec.mul ~checked:(checked_of_signed signed) l r,
        Svalue.BitVec.mul_overflows ~signed l r )

    let neg_checked x =
      (Svalue.BitVec.neg ~checked:true x, Svalue.BitVec.neg_overflows x)
  end

  module Float = struct
    let mk = Svalue.Float.mk
    let mk_bits = Svalue.Float.mk_bits
    let of_z = Svalue.Float.of_z
    let to_bits_opt = Svalue.Float.to_bits_opt
    let to_float_opt = Svalue.Float.to_float_opt
    let sign_bit_opt = Svalue.Float.sign_bit_opt
    let approx = Svalue.Float.approx
    let approx2 = Svalue.Float.approx2
    let zero = Svalue.Float.zero
    let neg_zero = Svalue.Float.neg_zero
    let one = Svalue.Float.one
    let nan = Svalue.Float.nan
    let infinity = Svalue.Float.infinity
    let neg_infinity = Svalue.Float.neg_infinity
    let fp_of = Svalue.Float.fp_of
    let minimum = Svalue.Float.minimum
    let maximum = Svalue.Float.maximum
  end

  module Ptr = struct
    let mk = Svalue.Ptr.mk
    let null_loc = Svalue.Ptr.null_loc
    let is_null_loc = Svalue.Ptr.is_null_loc
    let loc_of_z = Svalue.Ptr.loc_of_z
    let loc_of_int = Svalue.Ptr.loc_of_int
    let decompose = Svalue.Ptr.decompose
    let add_ofs = Svalue.Ptr.add_ofs
    let null = Svalue.Ptr.null
    let is_null = Svalue.Ptr.is_null
    let is_at_null_loc = Svalue.Ptr.is_at_null_loc
  end
end
