(* The typed layer of the Rust language without its own types, over the value
   language of {!Rust_stack}: the phantom-typed smart constructors that Kanon
   generates ({!Rust_typed.Derived}), the groups of tags, and the wrappers that
   give them the public API ({!Iface.Typed_intf.S}). The leaves and the
   operations that the rules do not type come from the untyped layer
   ({!Rust_stack.L.Svalue}). It is the analogue of [Bv_values.Typed] for the C
   language. *)

module L_logs = Soteria.Logs.Import.L
module L = Rust_stack.L
module G = Rust_typed.Derived
include L.Svalue
include G
module Svalue = L.Svalue
module Eval = L.Eval
module Expr = L.Expr
module Lang : Solver_lang.S with type t = L.V.t and type ty = L.V.ty = L.V

module T = struct
  type sint = Rust_typed.Tag.tbitvector
  type nonzero = Rust_typed.Tag.tnonzero
  type zero = Rust_typed.Tag.tzero
  type sfloat = Rust_typed.Tag.tfloat
  type sbool = Rust_typed.Tag.tbool
  type sptr = Rust_typed.Tag.tpointer
  type sloc = Rust_typed.Tag.tloc
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

let t_bool = G.Bool.t_bool
let t_int = G.Bitvec.t_bitvector
let t_ptr = G.Ptr.t_pointer
let t_loc = G.Ptr.t_loc
let t_float = G.Float.t_float
let t_f16 = t_float F16
let t_f32 = t_float F32
let t_f64 = t_float F64
let t_f128 = t_float F128

module Bool_ = struct
  include L.Svalue.Bool

  let and_ = G.Bool.b_and
  let or_ = G.Bool.b_or
  let not = G.Bool.b_not
  let ite = G.Bool.b_ite
  let distinct = G.Bool.b_distinct
end

include Bool_

module Bool = struct
  include Bool_

  type t = sbool
end

let sem_eq (x : 'a t) (y : 'b t) : [> sbool ] t = G.Bool.sem_eq x (cast y)

let sem_eq_untyped (x : 'a t) (y : 'b t) : [> sbool ] t =
  G.Bool.sem_eq_untyped x (cast y)

let[@inline] get_ty x = L.V.type_of x
let ppa = pp
let pp _ = pp
let ppa_ty = pp_ty
let pp_ty _ = pp_ty
let hasha = hash
let hash _ = hash
let[@inline] untyped_list l = l
let type_checked x ty = if equal_ty (L.V.type_of x) ty then Some x else None
let cast_checked = type_checked
let cast_float x = if is_float (L.V.type_of x) then Some x else None

let cast_int x =
  if is_bv (L.V.type_of x) then Some (x, size_of (L.V.type_of x)) else None

let size_of_int x = size_of (L.V.type_of x)

let cast_checked2 x y =
  if equal_ty (L.V.type_of x) (L.V.type_of y) then Some (x, y, L.V.type_of x)
  else None

module BitVec = struct
  include L.Svalue.BitVec

  let add ?(checked = unchecked) l r = G.Bitvec.bv_add checked l r
  let sub ?(checked = unchecked) l r = G.Bitvec.bv_sub checked l r
  let mul ?(checked = unchecked) l r = G.Bitvec.bv_mul checked l r
  let div ~signed l r = G.Bitvec.bv_div signed l r
  let rem ~signed l r = G.Bitvec.bv_rem signed l r
  let mod_ = G.Bitvec.bv_mod
  let neg ?(checked = false) v = G.Bitvec.bv_neg checked v
  let add_overflows ~signed l r = G.Bitvec.bv_add_overflows signed l r
  let sub_overflows ~signed l r = G.Bitvec.bv_sub_overflows signed l r
  let mul_overflows ~signed l r = G.Bitvec.bv_mul_overflows signed l r
  let neg_overflows = G.Bitvec.bv_neg_overflows
  let lt ~signed l r = G.Bitvec.bv_lt signed l r
  let leq ~signed l r = G.Bitvec.bv_leq signed l r
  let gt ~signed l r = lt ~signed r l
  let geq ~signed l r = leq ~signed r l
  let concat = G.Bitvec.bv_concat
  let extend ~signed by v = G.Bitvec.bv_extend signed (Z.of_int by) v

  let extract from_ to_ v =
    G.Bitvec.bv_extract (Z.of_int from_) (Z.of_int to_) v

  let and_ = G.Bitvec.bv_and
  let or_ = G.Bitvec.bv_or
  let xor = G.Bitvec.bv_xor
  let shl = G.Bitvec.bv_shl
  let lshr = G.Bitvec.bv_lshr
  let ashr = G.Bitvec.bv_ashr
  let not = G.Bitvec.bv_not
  let of_bool n b = G.Bitvec.bv_of_bool (Z.of_int n) b
  let to_bool = G.Bitvec.bv_to_bool
  let not_bool = G.Bitvec.bv_not_bool

  let of_float ~rounding ~signed ~size v =
    G.Bitvec.bv_of_float rounding signed (Z.of_int size) v

  let to_float ~rounding ~signed ~fp v =
    G.Bitvec.bv_to_float rounding signed fp v

  let to_float_raw = G.Bitvec.bv_to_float_raw

  let mk_nz n z =
    if Z.equal z Z.zero then L_logs.failwith "Zero value in mk_nonzero"
    else mk n z

  let mki_masked n i = mk_masked n (Z.of_int i)

  let mki_nz n i =
    if i = 0 then L_logs.failwith "Zero value in mki_nonzero"
    else mki_masked n i

  let cast_nonzero x = x

  let add_checked ~signed l r =
    (add ~checked:(checked_of_signed signed) l r, add_overflows ~signed l r)

  let sub_checked ~signed l r =
    (sub ~checked:(checked_of_signed signed) l r, sub_overflows ~signed l r)

  let mul_checked ~signed l r =
    (mul ~checked:(checked_of_signed signed) l r, mul_overflows ~signed l r)

  let neg_checked x = (neg ~checked:true x, neg_overflows x)
end

module Float = struct
  include L.Svalue.Float

  let is_floatclass = G.Float.float_is_floatclass
  let is_normal v = is_floatclass Normal v
  let is_subnormal v = is_floatclass Subnormal v
  let is_infinite v = is_floatclass Infinite v
  let is_nan v = is_floatclass NaN v
  let is_zero v = is_floatclass Zero v
  let is_negative = G.Float.float_is_negative
  let is_positive = G.Float.float_is_positive
  let cast ~rounding ~fp v = G.Float.float_cast rounding fp v
  let eq = G.Float.float_eq
  let lt = G.Float.float_lt
  let leq = G.Float.float_leq
  let gt l r = lt r l
  let geq l r = leq r l
  let add = G.Float.float_add
  let sub = G.Float.float_sub
  let mul = G.Float.float_mul
  let div = G.Float.float_div
  let rem = G.Float.float_rem
  let abs = G.Float.float_abs
  let neg = G.Float.float_neg
  let fma = G.Float.float_fma
  let fmod_of_rem = G.Float.float_fmod_of_rem
  let fmod = G.Float.float_fmod
  let min = G.Float.float_min
  let max = G.Float.float_max
  let sqrt = G.Float.float_sqrt
  let round rm v = G.Float.float_round rm v
end

module Ptr = struct
  include L.Svalue.Ptr

  let loc = G.Ptr.ptr_loc
  let ofs = G.Ptr.ptr_ofs
end

module Infix = struct
  let ( ==@ ) = sem_eq
  let ( ==?@ ) = sem_eq_untyped
  let ( &&@ ) = Bool.and_
  let ( ||@ ) = Bool.or_
  let ( >@ ) = BitVec.gt ~signed:false
  let ( >=@ ) = BitVec.geq ~signed:false
  let ( <@ ) = BitVec.lt ~signed:false
  let ( <=@ ) = BitVec.leq ~signed:false
  let ( >$@ ) = BitVec.gt ~signed:true
  let ( >=$@ ) = BitVec.geq ~signed:true
  let ( <$@ ) = BitVec.lt ~signed:true
  let ( <=$@ ) = BitVec.leq ~signed:true
  let ( +@ ) l r = BitVec.add l r
  let ( -@ ) l r = BitVec.sub l r
  let ( ~- ) v = BitVec.neg v
  let ( *@ ) l r = BitVec.mul l r
  let ( /@ ) = BitVec.div ~signed:false
  let ( /$@ ) = BitVec.div ~signed:true
  let ( %@ ) = BitVec.rem ~signed:false
  let ( %$@ ) = BitVec.rem ~signed:true
  let ( <<@ ) = BitVec.shl
  let ( >>@ ) = BitVec.lshr
  let ( >>>@ ) = BitVec.ashr
  let ( ^@ ) = BitVec.xor
  let ( &@ ) = BitVec.and_
  let ( |@ ) = BitVec.or_
  let ( ==.@ ) = Float.eq
  let ( >.@ ) = Float.gt
  let ( >=.@ ) = Float.geq
  let ( <.@ ) = Float.lt
  let ( <=.@ ) = Float.leq
  let ( +.@ ) = Float.add
  let ( -.@ ) = Float.sub
  let ( *.@ ) = Float.mul
  let ( /.@ ) = Float.div
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
