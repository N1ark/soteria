(** The typed layer of the C tool, over its value language {!Lang}: the typed
    interface that Kanon generates ([Bv_typed.Derived]), extended with the
    leaves and helpers written by hand ({!Typed_extras}), and the operations on
    the hot path, which call the generated rules directly. *)

module X = Typed_extras.Make (Lang.L)
include Bv_typed.Derived
include X.Common

module Bool = struct
  include Bool
  include X.Bool
end

module Bitvec = struct
  include Bitvec
  include X.Bitvec
end

module Float = struct
  include Float
  include X.Float
end

module Ptr = struct
  include Ptr
  include X.Ptr
end

include Bool

let sem_eq (x : 'a t) (y : 'b t) : [> sbool ] t = Bool.eq x (cast y)

let sem_eq_untyped (x : 'a t) (y : 'b t) : [> sbool ] t =
  Bool.eq_untyped x (cast y)

let not = Bool.not_

module Infix = struct
  let ( ==@ ) = sem_eq
  let ( ==?@ ) = sem_eq_untyped
  let ( &&@ ) = Bool.and_
  let ( ||@ ) = Bool.or_
  let ( >@ ) l r = Bitvec.lt false r l
  let ( >=@ ) l r = Bitvec.leq false r l
  let ( <@ ) l r = Bitvec.lt false l r
  let ( <=@ ) l r = Bitvec.leq false l r
  let ( >$@ ) l r = Bitvec.lt true r l
  let ( >=$@ ) l r = Bitvec.leq true r l
  let ( <$@ ) l r = Bitvec.lt true l r
  let ( <=$@ ) l r = Bitvec.leq true l r
  let ( +@ ) l r = Bitvec.add unchecked l r
  let ( -@ ) l r = Bitvec.sub unchecked l r
  let ( ~- ) v = Bitvec.neg false v
  let ( *@ ) l r = Bitvec.mul unchecked l r
  let ( /@ ) l r = Bitvec.div false l r
  let ( /$@ ) l r = Bitvec.div true l r
  let ( %@ ) l r = Bitvec.rem false l r
  let ( %$@ ) l r = Bitvec.rem true l r
  let ( <<@ ) = Bitvec.shl
  let ( >>@ ) = Bitvec.lshr
  let ( >>>@ ) = Bitvec.ashr
  let ( ^@ ) = Bitvec.xor
  let ( &@ ) = Bitvec.and_
  let ( |@ ) = Bitvec.or_
  let ( ==.@ ) = Float.eq
  let ( >.@ ) l r = Float.lt r l
  let ( >=.@ ) l r = Float.leq r l
  let ( <.@ ) = Float.lt
  let ( <=.@ ) = Float.leq
  let ( +.@ ) = Float.add
  let ( -.@ ) = Float.sub
  let ( *.@ ) = Float.mul
  let ( /.@ ) = Float.div
  let ( +!@ ) = ( +@ )
  let ( +!!@ ) l r = Bitvec.add checked_both l r
  let ( -!@ ) = ( -@ )
  let ( -!!@ ) l r = Bitvec.sub checked_both l r
  let ( *!@ ) = ( *@ )
  let ( *!!@ ) l r = Bitvec.mul checked_both l r
  let ( ~-! ) = ( ~- )
  let ( ~-!! ) v = Bitvec.neg true v
  let ( +?@ ) = Bitvec.add_checked ~signed:false
  let ( +$?@ ) = Bitvec.add_checked ~signed:true
  let ( -?@ ) = Bitvec.sub_checked ~signed:false
  let ( -$?@ ) = Bitvec.sub_checked ~signed:true
  let ( *?@ ) = Bitvec.mul_checked ~signed:false
  let ( *$?@ ) = Bitvec.mul_checked ~signed:true
  let ( ~-? ) = Bitvec.neg_checked
end
