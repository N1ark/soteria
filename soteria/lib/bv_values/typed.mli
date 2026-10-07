include sig
    include Bv_typed.S
    include Typed_intf.Common with type 'a t := 'a t and type 'a ty := 'a ty

    module Bool : sig
      include module type of Bool
      include Typed_intf.Bool with type 'a t := 'a t and type 'a ty := 'a ty
    end

    module Bitvec : sig
      include module type of Bitvec
      include Typed_intf.Bitvec with type 'a t := 'a t
    end

    module Float : sig
      include module type of Float
      include Typed_intf.Float with type 'a t := 'a t
    end

    module Ptr : sig
      include module type of Ptr
      include Typed_intf.Ptr with type 'a t := 'a t
    end

    include module type of Bool
  end
  with module Svalue = Lang.Svalue
   and module Eval = Lang.Eval
