(* The signature of the typed layer of the Rust language: the typed interface
   that Kanon generates ([Rust_typed.S]), extended as the typed layer of the C
   language ([Soteria.Bv_values.Typed], see its typed.mli) *)

module type S = sig
  include Rust_typed.S
  include Iface.Typed_intf.Common with type 'a t := 'a t and type 'a ty := 'a ty

  module Bool : sig
    include module type of Bool
    include Iface.Typed_intf.Bool with type 'a t := 'a t and type 'a ty := 'a ty
  end

  module Bitvec : sig
    include module type of Bitvec
    include Iface.Typed_intf.Bitvec with type 'a t := 'a t
  end

  module Float : sig
    include module type of Float
    include Iface.Typed_intf.Float with type 'a t := 'a t
  end

  module Ptr : sig
    include module type of Ptr
    include Iface.Typed_intf.Ptr with type 'a t := 'a t
  end

  include module type of Bool
end
