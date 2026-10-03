include
  Iface.Typed_intf.S
    with module Svalue = Rust_stack.L.Svalue
     and module Eval = Rust_stack.L.Eval
     and type 'a t = Rust_types.t
     and type 'a ty = Rust_types.ty
