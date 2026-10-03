(* The modules of Soteria's generic host stack that this directory uses, under
   one name each (they were in soteria/tests/bv_new/iface, library [bv_iface],
   while the stack of the C language was under test). Nothing else of this
   directory names them; the dune flags [-open Soteria.Bv_values] make the
   generated types find [View_host]. *)

module View_host = Soteria.Bv_values.View_host
module Kanon_fns = Soteria.Bv_values.Kanon_fns
module Value_lang = Soteria.Bv_values.Value_lang
module Lang_v = Soteria.Bv_values.Lang_v
module Typed_v = Soteria.Bv_values.Typed_v
module Typed_intf_v = Soteria.Bv_values.Typed_intf_v
module Svalue_sugar_v = Soteria.Bv_values.Svalue_sugar_v
