(* The modules of Soteria's generic host stack that this directory uses, under
   one name each. Nothing else of this directory names them; the generated types
   find [View_host] through the [-open Soteria.Bv_values] of the library. *)

module View_host = Soteria.Bv_values.View_host
module Kanon_fns = Soteria.Bv_values.Kanon_fns
module Value_lang = Soteria.Bv_values.Value_lang
module Lang_make = Soteria.Bv_values.Lang_make
module Typed = Soteria.Bv_values.Typed
module Typed_intf = Soteria.Bv_values.Typed_intf
module Svalue_sugar = Soteria.Bv_values.Svalue_sugar
