(* The modules of Soteria's generic host stack that this directory uses, under
   one name each. Nothing else of this directory names them; the generated types
   find [View_host] through the [-open Soteria.Bv_values] of the library. *)

module View_host = Soteria.Bv_values.View_host
module Kanon_fns = Soteria.Bv_values.Kanon_fns
module Value_lang = Soteria.Bv_values.Value_lang
module Lang_v = Soteria.Bv_values.Lang_v
module Typed_v = Soteria.Bv_values.Typed_v
module Typed_intf_v = Soteria.Bv_values.Typed_intf_v
module Svalue_sugar_v = Soteria.Bv_values.Svalue_sugar_v
