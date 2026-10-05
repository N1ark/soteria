import CoreMod.Syntax

/-!
# What the core module needs of the semantics of a language

The core module (`../rules/core.knl`) declares the variables, the sequences
and their sort, and has no rules: its interface (`CoreMod.Syntax`, generated)
is what the modules that use it see of these nodes, and its proofs need nothing
of the semantics.
-/

namespace CoreMod

open Kanon

/-- What the core module needs of the semantics `S` of a language, for its
interface `L`: nothing. -/
class Sem {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
    (L : Syntax B) where

end CoreMod
