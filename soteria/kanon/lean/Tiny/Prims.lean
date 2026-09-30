import KanonCore
import Tiny.Syntax

/-!
# Primitives of the rule language

The Lean counterparts of the primitives declared with `prim` by the modules of
Tiny_values (other than oracles), as `soteria/lib/tiny_values/svalue.ml`
implements them. Where the OCaml primitive raises (`Z.div`, `Z.rem`, `Z.ediv`
and `Z.erem` on a zero divisor), the Lean one returns an arbitrary value (Lean's
own): the soundness theorem is about the results that the OCaml code does
return, so this over-approximates it.
-/

namespace Tiny

open Classical

/-! ## Terms -/

noncomputable def equal (a b : Term) : Bool := decide (a = b)
def ty (v : Term) : Ty := v.ty
def kind (v : Term) : Kind := v.kind

def v_true : Term := .mk (.Bool true) .TBool
def v_false : Term := .mk (.Bool false) .TBool
def int_z (z : Int) : Term := .mk (.Int z) .TInt
def zero : Term := int_z 0
def one : Term := int_z 1

def var_equal (a b : Int) : Bool := decide (a = b)

/-! ## Integers, as Zarith's `Z` -/

/-- `Z.div`: truncated division. -/
def tdiv (a b : Int) : Int := a.tdiv b
/-- `Z.rem`: the remainder of the truncated division, of the sign of `a`. -/
def trem (a b : Int) : Int := a.tmod b
/-- `Z.divisible` (only `0` is divisible by `0`). -/
def divisible (a b : Int) : Bool := decide (b ∣ a)
/-- `Z.ediv`: Euclidean division, which is Lean's `/`. -/
def ediv (a b : Int) : Int := a / b
/-- `Z.erem`: Euclidean remainder, which is Lean's `%`. -/
def erem (a b : Int) : Int := a % b

end Tiny
