import CoreMod.FBits

/-!
# The primitives of the float module

The primitives that `../rules/float.kn` declares (with `prim`, as Floatml's
`AnyFloat`), on the concrete floats of the core module (`CoreMod.Float`, their
bit patterns `FBits`): `Sem` states that the primitives of a language are these.
-/

namespace FloatMod.Prim

open CoreMod

def fp_size (p : Fp) : Int := p.size

def fp_of_size (n : Int) : Fp :=
  if n = 16 then .F16 else if n = 64 then .F64 else if n = 128 then .F128 else .F32

def f_prec (f : CoreMod.Float) : Fp := f.prec
def f_equal (a b : CoreMod.Float) : Bool := decide (a = b)
def f_bits_equal (a b : CoreMod.Float) : Bool := decide (a = b)
def f_to_bits (f : CoreMod.Float) : Int := f.bits
def f_of_bits (p : Fp) (z : Int) : CoreMod.Float := ⟨p, (z % 2 ^ p.size).toNat⟩
def f_nan (p : Fp) : CoreMod.Float := ⟨p, (FBits.nan p).toNat⟩
def f_is_class (fc : Fc) (f : CoreMod.Float) : Bool := f.val.isClass fc
def f_is_nan (f : CoreMod.Float) : Bool := f.val.isNaN
def f_is_zero (f : CoreMod.Float) : Bool := f.val.isZero
def f_is_negative (f : CoreMod.Float) : Bool := f.val.isNeg
def f_is_positive (f : CoreMod.Float) : Bool := f.val.isPos
def f_eq (a b : CoreMod.Float) : Bool := Float.cmp FBits.eq a b
def f_lt (a b : CoreMod.Float) : Bool := Float.cmp FBits.lt a b
def f_le (a b : CoreMod.Float) : Bool := Float.cmp FBits.le a b
def f_abs (f : CoreMod.Float) : CoreMod.Float := ⟨f.prec, (FBits.abs f.val).toNat⟩
def f_neg (f : CoreMod.Float) : CoreMod.Float := ⟨f.prec, (FBits.neg f.val).toNat⟩

end FloatMod.Prim
