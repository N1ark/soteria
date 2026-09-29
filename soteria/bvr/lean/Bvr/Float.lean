import Bvr.Syntax

/-!
# IEEE floats, at the bit level

A float is its IEEE bit pattern; NaN payloads are significant. Classification,
comparisons, `abs` and `neg` (which only touch the sign bit) are defined here;
arithmetic is abstract (see `FloatSem`).
-/

namespace Bvr

def Prec.size : Prec → Nat
  | .f16 => 16 | .f32 => 32 | .f64 => 64 | .f128 => 128

/-- Exponent bits. -/
def Prec.eb : Prec → Nat
  | .f16 => 5 | .f32 => 8 | .f64 => 11 | .f128 => 15

/-- Stored mantissa bits (without the hidden bit). -/
def Prec.mb : Prec → Nat
  | .f16 => 10 | .f32 => 23 | .f64 => 52 | .f128 => 112

theorem Prec.size_eq (p : Prec) : p.size = 1 + p.eb + p.mb := by cases p <;> rfl

abbrev FBits (p : Prec) := BitVec p.size

namespace FBits

variable {p : Prec}

def mant (x : FBits p) : Nat := x.toNat % 2 ^ p.mb
def expo (x : FBits p) : Nat := x.toNat / 2 ^ p.mb % 2 ^ p.eb
def sign (x : FBits p) : Bool := x.msb

def isNaN (x : FBits p) : Bool := x.expo == 2 ^ p.eb - 1 && x.mant != 0
def isInf (x : FBits p) : Bool := x.expo == 2 ^ p.eb - 1 && x.mant == 0
def isZero (x : FBits p) : Bool := x.expo == 0 && x.mant == 0
def isSubnormal (x : FBits p) : Bool := x.expo == 0 && x.mant != 0
def isNormal (x : FBits p) : Bool := x.expo != 0 && x.expo != 2 ^ p.eb - 1

/-- SMT-LIB [fp.isNegative] / [fp.isPositive]: false on NaN. -/
def isNeg (x : FBits p) : Bool := !x.isNaN && x.sign
def isPos (x : FBits p) : Bool := !x.isNaN && !x.sign

def isClass : FClass → FBits p → Bool
  | .normal => isNormal
  | .subnormal => isSubnormal
  | .zero => isZero
  | .infinite => isInf
  | .nan => isNaN

/-- The NaN that represents all NaNs. -/
def nan (p : Prec) : FBits p :=
  BitVec.ofNat _ ((2 ^ p.eb - 1) * 2 ^ p.mb + 2 ^ (p.mb - 1))

def canon (x : FBits p) : FBits p := if x.isNaN then nan p else x

def signMask (p : Prec) : FBits p := BitVec.ofNat _ (2 ^ (p.size - 1))

/-- The magnitude of a float, with a sign: IEEE floats are ordered like this
key, NaNs aside, and with both zeros at 0. -/
def key (x : FBits p) : Int :=
  let mag : Int := (x.toNat % 2 ^ (p.size - 1) : Nat)
  if x.sign then -mag else mag

def eq (x y : FBits p) : Bool :=
  !x.isNaN && !y.isNaN && (x == y || (x.isZero && y.isZero))

def lt (x y : FBits p) : Bool := !x.isNaN && !y.isNaN && decide (x.key < y.key)
def le (x y : FBits p) : Bool := !x.isNaN && !y.isNaN && decide (x.key ≤ y.key)

def abs (x : FBits p) : FBits p := x &&& ~~~(signMask p)
def neg (x : FBits p) : FBits p := x ^^^ signMask p

end FBits

/-- The bit pattern of a concrete float. -/
def FloatLit.val (f : FloatLit) : FBits f.prec := BitVec.ofNat _ f.bits

end Bvr
