import CoreMod.Abstract

/-!
# IEEE floats, at the bit level

A float is its IEEE bit pattern; NaN payloads are significant. Classification,
comparisons, `abs` and `neg` (which only touch the sign bit) are defined here;
arithmetic is abstract (see `FloatSem`).
-/

namespace CoreMod

def Fp.size : Fp → Nat
  | .F16 => 16 | .F32 => 32 | .F64 => 64 | .F128 => 128

/-- Exponent bits. -/
def Fp.eb : Fp → Nat
  | .F16 => 5 | .F32 => 8 | .F64 => 11 | .F128 => 15

/-- Stored mantissa bits (without the hidden bit). -/
def Fp.mb : Fp → Nat
  | .F16 => 10 | .F32 => 23 | .F64 => 52 | .F128 => 112

theorem Fp.size_eq (p : Fp) : p.size = 1 + p.eb + p.mb := by cases p <;> rfl

abbrev FBits (p : Fp) := BitVec p.size

namespace FBits

variable {p : Fp}

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

def isClass : Fc → FBits p → Bool
  | .Normal => isNormal
  | .Subnormal => isSubnormal
  | .Zero => isZero
  | .Infinite => isInf
  | .NaN => isNaN

/-- The NaN that represents all NaNs. -/
def nan (p : Fp) : FBits p :=
  BitVec.ofNat _ ((2 ^ p.eb - 1) * 2 ^ p.mb + 2 ^ (p.mb - 1))

def canon (x : FBits p) : FBits p := if x.isNaN then nan p else x

def signMask (p : Fp) : FBits p := BitVec.ofNat _ (2 ^ (p.size - 1))

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
def Float.val (f : Float) : FBits f.prec := BitVec.ofNat _ f.bits

/-- A concrete float is well-formed when its bits fit its precision. -/
def Float.WF (f : Float) : Prop := f.bits < 2 ^ f.prec.size

/-- A comparison of concrete floats, `false` on different precisions. -/
def Float.cmp (c : ∀ {p}, FBits p → FBits p → Bool) (a b : Float) : Bool :=
  if h : b.prec = a.prec then c a.val (h ▸ b.val) else false

end CoreMod
