/-!
# The primitives of the bitvec module, on integers

The meaning of the primitives that `../rules/bitvec.kn` declares (with
`prim`), as the OCaml code of the rules computes them over Zarith's `Z`. The
operations on literals take the width of the sort of their first operand
(`size_of_ty`) instead of the sort; `Sem.lean` and `Prims.lean` give them to
the rules.

Where the OCaml primitive raises (e.g. `Z.log2 0`), the Lean one returns an
arbitrary value: the soundness theorem is about the results that the OCaml code
does return, so this over-approximates it.
-/

namespace BitvecMod.Prim

/-! ## Integers, as Zarith's `Z` (two's complement bit operations) -/

def z_land : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m &&& n)
  | .ofNat m, .negSucc n => .ofNat (Nat.bitwise (fun a b => a && !b) m n)
  | .negSucc m, .ofNat n => .ofNat (Nat.bitwise (fun a b => !a && b) m n)
  | .negSucc m, .negSucc n => .negSucc (m ||| n)

def zlor : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m ||| n)
  | .ofNat m, .negSucc n => .negSucc (Nat.bitwise (fun a b => !a && b) m n)
  | .negSucc m, .ofNat n => .negSucc (Nat.bitwise (fun a b => a && !b) m n)
  | .negSucc m, .negSucc n => .negSucc (m &&& n)

def zlxor : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m ^^^ n)
  | .ofNat m, .negSucc n => .negSucc (m ^^^ n)
  | .negSucc m, .ofNat n => .negSucc (m ^^^ n)
  | .negSucc m, .negSucc n => .ofNat (m ^^^ n)

def zlognot (a : Int) : Int := -a - 1

/-- `Z.shift_left` (which raises on a negative shift). -/
def z_lsl (a b : Int) : Int := a * 2 ^ b.toNat

/-- `Z.shift_right`, rounding towards minus infinity. -/
def zasr (a b : Int) : Int := a / 2 ^ b.toNat

def popcountNat : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) % 2 + popcountNat ((n + 1) / 2)

def popcount (z : Int) : Int := popcountNat z.toNat
def log2 (z : Int) : Int := Nat.log2 z.toNat
def tdiv (a b : Int) : Int := a.tdiv b
def trem (a b : Int) : Int := a.tmod b
def divisible (a b : Int) : Bool := decide (b ∣ a)

/-- `Z.signed_extract z o l`: the [l] bits of [z] from [o], read as a signed
integer. -/
def signed_extract (z o l : Int) : Int :=
  let u := zasr z o % 2 ^ l.toNat
  if 2 ^ (l.toNat - 1) ≤ u then u - 2 ^ l.toNat else u

/-! ## Bit-vector literals, of width `w` -/

def masked (w z : Int) : Int := z % 2 ^ w.toNat

/-- `z` read as a signed integer of `w` bits. -/
def sext_of (w z : Int) : Int := signed_extract z 0 w

def shift_amount (w b : Int) : Option Int :=
  if masked w b < w then some (masked w b) else none

def lit_add (w a b : Int) : Int := masked w (a + b)
def lit_sub (w a b : Int) : Int := masked w (a - b)
def lit_mul (w a b : Int) : Int := masked w (a * b)
def lit_neg (w a : Int) : Int := masked w (-a)
def lit_and (w a b : Int) : Int := masked w (z_land a b)
def lit_or (w a b : Int) : Int := masked w (zlor a b)
def lit_xor (w a b : Int) : Int := masked w (zlxor a b)
def lit_not (w a : Int) : Int := masked w (zlognot a)

def lit_shl (w a b : Int) : Int :=
  match shift_amount w b with
  | some s => masked w (z_lsl a s)
  | none => masked w 0

def lit_lshr (w a b : Int) : Int :=
  match shift_amount w b with
  | some s => masked w (zasr a s)
  | none => masked w 0

def lit_ashr (w a b : Int) : Int :=
  let n := sext_of w a
  match shift_amount w b with
  | some s => masked w (zasr n s)
  | none => masked w (if n < 0 then -1 else 0)

def lit_smod (w a b : Int) : Int :=
  let n := sext_of w a
  let d := sext_of w b
  if d = 0 then a
  else
    let r := trem n d
    if r = 0 ∨ r.sign = d.sign then masked w r else masked w (r + d)

def lit_extract (from_ to_ a : Int) : Int := masked (to_ - from_ + 1) (zasr a from_)

/-- The concatenation of `a` and `b`, of width `w2`. -/
def lit_concat (w2 a b : Int) : Int := zlor (z_lsl a w2) b

def lit_udiv (w a b : Int) : Int :=
  let d := masked w b
  if d = 0 then masked w (-1) else masked w (tdiv a d)

def lit_sdiv (w a b : Int) : Int :=
  let n := sext_of w a
  let d := sext_of w b
  if d = 0 then masked w (if n < 0 then 1 else -1) else masked w (tdiv n d)

def lit_urem (w a b : Int) : Int :=
  let d := masked w b
  if d = 0 then a else masked w (trem a d)

def lit_srem (w a b : Int) : Int :=
  let n := sext_of w a
  let d := sext_of w b
  if d = 0 then a else masked w (trem n d)

def lit_zext (a : Int) : Int := a

/-- The sign extension by `k` bits of `a`, of width `w`. -/
def lit_sext (k w a : Int) : Int := masked (w + k) (sext_of w a)

end BitvecMod.Prim
