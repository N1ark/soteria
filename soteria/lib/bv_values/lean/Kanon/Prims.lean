import KanonCore
import Kanon.Float

/-!
# Primitives of the rule language

The Lean counterparts of the primitives declared with `prim` by the modules of
Bv_values (other than oracles), and of the integer operators. Where
the OCaml primitive raises (e.g. `Z.log2 0`), the Lean one returns an
arbitrary value: the soundness theorem is about the results that the OCaml code
does return, so this over-approximates it.
-/

namespace Kanon

open Classical

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

/-! ## Terms -/

mutual
/-- The free variables of a term (see `iter_vars`). -/
def Term.freeVars : Term → List Int
  | .mk (.Var v) _ => [v]
  | .mk (.Seq l) _ => Term.freeVarsList l
  | .mk (.Op1 _ a) _ => a.freeVars
  | .mk (.Op2 _ a b) _ => a.freeVars ++ b.freeVars
  | .mk (.Op3 _ a b c) _ => a.freeVars ++ b.freeVars ++ c.freeVars
  | .mk (.OpN _ l) _ => Term.freeVarsList l
  | .mk (.Exists bs body) _ =>
      body.freeVars.filter (fun v => !(bs.any (fun b => b.1 == v)))
  | .mk _ _ => []

def Term.freeVarsList : List Term → List Int
  | [] => []
  | t :: ts => t.freeVars ++ Term.freeVarsList ts
end

noncomputable def equal (a b : Term) : Bool := decide (a = b)
def ty (v : Term) : Ty := v.ty
def kind (v : Term) : Kind := v.kind

def used_binders (bs : List (Int × Ty)) (body : Term) : List (Int × Ty) :=
  bs.filter (fun b => body.freeVars.contains b.1)

def size_of_ty : Ty → Int
  | .TBitVector n | .TLoc n | .TPointer n => n
  | _ => 0

def fp_of_ty : Ty → Fp
  | .TFloat p => p
  | _ => .F32

def mk_masked (n z : Int) : Term := .mk (.BitVec (z % 2 ^ n.toNat)) (.TBitVector n)

/-- `BitVec.mk` asserts that its argument is in range; where it returns, it is
`mk_masked`. -/
def mk_bv (n z : Int) : Term := mk_masked n z

def bv_zero (n : Int) : Term := .mk (.BitVec 0) (.TBitVector n)
def bv_one (n : Int) : Term := .mk (.BitVec 1) (.TBitVector n)
def v_true : Term := .mk (.Bool true) .TBool
def v_false : Term := .mk (.Bool false) .TBool

/-! ## Bit-vector literals

A bit-vector literal is an integer; the operations on literals take the sorts of
their operands, the first of which gives the width of the result, and reduce
the result modulo `2 ^ width`. -/

def masked (w z : Int) : Int := z % 2 ^ w.toNat

/-- `z` read as a signed integer of `w` bits. -/
def sext_of (w z : Int) : Int := signed_extract z 0 w

def shift_amount (w b : Int) : Option Int :=
  if masked w b < w then some (masked w b) else none

def lit_add (s1 _ : Ty) (a b : Int) : Int := masked (size_of_ty s1) (a + b)
def lit_sub (s1 _ : Ty) (a b : Int) : Int := masked (size_of_ty s1) (a - b)
def lit_mul (s1 _ : Ty) (a b : Int) : Int := masked (size_of_ty s1) (a * b)
def lit_neg (s1 : Ty) (a : Int) : Int := masked (size_of_ty s1) (-a)
def lit_and (s1 _ : Ty) (a b : Int) : Int := masked (size_of_ty s1) (z_land a b)
def lit_or (s1 _ : Ty) (a b : Int) : Int := masked (size_of_ty s1) (zlor a b)
def lit_xor (s1 _ : Ty) (a b : Int) : Int := masked (size_of_ty s1) (zlxor a b)
def lit_not (s1 : Ty) (a : Int) : Int := masked (size_of_ty s1) (zlognot a)

def lit_shl (s1 _ : Ty) (a b : Int) : Int :=
  match shift_amount (size_of_ty s1) b with
  | some s => masked (size_of_ty s1) (z_lsl a s)
  | none => masked (size_of_ty s1) 0

def lit_lshr (s1 _ : Ty) (a b : Int) : Int :=
  match shift_amount (size_of_ty s1) b with
  | some s => masked (size_of_ty s1) (zasr a s)
  | none => masked (size_of_ty s1) 0

def lit_ashr (s1 _ : Ty) (a b : Int) : Int :=
  let n := sext_of (size_of_ty s1) a
  match shift_amount (size_of_ty s1) b with
  | some s => masked (size_of_ty s1) (zasr n s)
  | none => masked (size_of_ty s1) (if n < 0 then -1 else 0)

def lit_smod (s1 _ : Ty) (a b : Int) : Int :=
  let w := size_of_ty s1
  let n := sext_of w a
  let d := sext_of w b
  if d = 0 then a
  else
    let r := trem n d
    if r = 0 ∨ r.sign = d.sign then masked w r else masked w (r + d)

def lit_extract (from_ to_ : Int) (_ : Ty) (a : Int) : Int :=
  masked (to_ - from_ + 1) (zasr a from_)

def lit_concat (_ s2 : Ty) (a b : Int) : Int := zlor (z_lsl a (size_of_ty s2)) b

def lit_udiv (s1 _ : Ty) (a b : Int) : Int :=
  let w := size_of_ty s1
  let d := masked w b
  if d = 0 then masked w (-1) else masked w (tdiv a d)

def lit_sdiv (s1 _ : Ty) (a b : Int) : Int :=
  let w := size_of_ty s1
  let n := sext_of w a
  let d := sext_of w b
  if d = 0 then masked w (if n < 0 then 1 else -1) else masked w (tdiv n d)

def lit_urem (s1 _ : Ty) (a b : Int) : Int :=
  let w := size_of_ty s1
  let d := masked w b
  if d = 0 then a else masked w (trem a d)

def lit_srem (s1 _ : Ty) (a b : Int) : Int :=
  let w := size_of_ty s1
  let n := sext_of w a
  let d := sext_of w b
  if d = 0 then a else masked w (trem n d)

def lit_zext (_ : Int) (_ : Ty) (a : Int) : Int := a

def lit_sext (k : Int) (s1 : Ty) (a : Int) : Int :=
  masked (size_of_ty s1 + k) (sext_of (size_of_ty s1) a)

/-! ## Floats, as Floatml's `AnyFloat` -/

def fp_size (p : Fp) : Int := p.size

def fp_of_size (n : Int) : Fp :=
  if n = 16 then .F16 else if n = 64 then .F64 else if n = 128 then .F128 else .F32

@[simp] def f_prec (f : Float) : Fp := f.prec
def f_equal (a b : Float) : Bool := decide (a = b)
def f_bits_equal (a b : Float) : Bool := decide (a = b)
def f_to_bits (f : Float) : Int := f.bits
def f_of_bits (p : Fp) (z : Int) : Float := ⟨p, (z % 2 ^ p.size).toNat⟩
def f_nan (p : Fp) : Float := ⟨p, (FBits.nan p).toNat⟩
def f_is_class (fc : Fc) (f : Float) : Bool := f.val.isClass fc
def f_is_nan (f : Float) : Bool := f.val.isNaN
def f_is_zero (f : Float) : Bool := f.val.isZero
def f_is_negative (f : Float) : Bool := f.val.isNeg
def f_is_positive (f : Float) : Bool := f.val.isPos

def Float.cmp (c : ∀ {p}, FBits p → FBits p → Bool) (a b : Float) : Bool :=
  if h : b.prec = a.prec then c a.val (h ▸ b.val) else false

def f_eq : Float → Float → Bool := Float.cmp FBits.eq
def f_lt : Float → Float → Bool := Float.cmp FBits.lt
def f_le : Float → Float → Bool := Float.cmp FBits.le
def f_abs (f : Float) : Float := ⟨f.prec, (FBits.abs f.val).toNat⟩
def f_neg (f : Float) : Float := ⟨f.prec, (FBits.neg f.val).toNat⟩

end Kanon
