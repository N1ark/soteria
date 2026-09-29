import Bvr.Attr
import Bvr.Float

/-!
# Primitives of the rule language

The Lean counterparts of the primitives declared with `external` in
`rules/prelude.bvr` (other than oracles), and of the integer operators. Where
the OCaml primitive raises (e.g. `Z.log2 0`), the Lean one returns an
arbitrary value: the soundness theorem is about the results that the OCaml code
does return, so this over-approximates it.
-/

namespace Bvr

open Classical

/-! ## Integers, as Zarith's `Z` (two's complement bit operations) -/

def zland : Int → Int → Int
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
def zshiftl (a b : Int) : Int := a * 2 ^ b.toNat

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
  | .mk (.var v) _ => [v]
  | .mk (.ptr a b) _ => a.freeVars ++ b.freeVars
  | .mk (.seq l) _ => Term.freeVarsList l
  | .mk (.unop _ a) _ => a.freeVars
  | .mk (.binop _ a b) _ => a.freeVars ++ b.freeVars
  | .mk (.triop _ a b c) _ => a.freeVars ++ b.freeVars ++ c.freeVars
  | .mk (.nop _ l) _ => Term.freeVarsList l
  | .mk (.exists_ bs body) _ =>
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
  | .bitVector n | .loc n | .pointer n => n
  | _ => 0

def fp_of_ty : Ty → Prec
  | .float p => p
  | _ => .f32

def mk_masked (n z : Int) : Term := .mk (.bitVec (z % 2 ^ n.toNat)) (.bitVector n)

/-- `BitVec.mk` asserts that its argument is in range; where it returns, it is
`mk_masked`. -/
def mk_bv (n z : Int) : Term := mk_masked n z

def bv_zero (n : Int) : Term := .mk (.bitVec 0) (.bitVector n)
def bv_one (n : Int) : Term := .mk (.bitVec 1) (.bitVector n)
def v_true : Term := .mk (.bool true) .bool
def v_false : Term := .mk (.bool false) .bool

/-! ## Bit-vector values -/

/-- A bit-vector value, of width `w`. -/
structure BvVal where
  w : Nat
  x : BitVec w
deriving DecidableEq

def bv_of_lit : Term → BvVal
  | .mk (.bitVec z) t => ⟨(size_of_ty t).toNat, BitVec.ofInt _ z⟩
  | _ => ⟨0, 0⟩

def lit (l : BvVal) : Term := .mk (.bitVec l.x.toNat) (.bitVector l.w)
def width (l : BvVal) : Int := l.w
def to_z (signed : Bool) (l : BvVal) : Int := if signed then l.x.toInt else l.x.toNat
def of_z (n z : Int) : BvVal := ⟨n.toNat, BitVec.ofInt _ z⟩

/-! The operations are at the width of their first operand (the other one is
truncated or extended to it, which is what the OCaml masking does). -/

def lit_add (a b : BvVal) : BvVal := ⟨a.w, a.x + b.x.setWidth a.w⟩
def lit_sub (a b : BvVal) : BvVal := ⟨a.w, a.x - b.x.setWidth a.w⟩
def lit_mul (a b : BvVal) : BvVal := ⟨a.w, a.x * b.x.setWidth a.w⟩
def lit_neg (a : BvVal) : BvVal := ⟨a.w, -a.x⟩
def lit_udiv (a b : BvVal) : BvVal := ⟨a.w, a.x.smtUDiv (b.x.setWidth a.w)⟩
def lit_sdiv (a b : BvVal) : BvVal := ⟨a.w, a.x.smtSDiv (b.x.setWidth a.w)⟩
def lit_and (a b : BvVal) : BvVal := ⟨a.w, a.x &&& b.x.setWidth a.w⟩
def lit_or (a b : BvVal) : BvVal := ⟨a.w, a.x ||| b.x.setWidth a.w⟩
def lit_xor (a b : BvVal) : BvVal := ⟨a.w, a.x ^^^ b.x.setWidth a.w⟩
def lit_not (a : BvVal) : BvVal := ⟨a.w, ~~~a.x⟩
def lit_shl (a b : BvVal) : BvVal := ⟨a.w, a.x <<< b.x.setWidth a.w⟩
def lit_lshr (a b : BvVal) : BvVal := ⟨a.w, a.x >>> b.x.setWidth a.w⟩
def lit_ashr (a b : BvVal) : BvVal := ⟨a.w, a.x.sshiftRight' (b.x.setWidth a.w)⟩
def lit_urem (a b : BvVal) : BvVal := ⟨a.w, a.x.umod (b.x.setWidth a.w)⟩
def lit_srem (a b : BvVal) : BvVal := ⟨a.w, a.x.srem (b.x.setWidth a.w)⟩
def lit_smod (a b : BvVal) : BvVal := ⟨a.w, a.x.smod (b.x.setWidth a.w)⟩
def lit_extract (from_ to_ : Int) (l : BvVal) : BvVal :=
  ⟨(to_ - from_ + 1).toNat, l.x.extractLsb' from_.toNat _⟩
def lit_zext (k : Int) (l : BvVal) : BvVal := ⟨l.w + k.toNat, l.x.setWidth _⟩
def lit_sext (k : Int) (l : BvVal) : BvVal := ⟨l.w + k.toNat, l.x.signExtend _⟩
def lit_concat (l r : BvVal) : BvVal := ⟨l.w + r.w, l.x ++ r.x⟩

/-! ## Floats, as Floatml's `AnyFloat` -/

def fp_size (p : Prec) : Int := p.size

def fp_of_size (n : Int) : Prec :=
  if n = 16 then .f16 else if n = 64 then .f64 else if n = 128 then .f128 else .f32

def f_equal (a b : FloatLit) : Bool := decide (a = b)
def f_bits_equal (a b : FloatLit) : Bool := decide (a = b)
def f_to_bits (f : FloatLit) : Int := f.bits
def f_of_bits (p : Prec) (z : Int) : FloatLit := ⟨p, (z % 2 ^ p.size).toNat⟩
def f_nan (p : Prec) : FloatLit := ⟨p, (FBits.nan p).toNat⟩
def f_is_class (fc : FClass) (f : FloatLit) : Bool := f.val.isClass fc
def f_is_nan (f : FloatLit) : Bool := f.val.isNaN
def f_is_zero (f : FloatLit) : Bool := f.val.isZero
def f_is_negative (f : FloatLit) : Bool := f.val.isNeg
def f_is_positive (f : FloatLit) : Bool := f.val.isPos

def FloatLit.cmp (c : ∀ {p}, FBits p → FBits p → Bool) (a b : FloatLit) : Bool :=
  if h : b.prec = a.prec then c a.val (h ▸ b.val) else false

def f_eq : FloatLit → FloatLit → Bool := FloatLit.cmp FBits.eq
def f_lt : FloatLit → FloatLit → Bool := FloatLit.cmp FBits.lt
def f_le : FloatLit → FloatLit → Bool := FloatLit.cmp FBits.le
def f_abs (f : FloatLit) : FloatLit := ⟨f.prec, (FBits.abs f.val).toNat⟩
def f_neg (f : FloatLit) : FloatLit := ⟨f.prec, (FBits.neg f.val).toNat⟩

end Bvr

namespace Bvr

/-- A guarded result, as the alternatives of `[@cases]` rules are written. -/
def whenSome {α : Type} (c : Bool) (a : α) : Option α := if c then some a else none

/-- The first of a list of options that is [some]. -/
def firstSome {α : Type} : List (Option α) → Option α
  | [] => none
  | o :: os => o <|> firstSome os

end Bvr
