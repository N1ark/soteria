import KanonCore.Sem
import KanonCore.BoolMod.Val
import Kanon.Model
import Kanon.Typing

/-!
# Semantics of svalues, and soundness of simplifications

`eval FS ρ t` is the value of the term `t` under the environment `ρ`, following
the SMT-LIB encoding of `encoding.ml`, with `none` standing for *poison*:

- ill-typed terms (see `Term.WT`) are poison;
- checked operations (`Add {signed}`, `Neg true`, ...) whose no-overflow flag
  does not hold are poison, like LLVM's `nsw`;
- the nodes of the bool module are evaluated by the operations of Kanon's
  library (`Kanon.BoolMod.Val`): `ite` only evaluates the branch it selects,
  and `&&` / `||` are "parallel": a `false` (resp. `true`) operand wins over a
  poisoned one.

A smart constructor is sound when its result *refines* the raw node it
simplifies (`Refines`): the result has the same sort, and whenever the raw node
evaluates to a value, the result evaluates to the same value. Under a model of
a path condition, all flags hold, and refinement is plain equality.

Floats are exact IEEE bit patterns: unlike in SMT-LIB, NaNs with different
payloads are different values (SMT-LIB's single NaN is an approximation made by
the solver encoding, not something the simplifications may rely on).
Floating-point arithmetic is abstract (`FloatSem`); `Oracle.Compat` states what
the proofs assume of Floatml's concrete operations and of the hash-consing
order.
-/

noncomputable section

namespace Kanon

open Classical BoolMod

/-! ## Types and values -/

/-- Types that have values: bit-vectors have a positive width. -/
def Ty.WF : Ty → Prop
  | .TLoc n | .TPointer n | .TBitVector n => 0 < n
  | .TSeq t => t.WF
  | _ => True

inductive Val where
  | bool (b : Bool)
  | bv (n : Nat) (x : BitVec n)
  | ptr (n : Nat) (l o : BitVec n)
  | float (p : Fp) (x : FBits p)
  | seq (vs : List Val)

mutual
def Val.hasSort : Val → Ty → Prop
  | .bool _, .TBool => True
  | .bv n _, .TBitVector m => (n : Int) = m ∧ 0 < n
  | .bv n _, .TLoc m => (n : Int) = m ∧ 0 < n
  | .ptr n _ _, .TPointer m => (n : Int) = m ∧ 0 < n
  | .float p _, .TFloat q => p = q
  | .seq vs, .TSeq t => Val.hasSortList vs t
  | _, _ => False

def Val.hasSortList : List Val → Ty → Prop
  | [], _ => True
  | v :: vs, t => v.hasSort t ∧ Val.hasSortList vs t
end

def Val.hasTy (v : Val) (t : Ty) : Prop := v.hasSort t

structure Env where
  var : Int → Option Val

/-- Floating-point operations, abstractly, as functions on bit patterns (so
NaN payloads are whatever the implementation produces). -/
structure FloatSem where
  add : (p : Fp) → FBits p → FBits p → FBits p
  sub : (p : Fp) → FBits p → FBits p → FBits p
  mul : (p : Fp) → FBits p → FBits p → FBits p
  div : (p : Fp) → FBits p → FBits p → FBits p
  rem : (p : Fp) → FBits p → FBits p → FBits p
  min : (p : Fp) → FBits p → FBits p → FBits p
  max : (p : Fp) → FBits p → FBits p → FBits p
  fma : (p : Fp) → FBits p → FBits p → FBits p → FBits p
  sqrt : (p : Fp) → FBits p → FBits p
  round : Rm → (p : Fp) → FBits p → FBits p
  convert : Rm → (p q : Fp) → FBits p → FBits q
  toBv : Rm → Bool → (n : Nat) → (p : Fp) → FBits p → BitVec n
  ofBv : Rm → Bool → (p : Fp) → (n : Nat) → BitVec n → FBits p

/-! ## Well-typed terms -/

/-! The typing of the operators, `Op1.WT`, `Op2.WT`, `Op3.WT` and `OpN.WT` (over
the type of all the operands of an n-ary operator), is generated from the
declarations of the nodes in `Typing.lean`. -/

mutual
/-- Syntactic well-typedness. -/
def Term.WT : Term → Prop
  | .mk (.Var _) _ => True
  | .mk (.Bool _) t => t = .TBool
  | .mk (.Float f) t => t = .TFloat f.prec ∧ f.bits < 2 ^ f.prec.size
  | .mk (.BitVec z) t => ∃ n : Nat, 0 < n ∧ t = .TBitVector n ∧ 0 ≤ z ∧ z < 2 ^ n
  | .mk (.LocLit z) t => ∃ n : Nat, 0 < n ∧ t = .TLoc n ∧ 0 ≤ z ∧ z < 2 ^ n
  | .mk (.Seq l) t => ∃ e, t = .TSeq e ∧ Term.WTList e l
  | .mk (.Op1 op a) t => op.WT a.ty t ∧ a.WT
  | .mk (.Op2 op a b) t => op.WT a.ty b.ty t ∧ a.WT ∧ b.WT
  | .mk (.Op3 op a b c) t => op.WT a.ty b.ty c.ty t ∧ a.WT ∧ b.WT ∧ c.WT
  | .mk (.OpN op l) t => ∃ e, op.WT e t ∧ Term.WTList e l
  | .mk (.Exists bs body) t =>
      t = .TBool ∧ (bs.map Prod.fst).Nodup ∧ (∀ b ∈ bs, b.2.WF) ∧ body.ty = .TBool ∧ body.WT

/-- All the terms are well-typed, of the sort of [e]. -/
def Term.WTList (e : Ty) : List Term → Prop
  | [] => True
  | x :: xs => x.ty = e ∧ x.WT ∧ Term.WTList e xs
end

/-! ## Evaluation -/

/-- The width of a bit-vector (or location, or pointer) type. -/
def Ty.width (t : Ty) : Nat := (size_of_ty t).toNat

def Float.sem (f : Float) : Val := .float f.prec f.val

/-- Binary bit-vector operations, on operands of the same width. -/
def bvBin (f : ∀ {n : Nat}, BitVec n → BitVec n → Option Val) :
    Option Val → Option Val → Option Val
  | some (.bv n x), some (.bv m y) => if h : m = n then f x (h ▸ y) else none
  | _, _ => none

def fBin (f : (p : Fp) → FBits p → FBits p → Option Val) :
    Option Val → Option Val → Option Val
  | some (.float p x), some (.float q y) => if h : q = p then f p x (h ▸ y) else none
  | _, _ => none

def fArith (f : (p : Fp) → FBits p → FBits p → FBits p) :=
  fBin (fun p x y => some (.float p (f p x y)))

/-- An arithmetic operation, poisoned when it overflows in a checked
signedness. -/
def checkedOp (c : Checked) (sovf uovf : ∀ {n : Nat}, BitVec n → BitVec n → Bool)
    (f : ∀ {n : Nat}, BitVec n → BitVec n → BitVec n) :=
  bvBin (fun x y =>
    if (c.signed && sovf x y) || (c.unsigned && uovf x y) then none
    else some (.bv _ (f x y)))

def evOp1 (FS : FloatSem) : Op1 → Option Val → Option Val
  | .Not, a => pnot Val.bool a
  | .GetPtrLoc, some (.ptr n l _) => some (.bv n l)
  | .GetPtrOfs, some (.ptr n _ o) => some (.bv n o)
  | .BvOfBool n, some (.bool b) => some (.bv n.toNat (if b then 1 else 0))
  | .BvOfFloat rm s n, some (.float p x) => some (.bv n.toNat (FS.toBv rm s n.toNat p x))
  | .FloatOfBv rm s p, some (.bv n x) => some (.float p (FS.ofBv rm s p n x))
  | .FloatOfBvRaw p, some (.bv n x) =>
      if h : n = p.size then some (.float p (x.cast h)) else none
  | .FloatOfFloat rm p, some (.float q x) => some (.float p (FS.convert rm q p x))
  | .BvExtract i j, some (.bv _ x) =>
      some (.bv (j - i + 1).toNat (x.extractLsb' i.toNat _))
  | .BvExtend s k, some (.bv n x) =>
      some (.bv (n + k.toNat) (if s then x.signExtend _ else x.setWidth _))
  | .BvNot, some (.bv n x) => some (.bv n (~~~x))
  | .Neg c, some (.bv n x) => if c && x = BitVec.intMin n then none else some (.bv n (-x))
  | .FAbs, some (.float p x) => some (.float p x.abs)
  | .FNeg, some (.float p x) => some (.float p x.neg)
  | .FSqrt, some (.float p x) => some (.float p (FS.sqrt p x))
  | .FRound rm, some (.float p x) => some (.float p (FS.round rm p x))
  | .FIs fc, some (.float _ x) => some (.bool (x.isClass fc))
  | .FIsNeg, some (.float _ x) => some (.bool x.isNeg)
  | .FIsPos, some (.float _ x) => some (.bool x.isPos)
  | _, _ => none

def evPtr : Option Val → Option Val → Option Val
  | some (.bv n l), some (.bv m o) => if h : m = n then some (.ptr n l (h ▸ o)) else none
  | _, _ => none

def evOp2 (FS : FloatSem) : Op2 → Option Val → Option Val → Option Val
  | .And, a, b => pand Val.bool a b
  | .Or, a, b => por Val.bool a b
  | .Eq, a, b => peq Val.bool a b
  | .FEq, a, b => fBin (fun _ x y => some (.bool (x.eq y))) a b
  | .FLeq, a, b => fBin (fun _ x y => some (.bool (x.le y))) a b
  | .FLt, a, b => fBin (fun _ x y => some (.bool (x.lt y))) a b
  | .FAdd, a, b => fArith FS.add a b
  | .FSub, a, b => fArith FS.sub a b
  | .FMul, a, b => fArith FS.mul a b
  | .FDiv, a, b => fArith FS.div a b
  | .FRem, a, b => fArith FS.rem a b
  | .FMin, a, b => fArith FS.min a b
  | .FMax, a, b => fArith FS.max a b
  | .Add c, a, b => checkedOp c BitVec.saddOverflow BitVec.uaddOverflow (· + ·) a b
  | .Sub c, a, b => checkedOp c BitVec.ssubOverflow BitVec.usubOverflow (· - ·) a b
  | .Mul c, a, b => checkedOp c BitVec.smulOverflow BitVec.umulOverflow (· * ·) a b
  | .Div s, a, b =>
      bvBin (fun x y => some (.bv _ (if s then x.smtSDiv y else x.smtUDiv y))) a b
  | .Rem s, a, b => bvBin (fun x y => some (.bv _ (if s then x.srem y else x.umod y))) a b
  | .Mod, a, b => bvBin (fun x y => some (.bv _ (x.smod y))) a b
  | .AddOvf s, a, b =>
      bvBin (fun x y => some (.bool (if s then x.saddOverflow y else x.uaddOverflow y))) a b
  | .SubOvf s, a, b =>
      bvBin (fun x y => some (.bool (if s then x.ssubOverflow y else x.usubOverflow y))) a b
  | .MulOvf s, a, b =>
      bvBin (fun x y => some (.bool (if s then x.smulOverflow y else x.umulOverflow y))) a b
  | .Lt s, a, b => bvBin (fun x y => some (.bool (if s then x.slt y else x.ult y))) a b
  | .Leq s, a, b => bvBin (fun x y => some (.bool (if s then x.sle y else x.ule y))) a b
  | .BvConcat, some (.bv n x), some (.bv m y) => some (.bv (n + m) (x ++ y))
  | .BvConcat, _, _ => none
  | .BitAnd, a, b => bvBin (fun x y => some (.bv _ (x &&& y))) a b
  | .BitOr, a, b => bvBin (fun x y => some (.bv _ (x ||| y))) a b
  | .BitXor, a, b => bvBin (fun x y => some (.bv _ (x ^^^ y))) a b
  | .Shl, a, b => bvBin (fun x y => some (.bv _ (x <<< y))) a b
  | .LShr, a, b => bvBin (fun x y => some (.bv _ (x >>> y))) a b
  | .AShr, a, b => bvBin (fun x y => some (.bv _ (x.sshiftRight' y))) a b
  | .Ptr, a, b => evPtr a b

def evFma (FS : FloatSem) : Option Val → Option Val → Option Val → Option Val
  | some (.float p x), some (.float q y), some (.float r z) =>
      if h : q = p ∧ r = p then
        some (.float p (FS.fma p x (h.1 ▸ y) (h.2 ▸ z)))
      else none
  | _, _, _ => none

def evOp3 (FS : FloatSem) : Op3 → Option Val → Option Val → Option Val → Option Val
  | .Ite, g, a, b => pite Val.bool g a b
  | .Fma, a, b, c => evFma FS a b c

def evOpN : OpN → Option (List Val) → Option Val
  | .Distinct, vs => pdistinct Val.bool vs

/-- The environments that differ from [ρ] only on the variables bound by
[bs], which they give values of the right types. -/
def Env.Extends (ρ' ρ : Env) (bs : List (Int × Ty)) : Prop :=
  (∀ v, (∀ b ∈ bs, b.1 ≠ v) → ρ'.var v = ρ.var v) ∧
    ∀ b ∈ bs, ∃ x, ρ'.var b.1 = some x ∧ x.hasTy b.2

mutual
/-- Evaluation, assuming well-typedness. -/
def ev (FS : FloatSem) : Env → Term → Option Val
  | ρ, .mk (.Var v) t =>
      match ρ.var v with
      | some x => if x.hasTy t then some x else none
      | none => none
  | _, .mk (.Bool b) _ => some (.bool b)
  | _, .mk (.Float f) _ => some f.sem
  | _, .mk (.BitVec z) t => some (.bv t.width (BitVec.ofInt _ z))
  | _, .mk (.LocLit z) t => some (.bv t.width (BitVec.ofInt _ z))
  | ρ, .mk (.Seq l) _ => (evList FS ρ l).map .seq
  | ρ, .mk (.Op1 op a) _ => evOp1 FS op (ev FS ρ a)
  | ρ, .mk (.Op2 op a b) _ => evOp2 FS op (ev FS ρ a) (ev FS ρ b)
  | ρ, .mk (.Op3 op a b c) _ => evOp3 FS op (ev FS ρ a) (ev FS ρ b) (ev FS ρ c)
  | ρ, .mk (.OpN op l) _ => evOpN op (evList FS ρ l)
  | ρ, .mk (.Exists bs body) _ =>
      if ∀ ρ', ρ'.Extends ρ bs → ∃ b, ev FS ρ' body = some (.bool b) then
        some (.bool (decide (∃ ρ', ρ'.Extends ρ bs ∧ ev FS ρ' body = some (.bool true))))
      else none

def evList (FS : FloatSem) : Env → List Term → Option (List Val)
  | _, [] => some []
  | ρ, t :: ts =>
      match ev FS ρ t, evList FS ρ ts with
      | some v, some vs => some (v :: vs)
      | _, _ => none
end

/-! ## Refinement

The value of a term and refinement are Kanon's (`Kanon.Sem`), for the
semantics `sem FS` of svalues. -/

/-- The semantics of svalues, with the floating-point operations `FS`. -/
@[reducible] def sem (FS : FloatSem) : Sem where
  Term := Term
  Ty := Ty
  Val := Val
  Env := Env
  ty := Term.ty
  WT := Term.WT
  ev := ev FS

/-- The value of a term; `none` for poison. -/
abbrev eval (FS : FloatSem) : Env → Term → Option Val := (sem FS).eval

/-- [r] refines [spec]: it has the same type, and the same value whenever
[spec] is not poison. -/
abbrev Refines (FS : FloatSem) : Term → Term → Prop := (sem FS).Refines

instance {FS : FloatSem} : Refinement (Refines FS) := Sem.refinement

/-- A term is not zero: whenever it has a bit-vector value, it is not zero, whatever the semantics of floats `FS`. This is
the meaning of the subsort `TNonzero` (`[@lean "Nonzero"]`), which the statements
of the rules assume of the divisor of `Div` and `Rem`. -/
def Nonzero (t : Term) : Prop := ∀ FS ρ n (x : BitVec n), eval FS ρ t = some (.bv n x) → x ≠ 0

/-- A term is zero: whenever it has a bit-vector value, it is zero (`TZero`), whatever `FS`. -/
def Zero (t : Term) : Prop := ∀ FS ρ n (x : BitVec n), eval FS ρ t = some (.bv n x) → x = 0

/-! ## Assumptions on the oracles -/

def Float.WF (f : Float) : Prop := f.bits < 2 ^ f.prec.size

/-- The literal term of a float. -/
def Float.term (f : Float) : Term := .mk (.Float f) (.TFloat f.prec)

/-- What the proofs assume of the oracles: that sorting by tags permutes a list,
and that Floatml computes, on literals, the same values (bit patterns) as the
float operations (of the same precision). -/
structure Oracle.Compat (orc : Oracle) (FS : FloatSem) : Prop where
  sort_by_tag : ∀ l, (orc.sort_by_tag l).Perm l
  bin : ∀ (op : Op2) (lit : Float → Float → Float),
    (op, lit) ∈ [(.FAdd, orc.f_add), (.FSub, orc.f_sub), (.FMul, orc.f_mul),
      (.FDiv, orc.f_div), (.FRem, orc.f_rem), (.FMin, orc.f_min), (.FMax, orc.f_max)] →
    ∀ f1 f2, f1.WF → f2.WF → f1.prec = f2.prec →
      (lit f1 f2).prec = f1.prec ∧ (lit f1 f2).WF ∧
        evOp2 FS op (some f1.sem) (some f2.sem) = some (lit f1 f2).sem
  fma : ∀ f1 f2 f3, f1.WF → f2.WF → f3.WF → f1.prec = f2.prec → f1.prec = f3.prec →
    (orc.f_fma f1 f2 f3).prec = f1.prec ∧ (orc.f_fma f1 f2 f3).WF ∧
      evFma FS (some f1.sem) (some f2.sem) (some f3.sem) = some (orc.f_fma f1 f2 f3).sem
  sqrt : ∀ f, f.WF → (orc.f_sqrt f).prec = f.prec ∧ (orc.f_sqrt f).WF ∧
    evOp1 FS .FSqrt (some f.sem) = some (orc.f_sqrt f).sem
  round : ∀ rm f, f.WF → (orc.f_round rm f).prec = f.prec ∧ (orc.f_round rm f).WF ∧
    evOp1 FS (.FRound rm) (some f.sem) = some (orc.f_round rm f).sem
  convert : ∀ rm p f, f.WF → (orc.f_convert rm p f).prec = p ∧ (orc.f_convert rm p f).WF ∧
    evOp1 FS (.FloatOfFloat rm p) (some f.sem) = some (orc.f_convert rm p f).sem
  to_int : ∀ rm s n f z, f.WF → 0 < n → orc.f_to_int rm s n f = some z →
    evOp1 FS (.BvOfFloat rm s n) (some f.sem) = some (.bv n.toNat (BitVec.ofInt _ z))
  of_int : ∀ rm s p n z f, 0 < n → 0 ≤ z → z < 2 ^ n.toNat → orc.f_of_int rm s p n z = some f →
    f.prec = p ∧ f.WF ∧
      evOp1 FS (.FloatOfBv rm s p) (some (.bv n.toNat (BitVec.ofInt _ z))) = some f.sem
  /-- C's [fmod] agrees with its emulation from the IEEE remainder. -/
  fmod : ∀ f1 f2 ρ, f1.WF → f2.WF → f1.prec = f2.prec →
    (orc.f_fmod f1 f2).prec = f1.prec ∧ (orc.f_fmod f1 f2).WF ∧
      eval FS ρ (raw_fmod_of_rem (.mk (.Op2 .FRem f1.term f2.term) (.TFloat f1.prec))
        f1.term f2.term) = some (orc.f_fmod f1 f2).sem

end Kanon

end
