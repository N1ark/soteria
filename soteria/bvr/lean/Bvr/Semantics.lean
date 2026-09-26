import Bvr.Model

/-!
# Semantics of svalues, and soundness of simplifications

`eval FS ρ t` is the value of the term `t` under the environment `ρ`, following
the SMT-LIB encoding of `encoding.ml`, with `none` standing for *poison*:

- ill-typed terms (see `Term.WT`) are poison;
- checked operations (`Add {signed}`, `Neg true`, ...) whose no-overflow flag
  does not hold are poison, like LLVM's `nsw`;
- `ite` only evaluates the branch it selects, and `&&` / `||` are "parallel":
  a `false` (resp. `true`) operand wins over a poisoned one.

A smart constructor is sound when its result *refines* the raw node it
simplifies (`Refines`): the result has the same sort, and whenever the raw node
evaluates to a value, the result evaluates to the same value. Under a model of
a path condition, all flags hold, and refinement is plain equality.

Floating-point arithmetic is abstract (`FloatSem`); `Oracle.Compat` states what
the proofs assume of Floatml's concrete operations and of the hash-consing
order.
-/

noncomputable section

namespace Bvr

open Classical

/-! ## Sorts and values -/

/-- The SMT sort of a type: locations are bit-vectors. -/
def Ty.sort : Ty → Ty
  | .loc n => .bitVector n
  | .seq t => .seq t.sort
  | t => t

inductive Val where
  | bool (b : Bool)
  | bv (n : Nat) (x : BitVec n)
  | ptr (n : Nat) (l o : BitVec n)
  | float (p : Prec) (x : FBits p)
  | seq (vs : List Val)
  | ext (e : Nat)

mutual
def Val.hasSort : Val → Ty → Prop
  | .bool _, .bool => True
  | .bv n _, .bitVector m => (n : Int) = m ∧ 0 < n
  | .ptr n _ _, .pointer m => (n : Int) = m ∧ 0 < n
  | .float p x, .float q => p = q ∧ x.canon = x
  | .seq vs, .seq t => Val.hasSortList vs t
  | .ext _, .extension _ => True
  | _, _ => False

def Val.hasSortList : List Val → Ty → Prop
  | [], _ => True
  | v :: vs, t => v.hasSort t ∧ Val.hasSortList vs t
end

def Val.hasTy (v : Val) (t : Ty) : Prop := v.hasSort t.sort

structure Env where
  var : Int → Option Val
  ext : Ext → Ty → Option Val

/-- Floating-point operations, abstractly (results are canonicalised by
`eval`). -/
structure FloatSem where
  add : (p : Prec) → FBits p → FBits p → FBits p
  sub : (p : Prec) → FBits p → FBits p → FBits p
  mul : (p : Prec) → FBits p → FBits p → FBits p
  div : (p : Prec) → FBits p → FBits p → FBits p
  rem : (p : Prec) → FBits p → FBits p → FBits p
  min : (p : Prec) → FBits p → FBits p → FBits p
  max : (p : Prec) → FBits p → FBits p → FBits p
  fma : (p : Prec) → FBits p → FBits p → FBits p → FBits p
  sqrt : (p : Prec) → FBits p → FBits p
  round : RM → (p : Prec) → FBits p → FBits p
  convert : RM → (p q : Prec) → FBits p → FBits q
  toBv : RM → Bool → (n : Nat) → (p : Prec) → FBits p → BitVec n
  ofBv : RM → Bool → (p : Prec) → (n : Nat) → BitVec n → FBits p
  /-- [fp.add] and [fp.mul] are commutative (up to the payload of NaNs). -/
  add_comm : ∀ p x y, (add p x y).canon = (add p y x).canon
  mul_comm : ∀ p x y, (mul p x y).canon = (mul p y x).canon
  /-- Converting to the same format is exact. -/
  convert_id : ∀ rm p x, (convert rm p p x).canon = x.canon

/-! ## Well-typed terms -/

def Unop.WT : Unop → Ty → Ty → Prop
  | .not_, a, t => a = .bool ∧ t = .bool
  | .getPtrLoc, a, t | .getPtrOfs, a, t =>
      ∃ n : Int, 0 < n ∧ a = .pointer n ∧ t = .bitVector n
  | .bvOfBool n, a, t => 0 < n ∧ a = .bool ∧ t = .bitVector n
  | .bvOfFloat _ _ n, a, t => 0 < n ∧ (∃ p, a = .float p) ∧ t = .bitVector n
  | .floatOfBv _ _ p, a, t =>
      (∃ n : Int, 0 < n ∧ a = .bitVector n) ∧ t = .float p
  | .floatOfBvRaw p, a, t => a = .bitVector p.size ∧ t = .float p
  | .floatOfFloat _ p, a, t => (∃ q, a = .float q) ∧ t = .float p
  | .bvExtract i j, a, t =>
      ∃ n : Int, a = .bitVector n ∧ 0 ≤ i ∧ i ≤ j ∧ j < n ∧ t = .bitVector (j - i + 1)
  | .bvExtend _ k, a, t => ∃ n : Int, 0 < n ∧ a = .bitVector n ∧ 0 ≤ k ∧ t = .bitVector (n + k)
  | .bvNot, a, t | .neg _, a, t => ∃ n : Int, 0 < n ∧ a = .bitVector n ∧ t = a
  | .fAbs, a, t | .fNeg, a, t | .fSqrt, a, t | .fRound _, a, t =>
      (∃ p, a = .float p) ∧ t = a
  | .fIs _, a, t | .fIsNeg, a, t | .fIsPos, a, t => (∃ p, a = .float p) ∧ t = .bool

def Binop.WT : Binop → Ty → Ty → Ty → Prop
  | .and_, a, b, t | .or_, a, b, t => a = .bool ∧ b = .bool ∧ t = .bool
  | .eq, a, b, t => a = b ∧ t = .bool
  | .fEq, a, b, t | .fLeq, a, b, t | .fLt, a, b, t =>
      (∃ p, a = .float p) ∧ b = a ∧ t = .bool
  | .fAdd, a, b, t | .fSub, a, b, t | .fMul, a, b, t | .fDiv, a, b, t
  | .fRem, a, b, t | .fMin, a, b, t | .fMax, a, b, t =>
      (∃ p, a = .float p) ∧ b = a ∧ t = a
  | .addOvf _, a, b, t | .subOvf _, a, b, t | .mulOvf _, a, b, t
  | .lt _, a, b, t | .leq _, a, b, t =>
      (∃ n : Int, 0 < n ∧ a = .bitVector n) ∧ b = a ∧ t = .bool
  | .bvConcat, a, b, t =>
      ∃ n m : Int, 0 < n ∧ 0 < m ∧ a = .bitVector n ∧ b = .bitVector m ∧
        t = .bitVector (n + m)
  | _, a, b, t => (∃ n : Int, 0 < n ∧ a = .bitVector n) ∧ b = a ∧ t = a

def Triop.WT : Triop → Ty → Ty → Ty → Ty → Prop
  | .fma, a, b, c, t => (∃ p, a = .float p) ∧ b = a ∧ c = a ∧ t = a
  | .ite, a, b, c, t => a = .bool ∧ c = b ∧ t = b

mutual
/-- Syntactic well-typedness, up to sorts (a location is a bit-vector). -/
def Term.WT : Term → Prop
  | .mk (.var _) _ => True
  | .mk (.bool _) t => t = .bool
  | .mk (.float f) t => t = .float f.prec ∧ f.bits < 2 ^ f.prec.size
  | .mk (.bitVec z) t => ∃ n : Nat, 0 < n ∧ t.sort = .bitVector n ∧ 0 ≤ z ∧ z < 2 ^ n
  | .mk (.ptr l o) t =>
      ∃ n : Int, 0 < n ∧ t = .pointer n ∧ l.ty.sort = .bitVector n ∧
        o.ty.sort = .bitVector n ∧ l.WT ∧ o.WT
  | .mk (.seq l) t => ∃ e, t = .seq e ∧ Term.WTList e l
  | .mk (.unop op a) t => op.WT a.ty.sort t.sort ∧ a.WT
  | .mk (.binop op a b) t => op.WT a.ty.sort b.ty.sort t.sort ∧ a.WT ∧ b.WT
  | .mk (.triop op a b c) t =>
      op.WT a.ty.sort b.ty.sort c.ty.sort t.sort ∧ a.WT ∧ b.WT ∧ c.WT
  | .mk (.nop _ l) t => t = .bool ∧ ∃ e, Term.WTList e l
  | .mk (.exists_ _ body) t => t = .bool ∧ body.ty = .bool ∧ body.WT
  | .mk (.extension _) _ => True

/-- All the terms are well-typed, of the sort of [e]. -/
def Term.WTList (e : Ty) : List Term → Prop
  | [] => True
  | x :: xs => x.ty.sort = e.sort ∧ x.WT ∧ Term.WTList e xs
end

/-! ## Evaluation -/

/-- The width of a bit-vector (or location, or pointer) type. -/
def Ty.width (t : Ty) : Nat := (size_of_ty t).toNat

def FloatLit.sem (f : FloatLit) : Val := .float f.prec f.val.canon

/-- Binary bit-vector operations, on operands of the same width. -/
def bvBin (f : ∀ {n : Nat}, BitVec n → BitVec n → Option Val) :
    Option Val → Option Val → Option Val
  | some (.bv n x), some (.bv m y) => if h : m = n then f x (h ▸ y) else none
  | _, _ => none

def fBin (f : (p : Prec) → FBits p → FBits p → Option Val) :
    Option Val → Option Val → Option Val
  | some (.float p x), some (.float q y) => if h : q = p then f p x (h ▸ y) else none
  | _, _ => none

def fArith (f : (p : Prec) → FBits p → FBits p → FBits p) :=
  fBin (fun p x y => some (.float p (f p x y).canon))

/-- An arithmetic operation, poisoned when it overflows in a checked
signedness. -/
def checkedOp (c : Checked) (sovf uovf : ∀ {n : Nat}, BitVec n → BitVec n → Bool)
    (f : ∀ {n : Nat}, BitVec n → BitVec n → BitVec n) :=
  bvBin (fun x y =>
    if (c.signed && sovf x y) || (c.unsigned && uovf x y) then none
    else some (.bv _ (f x y)))

def pand : Option Val → Option Val → Option Val
  | some (.bool false), _ => some (.bool false)
  | _, some (.bool false) => some (.bool false)
  | some (.bool true), some (.bool true) => some (.bool true)
  | _, _ => none

def por : Option Val → Option Val → Option Val
  | some (.bool true), _ => some (.bool true)
  | _, some (.bool true) => some (.bool true)
  | some (.bool false), some (.bool false) => some (.bool false)
  | _, _ => none

def evUnop (FS : FloatSem) : Unop → Option Val → Option Val
  | .not_, some (.bool b) => some (.bool !b)
  | .getPtrLoc, some (.ptr n l _) => some (.bv n l)
  | .getPtrOfs, some (.ptr n _ o) => some (.bv n o)
  | .bvOfBool n, some (.bool b) => some (.bv n.toNat (if b then 1 else 0))
  | .bvOfFloat rm s n, some (.float p x) => some (.bv n.toNat (FS.toBv rm s n.toNat p x))
  | .floatOfBv rm s p, some (.bv n x) => some (.float p (FS.ofBv rm s p n x).canon)
  | .floatOfBvRaw p, some (.bv n x) =>
      if h : n = p.size then some (.float p (FBits.canon (p := p) (x.cast h))) else none
  | .floatOfFloat rm p, some (.float q x) => some (.float p (FS.convert rm q p x).canon)
  | .bvExtract i j, some (.bv _ x) =>
      some (.bv (j - i + 1).toNat (x.extractLsb' i.toNat _))
  | .bvExtend s k, some (.bv n x) =>
      some (.bv (n + k.toNat) (if s then x.signExtend _ else x.setWidth _))
  | .bvNot, some (.bv n x) => some (.bv n (~~~x))
  | .neg c, some (.bv n x) => if c && x = BitVec.intMin n then none else some (.bv n (-x))
  | .fAbs, some (.float p x) => some (.float p x.abs.canon)
  | .fNeg, some (.float p x) => some (.float p x.neg.canon)
  | .fSqrt, some (.float p x) => some (.float p (FS.sqrt p x).canon)
  | .fRound rm, some (.float p x) => some (.float p (FS.round rm p x).canon)
  | .fIs fc, some (.float _ x) => some (.bool (x.isClass fc))
  | .fIsNeg, some (.float _ x) => some (.bool x.isNeg)
  | .fIsPos, some (.float _ x) => some (.bool x.isPos)
  | _, _ => none

def evBinop (FS : FloatSem) : Binop → Option Val → Option Val → Option Val
  | .and_, a, b => pand a b
  | .or_, a, b => por a b
  | .eq, some a, some b => some (.bool (decide (a = b)))
  | .eq, _, _ => none
  | .fEq, a, b => fBin (fun _ x y => some (.bool (x.eq y))) a b
  | .fLeq, a, b => fBin (fun _ x y => some (.bool (x.le y))) a b
  | .fLt, a, b => fBin (fun _ x y => some (.bool (x.lt y))) a b
  | .fAdd, a, b => fArith FS.add a b
  | .fSub, a, b => fArith FS.sub a b
  | .fMul, a, b => fArith FS.mul a b
  | .fDiv, a, b => fArith FS.div a b
  | .fRem, a, b => fArith FS.rem a b
  | .fMin, a, b => fArith FS.min a b
  | .fMax, a, b => fArith FS.max a b
  | .add c, a, b => checkedOp c BitVec.saddOverflow BitVec.uaddOverflow (· + ·) a b
  | .sub c, a, b => checkedOp c BitVec.ssubOverflow BitVec.usubOverflow (· - ·) a b
  | .mul c, a, b => checkedOp c BitVec.smulOverflow BitVec.umulOverflow (· * ·) a b
  | .div s, a, b =>
      bvBin (fun x y => some (.bv _ (if s then x.smtSDiv y else x.smtUDiv y))) a b
  | .rem s, a, b => bvBin (fun x y => some (.bv _ (if s then x.srem y else x.umod y))) a b
  | .mod_, a, b => bvBin (fun x y => some (.bv _ (x.smod y))) a b
  | .addOvf s, a, b =>
      bvBin (fun x y => some (.bool (if s then x.saddOverflow y else x.uaddOverflow y))) a b
  | .subOvf s, a, b =>
      bvBin (fun x y => some (.bool (if s then x.ssubOverflow y else x.usubOverflow y))) a b
  | .mulOvf s, a, b =>
      bvBin (fun x y => some (.bool (if s then x.smulOverflow y else x.umulOverflow y))) a b
  | .lt s, a, b => bvBin (fun x y => some (.bool (if s then x.slt y else x.ult y))) a b
  | .leq s, a, b => bvBin (fun x y => some (.bool (if s then x.sle y else x.ule y))) a b
  | .bvConcat, some (.bv n x), some (.bv m y) => some (.bv (n + m) (x ++ y))
  | .bvConcat, _, _ => none
  | .bitAnd, a, b => bvBin (fun x y => some (.bv _ (x &&& y))) a b
  | .bitOr, a, b => bvBin (fun x y => some (.bv _ (x ||| y))) a b
  | .bitXor, a, b => bvBin (fun x y => some (.bv _ (x ^^^ y))) a b
  | .shl, a, b => bvBin (fun x y => some (.bv _ (x <<< y))) a b
  | .lShr, a, b => bvBin (fun x y => some (.bv _ (x >>> y))) a b
  | .aShr, a, b => bvBin (fun x y => some (.bv _ (x.sshiftRight' y))) a b

def evFma (FS : FloatSem) : Option Val → Option Val → Option Val → Option Val
  | some (.float p x), some (.float q y), some (.float r z) =>
      if h : q = p ∧ r = p then
        some (.float p (FS.fma p x (h.1 ▸ y) (h.2 ▸ z)).canon)
      else none
  | _, _, _ => none

/-- The environments that differ from [ρ] only on the variables bound by
[bs], which they give values of the right types. -/
def Env.Extends (ρ' ρ : Env) (bs : List (Int × Ty)) : Prop :=
  ρ'.ext = ρ.ext ∧ (∀ v, (∀ b ∈ bs, b.1 ≠ v) → ρ'.var v = ρ.var v) ∧
    ∀ b ∈ bs, ∃ x, ρ'.var b.1 = some x ∧ x.hasTy b.2

mutual
/-- Evaluation, assuming well-typedness. -/
def ev (FS : FloatSem) : Env → Term → Option Val
  | ρ, .mk (.var v) t =>
      match ρ.var v with
      | some x => if x.hasTy t then some x else none
      | none => none
  | _, .mk (.bool b) _ => some (.bool b)
  | _, .mk (.float f) _ => some f.sem
  | _, .mk (.bitVec z) t => some (.bv t.width (BitVec.ofInt _ z))
  | ρ, .mk (.ptr l o) _ =>
      match ev FS ρ l, ev FS ρ o with
      | some (.bv n x), some (.bv m y) => if h : m = n then some (.ptr n x (h ▸ y)) else none
      | _, _ => none
  | ρ, .mk (.seq l) _ => (evList FS ρ l).map .seq
  | ρ, .mk (.unop op a) _ => evUnop FS op (ev FS ρ a)
  | ρ, .mk (.binop op a b) _ => evBinop FS op (ev FS ρ a) (ev FS ρ b)
  | ρ, .mk (.triop .ite g a b) _ =>
      match ev FS ρ g with
      | some (.bool true) => ev FS ρ a
      | some (.bool false) => ev FS ρ b
      | _ => none
  | ρ, .mk (.triop .fma a b c) _ => evFma FS (ev FS ρ a) (ev FS ρ b) (ev FS ρ c)
  | ρ, .mk (.nop .distinct l) _ =>
      (evList FS ρ l).map (fun vs => .bool (decide vs.Nodup))
  | ρ, .mk (.exists_ bs body) _ =>
      if ∀ ρ', ρ'.Extends ρ bs → ∃ b, ev FS ρ' body = some (.bool b) then
        some (.bool (decide (∃ ρ', ρ'.Extends ρ bs ∧ ev FS ρ' body = some (.bool true))))
      else none
  | ρ, .mk (.extension e) t =>
      match ρ.ext e t with
      | some x => if x.hasTy t then some x else none
      | none => none

def evList (FS : FloatSem) : Env → List Term → Option (List Val)
  | _, [] => some []
  | ρ, t :: ts =>
      match ev FS ρ t, evList FS ρ ts with
      | some v, some vs => some (v :: vs)
      | _, _ => none
end

/-- The value of a term; `none` for poison. -/
def eval (FS : FloatSem) (ρ : Env) (t : Term) : Option Val :=
  if t.WT then ev FS ρ t else none

/-! ## Refinement -/

/-- [r] refines [spec]: it has the same sort, and the same value whenever
[spec] is not poison. -/
def Refines (FS : FloatSem) (spec r : Term) : Prop :=
  (spec.WT → r.WT ∧ r.ty.sort = spec.ty.sort) ∧
    ∀ ρ v, eval FS ρ spec = some v → eval FS ρ r = some v

theorem Refines.refl {FS : FloatSem} {t : Term} : Refines FS t t :=
  ⟨fun h => ⟨h, rfl⟩, fun _ _ h => h⟩

theorem Refines.firstSome_nil {FS : FloatSem} {spec : Term} :
    Refines FS spec ((firstSome ([] : List (Option Term))).getD spec) :=
  Refines.refl

theorem Refines.firstSome_cons {FS : FloatSem} {spec : Term} {o : Option Term}
    {l : List (Option Term)} (h : ∀ r, o = some r → Refines FS spec r)
    (t : Refines FS spec ((firstSome l).getD spec)) :
    Refines FS spec ((firstSome (o :: l)).getD spec) := by
  cases o with
  | none => simpa [firstSome] using t
  | some r => simpa [firstSome] using h r rfl

/-! ## Assumptions on the oracles -/

def FloatLit.WF (f : FloatLit) : Prop := f.bits < 2 ^ f.prec.size

/-- The literal term of a float. -/
def FloatLit.term (f : FloatLit) : Term := .mk (.float f) (.float f.prec)

/-- What the proofs assume of the oracles: that sorting by tags permutes a list,
and that Floatml computes, on literals, the same values as the SMT-LIB
operations (of the same precision). -/
structure Oracle.Compat (orc : Oracle) (FS : FloatSem) : Prop where
  sort_by_tag : ∀ l, (orc.sort_by_tag l).Perm l
  bin : ∀ (op : Binop) (lit : FloatLit → FloatLit → FloatLit),
    (op, lit) ∈ [(.fAdd, orc.f_add), (.fSub, orc.f_sub), (.fMul, orc.f_mul),
      (.fDiv, orc.f_div), (.fRem, orc.f_rem), (.fMin, orc.f_min), (.fMax, orc.f_max)] →
    ∀ f1 f2, f1.WF → f2.WF → f1.prec = f2.prec →
      (lit f1 f2).prec = f1.prec ∧ (lit f1 f2).WF ∧
        evBinop FS op (some f1.sem) (some f2.sem) = some (lit f1 f2).sem
  fma : ∀ f1 f2 f3, f1.WF → f2.WF → f3.WF → f1.prec = f2.prec → f1.prec = f3.prec →
    (orc.f_fma f1 f2 f3).prec = f1.prec ∧ (orc.f_fma f1 f2 f3).WF ∧
      evFma FS (some f1.sem) (some f2.sem) (some f3.sem) = some (orc.f_fma f1 f2 f3).sem
  sqrt : ∀ f, f.WF → (orc.f_sqrt f).prec = f.prec ∧ (orc.f_sqrt f).WF ∧
    evUnop FS .fSqrt (some f.sem) = some (orc.f_sqrt f).sem
  round : ∀ rm f, f.WF → (orc.f_round rm f).prec = f.prec ∧ (orc.f_round rm f).WF ∧
    evUnop FS (.fRound rm) (some f.sem) = some (orc.f_round rm f).sem
  convert : ∀ rm p f, f.WF → (orc.f_convert rm p f).prec = p ∧ (orc.f_convert rm p f).WF ∧
    evUnop FS (.floatOfFloat rm p) (some f.sem) = some (orc.f_convert rm p f).sem
  to_int : ∀ rm s n f z, f.WF → 0 < n → orc.f_to_int rm s n f = some z →
    evUnop FS (.bvOfFloat rm s n) (some f.sem) = some (.bv n.toNat (BitVec.ofInt _ z))
  of_int : ∀ rm s p n z f, 0 < n → 0 ≤ z → z < 2 ^ n.toNat → orc.f_of_int rm s p n z = some f →
    f.prec = p ∧ f.WF ∧
      evUnop FS (.floatOfBv rm s p) (some (.bv n.toNat (BitVec.ofInt _ z))) = some f.sem
  /-- C's [fmod] agrees with its emulation from the IEEE remainder. -/
  fmod : ∀ f1 f2 ρ, f1.WF → f2.WF → f1.prec = f2.prec →
    (orc.f_fmod f1 f2).prec = f1.prec ∧ (orc.f_fmod f1 f2).WF ∧
      eval FS ρ (raw_fmod_of_rem (.mk (.binop .fRem f1.term f2.term) (.float f1.prec))
        f1.term f2.term) = some (orc.f_fmod f1 f2).sem

end Bvr

end
