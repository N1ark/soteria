import FloatMod.Node
import BitvecMod.Sem

/-!
# The meaning of the nodes of the float module

Floats are exact IEEE bit patterns (`CoreMod.FBits`): unlike in SMT-LIB, NaNs
with different payloads are different values (SMT-LIB's single NaN is an
approximation made by the solver encoding, not something the simplifications may
rely on). The arithmetic of a language is its own (`Values.add`, …): each
language gives it (as opaque operations, so that the proofs hold of any), and
`Oracle.Compat` (`Prims.lean`) states that Floatml computes it on literals.
Classification, comparisons, `abs` and `neg`, which only read or flip bits, are
defined here. The invariant of the literals (`float_wf`) is that their bits fit
their precision.
-/

noncomputable section

namespace FloatMod

open Classical Kanon CoreMod
open Kanon.Sem (OLe FLe)
open BitvecMod (bv asBV withW ofB)

/-- What the float module needs of the values of a language: its floats, and
its floating-point arithmetic, on bit patterns. -/
class Values (D : Kanon.Dom) where
  vfloat : Embed ((p : Fp) × FBits p) D.Val
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

/-! ## The primitives on floats, as Floatml's `AnyFloat` -/

def fp_size (p : Fp) : Int := p.size

def fp_of_size (n : Int) : Fp :=
  if n = 16 then .F16 else if n = 64 then .F64 else if n = 128 then .F128 else .F32

@[simp] def f_prec (f : CoreMod.Float) : Fp := f.prec
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
def f_eq : CoreMod.Float → CoreMod.Float → Bool := Float.cmp FBits.eq
def f_lt : CoreMod.Float → CoreMod.Float → Bool := Float.cmp FBits.lt
def f_le : CoreMod.Float → CoreMod.Float → Bool := Float.cmp FBits.le
def f_abs (f : CoreMod.Float) : CoreMod.Float := ⟨f.prec, (FBits.abs f.val).toNat⟩
def f_neg (f : CoreMod.Float) : CoreMod.Float := ⟨f.prec, (FBits.neg f.val).toNat⟩

/-- The invariant of the literals: their bits fit their precision. -/
@[kanon_wt] def float_wf {T Ty : Type} (sBool : KanonBool.Srt → Ty) (sCore : CoreMod.Srt Ty → Ty)
    (sBitvec : BitvecMod.Srt → Ty) (sFloat : Srt → Ty) (ty : T → Ty) : Node T → Ty → Prop
  | .Float f, _ => f.WF
  | _, _ => True

/-! ## The operations on values -/

section
variable {D : Kanon.Dom} [KanonBool.Values D] [BitvecMod.Values D] [Values D]

/-- The value of a float. -/
abbrev vf (p : Fp) (x : FBits p) : D.Val := Values.vfloat.inj ⟨p, x⟩

/-- The value of a concrete float. -/
abbrev vlit (f : CoreMod.Float) : D.Val := vf f.prec f.val

/-- A value as a float of precision `p`. -/
def asF (p : Fp) (a : Option D.Val) : Option (FBits p) :=
  a.bind fun v => (Values.vfloat.proj v).bind fun q => if h : q.1 = p then some (h ▸ q.2) else none

/-- `k` at the precision and bits of the value `a`, if it is a float. -/
def withF (a : Option D.Val) (k : (p : Fp) → FBits p → Option D.Val) : Option D.Val :=
  a.bind fun v => (Values.vfloat.proj v).bind fun q => k q.1 q.2

/-- A binary operation on floats of the same precision. -/
def fBin (f : (p : Fp) → FBits p → FBits p → Option D.Val) (a b : Option D.Val) :
    Option D.Val :=
  withF a fun p x => (asF p b).bind (f p x)

@[simp] theorem asF_none (p : Fp) : asF (D := D) p none = none := rfl
@[simp] theorem withF_none (k : (p : Fp) → FBits p → Option D.Val) : withF none k = none := rfl
@[simp] theorem withF_none_k (a : Option D.Val) : withF a (fun _ _ => none) = none := by
  simp [withF]
@[simp] theorem fBin_none_l (f : (p : Fp) → FBits p → FBits p → Option D.Val) (b : Option D.Val) :
    fBin f none b = none := rfl
@[simp] theorem fBin_none_r (f : (p : Fp) → FBits p → FBits p → Option D.Val) (a : Option D.Val) :
    fBin f a none = none := by simp [fBin]

@[simp, kanon_val] theorem asF_vf (p : Fp) (x : FBits p) :
    asF p (some (vf (D := D) p x)) = some x := by
  simp [asF]

@[kanon_val] theorem asF_eq_some {p : Fp} {a : Option D.Val} {x : FBits p} :
    asF p a = some x ↔ a = some (vf p x) := by
  constructor
  · intro h
    simp only [asF, Option.bind_eq_some_iff] at h
    obtain ⟨v, rfl, ⟨q, y⟩, hp, h⟩ := h
    split at h
    · rename_i hq; simp only at hq; subst hq; cases h
      rw [Embed.proj_eq_some_iff] at hp; rw [hp]
    · cases h
  · rintro rfl; exact asF_vf p x

@[simp, kanon_val] theorem withF_vf (p : Fp) (x : FBits p) (k : (p : Fp) → FBits p → Option D.Val) :
    withF (some (vf p x)) k = k p x := by
  simp [withF]

@[kanon_val] theorem withF_eq_some {a : Option D.Val} {k : (p : Fp) → FBits p → Option D.Val}
    {v : D.Val} : withF a k = some v ↔ ∃ p x, a = some (vf p x) ∧ k p x = some v := by
  constructor
  · intro h
    simp only [withF, Option.bind_eq_some_iff] at h
    obtain ⟨u, rfl, ⟨p, x⟩, hp, h⟩ := h
    exact ⟨p, x, by rw [Embed.proj_eq_some_iff] at hp; rw [hp], h⟩
  · rintro ⟨p, x, rfl, h⟩; rw [withF_vf]; exact h

@[simp, kanon_val] theorem fBin_vf (f : (p : Fp) → FBits p → FBits p → Option D.Val) (p : Fp)
    (x y : FBits p) : fBin f (some (vf p x)) (some (vf p y)) = f p x y := by
  simp [fBin]

/-- An arithmetic operation on floats of the same precision. -/
def fArith (f : (p : Fp) → FBits p → FBits p → FBits p) : Option D.Val → Option D.Val → Option D.Val :=
  fBin fun p x y => some (vf p (f p x y))

/-- A comparison of floats of the same precision. -/
def fCmp (f : ∀ {p : Fp}, FBits p → FBits p → Bool) : Option D.Val → Option D.Val → Option D.Val :=
  fBin fun _ x y => some (KanonBool.Values.vbool.inj (f x y))

/-- A unary operation on floats, of the same precision. -/
def fUn (f : (p : Fp) → FBits p → FBits p) (a : Option D.Val) : Option D.Val :=
  withF a fun p x => some (vf p (f p x))

/-- A predicate on floats. -/
def fPred (f : ∀ {p : Fp}, FBits p → Bool) (a : Option D.Val) : Option D.Val :=
  withF a fun _ x => some (KanonBool.Values.vbool.inj (f x))

end

/-! ## The evaluation of the nodes -/

/-- The evaluation of a node in the environment `ρ`, at the sort `t`, given the
values of its children in every environment. -/
def Node.eval {D : Kanon.Dom} [KanonBool.Values D] [BitvecMod.Values D] [Values D] (ρ : D.Env)
    (t : D.Ty) : Node (D.Env → Option D.Val) → Option D.Val
  | .Float f => some (vlit f)
  | .BvOfFloat rm s n a =>
    withF (a ρ) fun p x => some (bv n.toNat ((Values.toBv (D := D)) rm s n.toNat p x))
  | .FloatOfBv rm s p a =>
    withW (a ρ) fun n => (asBV n (a ρ)).map fun x => vf p ((Values.ofBv (D := D)) rm s p n x)
  | .FloatOfBvRaw p a => (asBV p.size (a ρ)).map (vf p)
  | .FloatOfFloat rm p a => withF (a ρ) fun q x => some (vf p ((Values.convert (D := D)) rm q p x))
  | .FAbs a => fUn (fun _ x => x.abs) (a ρ)
  | .FNeg a => fUn (fun _ x => x.neg) (a ρ)
  | .FSqrt a => fUn (Values.sqrt (D := D)) (a ρ)
  | .FRound rm a => fUn ((Values.round (D := D)) rm) (a ρ)
  | .FIs fc a => fPred (fun x => x.isClass fc) (a ρ)
  | .FIsNeg a => fPred (fun x => x.isNeg) (a ρ)
  | .FIsPos a => fPred (fun x => x.isPos) (a ρ)
  | .FEq a b => fCmp (fun x y => x.eq y) (a ρ) (b ρ)
  | .FLeq a b => fCmp (fun x y => x.le y) (a ρ) (b ρ)
  | .FLt a b => fCmp (fun x y => x.lt y) (a ρ) (b ρ)
  | .FAdd a b => fArith (Values.add (D := D)) (a ρ) (b ρ)
  | .FSub a b => fArith (Values.sub (D := D)) (a ρ) (b ρ)
  | .FMul a b => fArith (Values.mul (D := D)) (a ρ) (b ρ)
  | .FDiv a b => fArith (Values.div (D := D)) (a ρ) (b ρ)
  | .FRem a b => fArith (Values.rem (D := D)) (a ρ) (b ρ)
  | .FMin a b => fArith (Values.min (D := D)) (a ρ) (b ρ)
  | .FMax a b => fArith (Values.max (D := D)) (a ρ) (b ρ)
  | .Fma a b c =>
    withF (a ρ) fun p x => (asF p (b ρ)).bind fun y => (asF p (c ρ)).map fun z =>
      vf p ((Values.fma (D := D)) p x y z)

attribute [kanon_close_simp] fArith fCmp fUn fPred

/-- The evaluation of the nodes is monotone in poison: it is strict in each
child. -/
theorem Node.eval_mono {D : Kanon.Dom} [KanonBool.Values D] [BitvecMod.Values D] [Values D]
    (ρ : D.Env) (t : D.Ty) {n n' : Node (D.Env → Option D.Val)} (h : n.Rel FLe n') :
    OLe (n.eval ρ t) (n'.eval ρ t) := by
  cases n <;> cases n' <;> simp only [Node.Rel] at h <;> (try contradiction)
  all_goals simp only [Node.eval, fArith, fCmp, fUn, fPred]
  all_goals first
    | (subst h; exact OLe.refl _)
    | (obtain ⟨rfl, rfl, rfl, h⟩ := h; rcases (h ρ).cases with h1 | h1 <;> simp [h1])
    | (obtain ⟨rfl, rfl, h⟩ := h; rcases (h ρ).cases with h1 | h1 <;> simp [h1])
    | (obtain ⟨rfl, h⟩ := h; rcases (h ρ).cases with h1 | h1 <;> simp [h1])
    | (rcases (h ρ).cases with h1 | h1 <;> simp [h1])
    | (obtain ⟨h1, h2, h3⟩ := h; rcases (h1 ρ).cases with h1 | h1 <;>
        rcases (h2 ρ).cases with h2 | h2 <;> rcases (h3 ρ).cases with h3 | h3 <;>
        simp [h1, h2, h3])
    | (obtain ⟨h1, h2⟩ := h; rcases (h1 ρ).cases with h1 | h1 <;>
        rcases (h2 ρ).cases with h2 | h2 <;> simp [h1, h2])

/-- The values of the sorts of the module: floats of their precision. -/
def Srt.val {D : Kanon.Dom} [Values D] : Srt → D.Val → Prop
  | .TFloat p, v => ∃ x : FBits p, v = Values.vfloat.inj ⟨p, x⟩

end FloatMod
