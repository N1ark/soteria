import FloatMod.Lang

/-!
# What the rules of the float module assume of Floatml

The precision of a sort (`fp_of_ty`), and what the proofs assume of the oracles
(`Oracle.Compat`): that Floatml computes, on well-formed literals, the
operations of the language (`Values.add`, …), as option B assumed of its
`FloatSem`. C's `fmod` is emulated from the IEEE remainder (`fmodBits`, the
value of `Float.raw_fmod_of_rem`).
-/

noncomputable section

namespace FloatMod

open Classical Kanon CoreMod

variable {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [BitvecMod.Lang S] [Lang S]

/-- The precision of a sort of floats. -/
def fp_of_ty (s : S.Ty) : Fp :=
  match sortProj s with
  | some (.TFloat p) => p
  | none => .F32

/-- C's `fmod`, from the IEEE remainder: the value of `Float.raw_fmod_of_rem`. -/
def fmodBits (D : Kanon.Dom) [Values D] (p : Fp) (x y : FBits p) : FBits p :=
  let r := Values.rem (D := D) p x y
  if r.isNeg = x.isNeg then r else Values.add (D := D) p r (if x.isNeg then y.abs.neg else y.abs)

/-- `lit` computes the binary operation `op` on well-formed literals of the same
precision. -/
def Bin (op : (p : Fp) → FBits p → FBits p → FBits p) (lit : CoreMod.Float → CoreMod.Float → CoreMod.Float) :
    Prop :=
  ∀ f1 f2 : CoreMod.Float, f1.WF → f2.WF → (h : f2.prec = f1.prec) →
    (lit f1 f2).prec = f1.prec ∧ (lit f1 f2).WF ∧
      vlit (D := S.toDom) (lit f1 f2) = vf f1.prec (op f1.prec f1.val (h ▸ f2.val))

/-- `lit` computes the unary operation `op` on well-formed literals. -/
def Un (op : (p : Fp) → FBits p → FBits p) (lit : CoreMod.Float → CoreMod.Float) : Prop :=
  ∀ f : CoreMod.Float, f.WF →
    (lit f).prec = f.prec ∧ (lit f).WF ∧ vlit (D := S.toDom) (lit f) = vf f.prec (op f.prec f.val)

/-- What the rules assume of the oracles. -/
structure Oracle.Compat (f_add f_sub f_mul f_div f_rem f_fmod f_min f_max :
      CoreMod.Float → CoreMod.Float → CoreMod.Float)
    (f_fma : CoreMod.Float → CoreMod.Float → CoreMod.Float → CoreMod.Float)
    (f_sqrt : CoreMod.Float → CoreMod.Float) (f_round : Rm → CoreMod.Float → CoreMod.Float)
    (f_convert : Rm → Fp → CoreMod.Float → CoreMod.Float)
    (f_to_int : Rm → Bool → Int → CoreMod.Float → Option Int)
    (f_of_int : Rm → Bool → Fp → Int → Int → Option CoreMod.Float) : Prop where
  add : Bin (S := S) (Values.add (D := S.toDom)) f_add
  sub : Bin (S := S) (Values.sub (D := S.toDom)) f_sub
  mul : Bin (S := S) (Values.mul (D := S.toDom)) f_mul
  div : Bin (S := S) (Values.div (D := S.toDom)) f_div
  rem : Bin (S := S) (Values.rem (D := S.toDom)) f_rem
  fmod : Bin (S := S) (fmodBits S.toDom) f_fmod
  min : Bin (S := S) (Values.min (D := S.toDom)) f_min
  max : Bin (S := S) (Values.max (D := S.toDom)) f_max
  fma : ∀ f1 f2 f3 : CoreMod.Float, f1.WF → f2.WF → f3.WF → (h2 : f2.prec = f1.prec) →
    (h3 : f3.prec = f1.prec) →
    (f_fma f1 f2 f3).prec = f1.prec ∧ (f_fma f1 f2 f3).WF ∧
      vlit (D := S.toDom) (f_fma f1 f2 f3) =
        vf f1.prec (Values.fma (D := S.toDom) f1.prec f1.val (h2 ▸ f2.val) (h3 ▸ f3.val))
  sqrt : Un (S := S) (Values.sqrt (D := S.toDom)) f_sqrt
  round : ∀ rm, Un (S := S) (Values.round (D := S.toDom) rm) (f_round rm)
  convert : ∀ rm p (f : CoreMod.Float), f.WF →
    (f_convert rm p f).prec = p ∧ (f_convert rm p f).WF ∧
      vlit (D := S.toDom) (f_convert rm p f) = vf p (Values.convert (D := S.toDom) rm f.prec p f.val)
  to_int : ∀ rm s (n : Int) (f : CoreMod.Float) z, f.WF → 0 < n → f_to_int rm s n f = some z →
    Values.toBv (D := S.toDom) rm s n.toNat f.prec f.val = BitVec.ofInt _ z
  -- prim.ml: `f_of_int … = Some (F.int2float z int_size fp …)`; Floatml's `AnyFloat.int2float`
  -- is `match precision with F16 -> F16 (…) | …`: of precision `fp` (and fits it) for any `z`.
  of_int_prec : ∀ rm s p (n z : Int) f, f_of_int rm s p n z = some f → f.prec = p ∧ f.WF
  of_int : ∀ rm s p (n z : Int) f, 0 < n → 0 ≤ z → z < 2 ^ n.toNat → f_of_int rm s p n z = some f →
    vlit (D := S.toDom) f = vf p (Values.ofBv (D := S.toDom) rm s p n.toNat (BitVec.ofInt _ z))

end FloatMod
