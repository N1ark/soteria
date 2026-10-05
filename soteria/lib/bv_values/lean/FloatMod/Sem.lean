import BitvecMod.Sem
import FloatMod.Syntax
import FloatMod.Prim
import FloatMod.Val

/-!
# What the float module needs of the semantics of a language

The rules of the float module (`../rules/float.kn`) are proved once, over its
interface `L` and what they need of the semantics `S`, the class
`FloatMod.Sem L`:

- the floats among the values (`vfloat`, by their precision and bit pattern),
  which are different from each other and from the booleans and bit-vectors,
  and which the well-typed float terms evaluate to (`ev_float`);
- the floating-point arithmetic of the language (`fadd`, …, which the module
  leaves abstract), and the evaluation of the nodes with it (`ev_FAdd`, …), by
  the operations of `Val.lean`;
- the primitives of the module (`Prim`), and the invariant of the literals
  (`float_wf`).

`Oracle.Compat` is what the rules assume of the oracles (Floatml's
operations): that they compute, on literals, what the arithmetic of the
language does.
-/

namespace FloatMod

open Classical Kanon CoreMod

/-- What the float module needs of the semantics `S` of a language, for its
interface `L`. -/
class Sem {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
    {LBool : KanonBool.Syntax B} {LCore : CoreMod.Syntax B}
    {LBitvec : BitvecMod.Syntax B LBool LCore} (L : Syntax B LBool LCore LBitvec)
    [KanonBool.Sem LBool] [CoreMod.Sem LCore] [BitvecMod.Sem LBitvec] where
  /-- The float values. -/
  vfloat : (p : Fp) → FBits p → S.Val
  vfloat_inj : ∀ p q (x : FBits p) (y : FBits q), vfloat p x = vfloat q y →
    (⟨p, x⟩ : Σ p, FBits p) = ⟨q, y⟩
  vfloat_ne_vbool : ∀ p (x : FBits p) b, vfloat p x ≠ KanonBool.Sem.vbool LBool b
  vfloat_ne_vbv : ∀ p (x : FBits p) n (y : BitVec n), vfloat p x ≠ BitvecMod.Sem.vbv LBitvec n y
  /-- Well-typed floats evaluate to floats of their precision. -/
  ev_float : ∀ ρ t v p, S.WT t → S.ty t = L.TFloat p → S.ev ρ t = some v →
    ∃ x, v = vfloat p x
  /-- The floating-point arithmetic of the language, on bit patterns. -/
  fadd : (p : Fp) → FBits p → FBits p → FBits p
  fsub : (p : Fp) → FBits p → FBits p → FBits p
  fmul : (p : Fp) → FBits p → FBits p → FBits p
  fdiv : (p : Fp) → FBits p → FBits p → FBits p
  frem : (p : Fp) → FBits p → FBits p → FBits p
  fmin : (p : Fp) → FBits p → FBits p → FBits p
  fmax : (p : Fp) → FBits p → FBits p → FBits p
  ffma : (p : Fp) → FBits p → FBits p → FBits p → FBits p
  fsqrt : (p : Fp) → FBits p → FBits p
  fround : Rm → (p : Fp) → FBits p → FBits p
  fconvert : Rm → (p q : Fp) → FBits p → FBits q
  ftoBv : Rm → Bool → (n : Nat) → (p : Fp) → FBits p → BitVec n
  fofBv : Rm → Bool → (p : Fp) → (n : Nat) → BitVec n → FBits p
  -- the evaluation of the nodes
  ev_Float : ∀ ρ f t, S.ev ρ (B.node (L.FloatK f) t) = some (vfloat f.prec f.val)
  ev_BvOfFloat : ∀ ρ rm s n a t, S.ev ρ (B.node (L.BvOfFloatK rm s n a) t) =
    fUn vfloat (fun p x => some (BitvecMod.Sem.vbv LBitvec n.toNat (ftoBv rm s n.toNat p x)))
      (S.ev ρ a)
  ev_FloatOfBv : ∀ ρ rm s p a t, S.ev ρ (B.node (L.FloatOfBvK rm s p a) t) =
    BitvecMod.bvUn (BitvecMod.Sem.vbv LBitvec) (fun n x => some (vfloat p (fofBv rm s p n x)))
      (S.ev ρ a)
  ev_FloatOfBvRaw : ∀ ρ p a t, S.ev ρ (B.node (L.FloatOfBvRawK p a) t) =
    BitvecMod.bvUn (BitvecMod.Sem.vbv LBitvec)
      (fun n x => if h : n = p.size then some (vfloat p (x.cast h)) else none) (S.ev ρ a)
  ev_FloatOfFloat : ∀ ρ rm p a t, S.ev ρ (B.node (L.FloatOfFloatK rm p a) t) =
    fUn vfloat (fun q x => some (vfloat p (fconvert rm q p x))) (S.ev ρ a)
  ev_FAbs : ∀ ρ a t, S.ev ρ (B.node (L.FAbsK a) t) =
    fUn vfloat (fun p x => some (vfloat p x.abs)) (S.ev ρ a)
  ev_FNeg : ∀ ρ a t, S.ev ρ (B.node (L.FNegK a) t) =
    fUn vfloat (fun p x => some (vfloat p x.neg)) (S.ev ρ a)
  ev_FSqrt : ∀ ρ a t, S.ev ρ (B.node (L.FSqrtK a) t) =
    fUn vfloat (fun p x => some (vfloat p (fsqrt p x))) (S.ev ρ a)
  ev_FRound : ∀ ρ rm a t, S.ev ρ (B.node (L.FRoundK rm a) t) =
    fUn vfloat (fun p x => some (vfloat p (fround rm p x))) (S.ev ρ a)
  ev_FIs : ∀ ρ fc a t, S.ev ρ (B.node (L.FIsK fc a) t) =
    fUn vfloat (fun _ x => some (KanonBool.Sem.vbool LBool (x.isClass fc))) (S.ev ρ a)
  ev_FIsNeg : ∀ ρ a t, S.ev ρ (B.node (L.FIsNegK a) t) =
    fUn vfloat (fun _ x => some (KanonBool.Sem.vbool LBool x.isNeg)) (S.ev ρ a)
  ev_FIsPos : ∀ ρ a t, S.ev ρ (B.node (L.FIsPosK a) t) =
    fUn vfloat (fun _ x => some (KanonBool.Sem.vbool LBool x.isPos)) (S.ev ρ a)
  ev_FEq : ∀ ρ a b t, S.ev ρ (B.node (L.FEqK a b) t) =
    fBin vfloat (fun _ x y => some (KanonBool.Sem.vbool LBool (x.eq y))) (S.ev ρ a) (S.ev ρ b)
  ev_FLeq : ∀ ρ a b t, S.ev ρ (B.node (L.FLeqK a b) t) =
    fBin vfloat (fun _ x y => some (KanonBool.Sem.vbool LBool (x.le y))) (S.ev ρ a) (S.ev ρ b)
  ev_FLt : ∀ ρ a b t, S.ev ρ (B.node (L.FLtK a b) t) =
    fBin vfloat (fun _ x y => some (KanonBool.Sem.vbool LBool (x.lt y))) (S.ev ρ a) (S.ev ρ b)
  ev_FAdd : ∀ ρ a b t, S.ev ρ (B.node (L.FAddK a b) t) =
    fBin vfloat (fun p x y => some (vfloat p (fadd p x y))) (S.ev ρ a) (S.ev ρ b)
  ev_FSub : ∀ ρ a b t, S.ev ρ (B.node (L.FSubK a b) t) =
    fBin vfloat (fun p x y => some (vfloat p (fsub p x y))) (S.ev ρ a) (S.ev ρ b)
  ev_FMul : ∀ ρ a b t, S.ev ρ (B.node (L.FMulK a b) t) =
    fBin vfloat (fun p x y => some (vfloat p (fmul p x y))) (S.ev ρ a) (S.ev ρ b)
  ev_FDiv : ∀ ρ a b t, S.ev ρ (B.node (L.FDivK a b) t) =
    fBin vfloat (fun p x y => some (vfloat p (fdiv p x y))) (S.ev ρ a) (S.ev ρ b)
  ev_FRem : ∀ ρ a b t, S.ev ρ (B.node (L.FRemK a b) t) =
    fBin vfloat (fun p x y => some (vfloat p (frem p x y))) (S.ev ρ a) (S.ev ρ b)
  ev_FMin : ∀ ρ a b t, S.ev ρ (B.node (L.FMinK a b) t) =
    fBin vfloat (fun p x y => some (vfloat p (fmin p x y))) (S.ev ρ a) (S.ev ρ b)
  ev_FMax : ∀ ρ a b t, S.ev ρ (B.node (L.FMaxK a b) t) =
    fBin vfloat (fun p x y => some (vfloat p (fmax p x y))) (S.ev ρ a) (S.ev ρ b)
  ev_Fma : ∀ ρ a b c t, S.ev ρ (B.node (L.FmaK a b c) t) =
    fTern vfloat (fun p x y z => some (vfloat p (ffma p x y z))) (S.ev ρ a) (S.ev ρ b)
      (S.ev ρ c)
  -- the invariant of the literals, and the primitives (`Prim`)
  float_wf_Float : ∀ f t, L.float_wf (B.node (L.FloatK f) t) ↔ f.WF
  fp_of_ty_TFloat : ∀ p, L.float_fp_of_ty (L.TFloat p) = p
  fp_size_eq : ∀ p, L.float_fp_size p = Prim.fp_size p
  f_prec_eq : ∀ f, L.float_f_prec f = Prim.f_prec f
  fp_of_size_eq : ∀ n, L.float_fp_of_size n = Prim.fp_of_size n
  f_equal_eq : ∀ a b, L.float_f_equal a b = Prim.f_equal a b
  f_bits_equal_eq : ∀ a b, L.float_f_bits_equal a b = Prim.f_bits_equal a b
  f_to_bits_eq : ∀ f, L.float_f_to_bits f = Prim.f_to_bits f
  f_of_bits_eq : ∀ p z, L.float_f_of_bits p z = Prim.f_of_bits p z
  f_nan_eq : ∀ p, L.float_f_nan p = Prim.f_nan p
  f_is_class_eq : ∀ fc f, L.float_f_is_class fc f = Prim.f_is_class fc f
  f_is_nan_eq : ∀ f, L.float_f_is_nan f = Prim.f_is_nan f
  f_is_zero_eq : ∀ f, L.float_f_is_zero f = Prim.f_is_zero f
  f_is_negative_eq : ∀ f, L.float_f_is_negative f = Prim.f_is_negative f
  f_is_positive_eq : ∀ f, L.float_f_is_positive f = Prim.f_is_positive f
  f_eq_eq : ∀ a b, L.float_f_eq a b = Prim.f_eq a b
  f_lt_eq : ∀ a b, L.float_f_lt a b = Prim.f_lt a b
  f_le_eq : ∀ a b, L.float_f_le a b = Prim.f_le a b
  f_abs_eq : ∀ f, L.float_f_abs f = Prim.f_abs f
  f_neg_eq : ∀ f, L.float_f_neg f = Prim.f_neg f

/-- The literal term of a float. -/
def Syntax.lit {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
    {LBool : KanonBool.Syntax B} {LCore : CoreMod.Syntax B}
    {LBitvec : BitvecMod.Syntax B LBool LCore} (L : Syntax B LBool LCore LBitvec)
    (f : CoreMod.Float) : S.Term :=
  B.node (L.FloatK f) (L.TFloat f.prec)

/-- What the rules assume of the oracles, for the interface `L`: on literals of
the same precision, which fit it, they compute what the arithmetic of the
language does (a float of that precision, which fits it); `f_to_int` and
`f_of_int` the conversions, where they return; and `f_fmod` the emulation of
C's `fmod` (`raw_fmod_of_rem`), in any environment. -/
structure Oracle.Compat {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty]
    {B : Kanon.Base S} {LBool : KanonBool.Syntax B} {LCore : CoreMod.Syntax B}
    {LBitvec : BitvecMod.Syntax B LBool LCore} (L : Syntax B LBool LCore LBitvec)
    [KanonBool.Sem LBool] [CoreMod.Sem LCore] [BitvecMod.Sem LBitvec] [Sem L]
    (f_add f_sub f_mul f_div f_rem f_fmod f_min f_max : CoreMod.Float → CoreMod.Float → CoreMod.Float)
    (f_fma : CoreMod.Float → CoreMod.Float → CoreMod.Float → CoreMod.Float)
    (f_sqrt : CoreMod.Float → CoreMod.Float) (f_round : Rm → CoreMod.Float → CoreMod.Float)
    (f_convert : Rm → Fp → CoreMod.Float → CoreMod.Float)
    (f_to_int : Rm → Bool → Int → CoreMod.Float → Option Int)
    (f_of_int : Rm → Bool → Fp → Int → Int → Option CoreMod.Float) : Prop where
  bin : ∀ (op : (p : Fp) → FBits p → FBits p → FBits p)
    (lit : CoreMod.Float → CoreMod.Float → CoreMod.Float),
    (op, lit) ∈ [(Sem.fadd L, f_add), (Sem.fsub L, f_sub), (Sem.fmul L, f_mul),
      (Sem.fdiv L, f_div), (Sem.frem L, f_rem), (Sem.fmin L, f_min), (Sem.fmax L, f_max)] →
    ∀ (f1 f2 : CoreMod.Float), f1.WF → f2.WF → f1.prec = f2.prec →
      (lit f1 f2).prec = f1.prec ∧ (lit f1 f2).WF ∧
        fBin (Sem.vfloat L) (fun p x y => some (Sem.vfloat L p (op p x y)))
          (some (Sem.vfloat L f1.prec f1.val)) (some (Sem.vfloat L f2.prec f2.val)) =
          some (Sem.vfloat L (lit f1 f2).prec (lit f1 f2).val)
  fma : ∀ (f1 f2 f3 : CoreMod.Float), f1.WF → f2.WF → f3.WF → f1.prec = f2.prec →
    f1.prec = f3.prec →
    (f_fma f1 f2 f3).prec = f1.prec ∧ (f_fma f1 f2 f3).WF ∧
      fTern (Sem.vfloat L) (fun p x y z => some (Sem.vfloat L p (Sem.ffma L p x y z)))
        (some (Sem.vfloat L f1.prec f1.val)) (some (Sem.vfloat L f2.prec f2.val))
        (some (Sem.vfloat L f3.prec f3.val)) =
        some (Sem.vfloat L (f_fma f1 f2 f3).prec (f_fma f1 f2 f3).val)
  sqrt : ∀ f, f.WF → (f_sqrt f).prec = f.prec ∧ (f_sqrt f).WF ∧
    Sem.vfloat L _ (Sem.fsqrt L f.prec f.val) = Sem.vfloat L (f_sqrt f).prec (f_sqrt f).val
  round : ∀ rm f, f.WF → (f_round rm f).prec = f.prec ∧ (f_round rm f).WF ∧
    Sem.vfloat L _ (Sem.fround L rm f.prec f.val) =
      Sem.vfloat L (f_round rm f).prec (f_round rm f).val
  convert : ∀ rm p f, f.WF → (f_convert rm p f).prec = p ∧ (f_convert rm p f).WF ∧
    Sem.vfloat L _ (Sem.fconvert L rm f.prec p f.val) =
      Sem.vfloat L (f_convert rm p f).prec (f_convert rm p f).val
  to_int : ∀ rm s n f z, f.WF → 0 < n → f_to_int rm s n f = some z →
    Sem.ftoBv L rm s n.toNat f.prec f.val = BitVec.ofInt _ z
  of_int : ∀ rm s p n z f, 0 < n → 0 ≤ z → z < 2 ^ n.toNat → f_of_int rm s p n z = some f →
    f.prec = p ∧ f.WF ∧
      Sem.vfloat L p (Sem.fofBv L rm s p n.toNat (BitVec.ofInt _ z)) = Sem.vfloat L f.prec f.val
  /-- C's `fmod` agrees with its emulation from the IEEE remainder. -/
  fmod : ∀ f1 f2, f1.WF → f2.WF → f1.prec = f2.prec →
    (f_fmod f1 f2).prec = f1.prec ∧ (f_fmod f1 f2).WF ∧ ∀ ρ,
      S.eval ρ (L.float_raw_fmod_of_rem (B.node (L.FRemK (L.lit f1) (L.lit f2)) (L.TFloat f1.prec))
        (L.lit f1) (L.lit f2)) = some (Sem.vfloat L (f_fmod f1 f2).prec (f_fmod f1 f2).val)

end FloatMod
