/-!
# The svalue grammar

A mirror of `soteria/lib/bv_values/svalue_ast.ml`. Widths and indices are
`Int`s, like OCaml's `int`s; hash-consed terms are modelled as trees, so that
the physical equality of hash-consed terms is structural equality.
-/

namespace Bvr

inductive Prec where
  | f16 | f32 | f64 | f128
  deriving DecidableEq, Repr, Inhabited

inductive RM where
  | nearestTiesToEven | truncate | ceil | floor | nearestTiesToAway
  deriving DecidableEq, Repr, Inhabited

inductive FClass where
  | normal | subnormal | zero | infinite | nan
  deriving DecidableEq, Repr, Inhabited

structure Checked where
  signed : Bool
  unsigned : Bool
  deriving DecidableEq, Repr, Inhabited

inductive Unop where
  | not_ | getPtrLoc | getPtrOfs
  | bvOfBool (n : Int)
  | bvOfFloat (rm : RM) (signed : Bool) (n : Int)
  | floatOfBv (rm : RM) (signed : Bool) (p : Prec)
  | floatOfBvRaw (p : Prec)
  | floatOfFloat (rm : RM) (p : Prec)
  | bvExtract (from_ to_ : Int)
  | bvExtend (signed : Bool) (by_ : Int)
  | bvNot
  | neg (checked : Bool)
  | fAbs | fNeg | fSqrt
  | fIs (fc : FClass)
  | fIsNeg | fIsPos
  | fRound (rm : RM)
  deriving DecidableEq, Repr, Inhabited

inductive Binop where
  | and_ | or_ | eq
  | fEq | fLeq | fLt
  | fAdd | fSub | fMul | fDiv | fRem | fMin | fMax
  | add (c : Checked) | sub (c : Checked) | mul (c : Checked)
  | div (signed : Bool) | rem (signed : Bool) | mod_
  | addOvf (signed : Bool) | subOvf (signed : Bool) | mulOvf (signed : Bool)
  | lt (signed : Bool) | leq (signed : Bool)
  | bvConcat | bitAnd | bitOr | bitXor | shl | lShr | aShr
  deriving DecidableEq, Repr, Inhabited

inductive Triop where
  | fma | ite
  deriving DecidableEq, Repr, Inhabited

inductive Nop where
  | distinct
  deriving DecidableEq, Repr, Inhabited

/-- Values of an extension, which the rules never inspect. -/
structure Ext where
  id : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Types of an extension. -/
structure ExtTy where
  id : Nat
  deriving DecidableEq, Repr, Inhabited

inductive Ty where
  | bool
  | float (p : Prec)
  | loc (n : Int)
  | pointer (n : Int)
  | seq (t : Ty)
  | bitVector (n : Int)
  | extension (e : ExtTy)
  deriving DecidableEq, Repr, Inhabited

/-- A concrete float of Floatml, given by its precision and bit pattern. -/
structure FloatLit where
  prec : Prec
  bits : Nat
  deriving DecidableEq, Repr, Inhabited

mutual
inductive Kind where
  | var (v : Int)
  | bool (b : Bool)
  | float (f : FloatLit)
  | ptr (l o : Term)
  | bitVec (z : Int)
  | seq (l : List Term)
  | unop (op : Unop) (a : Term)
  | binop (op : Binop) (a b : Term)
  | triop (op : Triop) (a b c : Term)
  | nop (op : Nop) (l : List Term)
  | exists_ (binders : List (Int × Ty)) (body : Term)
  | extension (e : Ext)

inductive Term where
  | mk (kind : Kind) (ty : Ty)
end

def Term.kind : Term → Kind
  | .mk k _ => k

def Term.ty : Term → Ty
  | .mk _ t => t

@[simp] theorem Term.kind_mk (k : Kind) (t : Ty) : (Term.mk k t).kind = k := rfl
@[simp] theorem Term.ty_mk (k : Kind) (t : Ty) : (Term.mk k t).ty = t := rfl

end Bvr

namespace Bvr
instance : Inhabited Kind := ⟨.bool false⟩
instance : Inhabited Term := ⟨.mk (.bool false) .bool⟩
end Bvr
