import BitvecMod.Node
import BitvecMod.Ints
import CoreMod.Sem
import KanonBool.Sem

/-!
# The meaning of the nodes of the bitvec module

A language has bit-vectors among its values (`Values.vbv`), which are those of
the sorts `TBitVector n` and `TLoc n`, and gives the width of a sort
(`Values.width`), which the literals and the nodes whose result is of the width
of their operands take; the others take the widths of the values of their
operands. Checked operations (`Add {signed}`, `Neg true`, ...) whose
no-overflow flag does not hold are poison, like LLVM's `nsw`. The operations
follow the SMT-LIB encoding of `encoding.ml`.

The invariant of the literals (`bv_wf`, part of their typing) is that their
integer is in the range of their width.
-/

noncomputable section

namespace BitvecMod

open Classical Kanon
open Kanon.Sem (OLe FLe)

/-- What the bitvec module needs of the values of a language: its bit-vectors,
and the width of a sort of bit-vectors. -/
class Values (D : Kanon.Dom) where
  vbv : Embed ((n : Nat) × BitVec n) D.Val
  width : D.Ty → Nat

/-! ## The primitives on integers -/

abbrev z_land := Prim.z_land
abbrev z_lsl := Prim.z_lsl
abbrev popcount := Prim.popcount
abbrev log2 := Prim.log2
abbrev tdiv := Prim.tdiv
abbrev trem := Prim.trem
abbrev divisible := Prim.divisible
abbrev signed_extract := Prim.signed_extract

/-- The invariant of the literals: their integer is in the range of their
width. -/
@[kanon_wt] def bv_wf {T Ty : Type} (sBool : KanonBool.Srt → Ty) (sCore : CoreMod.Srt Ty → Ty)
    (sBitvec : Srt → Ty) (ty : T → Ty) : Node T → Ty → Prop
  | .BitVec z, t | .LocLit z, t =>
    ∀ n, (t = sBitvec (.TBitVector n) ∨ t = sBitvec (.TLoc n)) → 0 ≤ z ∧ z < 2 ^ n.toNat
  | _, _ => True

/-! ## The operations on values -/

section
variable {D : Kanon.Dom} [KanonBool.Values D] [Values D]

/-- The value of a bit-vector. -/
abbrev bv (n : Nat) (x : BitVec n) : D.Val := Values.vbv.inj ⟨n, x⟩

/-- A value as a bit-vector of width `n`; `none` for poison or another value. -/
def asBV (n : Nat) (a : Option D.Val) : Option (BitVec n) :=
  a.bind fun v => (Values.vbv.proj v).bind fun p => if h : p.1 = n then some (h ▸ p.2) else none

/-- A value as a boolean. -/
def asB (a : Option D.Val) : Option Bool := a.bind KanonBool.Values.vbool.proj

/-- `k` at the width of the value `a`, if it is a bit-vector. -/
def withW (a : Option D.Val) (k : Nat → Option D.Val) : Option D.Val :=
  a.bind fun v => (Values.vbv.proj v).bind fun p => k p.1

/-- A bit-vector result. -/
def ofBV (n : Nat) (r : Option (BitVec n)) : Option D.Val := r.map (bv n)

/-- A boolean result. -/
def ofB (r : Option Bool) : Option D.Val := r.map KanonBool.Values.vbool.inj

@[simp] theorem asBV_none (n : Nat) : asBV (D := D) n none = none := rfl
@[simp] theorem asB_none : asB (D := D) none = none := rfl
@[simp] theorem withW_none (k : Nat → Option D.Val) : withW none k = none := rfl
@[simp] theorem withW_none_k (a : Option D.Val) : withW a (fun _ => none) = none := by
  simp [withW]
@[simp] theorem ofBV_none (n : Nat) : ofBV (D := D) n none = none := rfl
@[simp] theorem ofB_none : ofB (D := D) none = none := rfl

@[simp, kanon_val] theorem asBV_bv (n : Nat) (x : BitVec n) :
    asBV n (some (bv (D := D) n x)) = some x := by
  simp [asBV]

@[kanon_val] theorem asBV_eq_some {n : Nat} {a : Option D.Val} {x : BitVec n} :
    asBV n a = some x ↔ a = some (bv n x) := by
  constructor
  · intro h
    simp only [asBV, Option.bind_eq_some_iff] at h
    obtain ⟨v, rfl, ⟨m, y⟩, hp, h⟩ := h
    split at h
    · rename_i hm; simp only at hm; subst hm; cases h
      rw [Embed.proj_eq_some_iff] at hp; rw [hp]
    · cases h
  · rintro rfl; exact asBV_bv n x

@[simp, kanon_val] theorem asB_vbool (b : Bool) :
    asB (some (KanonBool.Values.vbool.inj b : D.Val)) = some b := by
  simp [asB]

@[kanon_val] theorem asB_eq_some {a : Option D.Val} {b : Bool} :
    asB a = some b ↔ a = some (KanonBool.Values.vbool.inj b) := by
  simp only [asB, Option.bind_eq_some_iff, Embed.proj_eq_some_iff]
  constructor
  · rintro ⟨v, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨_, rfl, rfl⟩

@[simp, kanon_val] theorem withW_bv (n : Nat) (x : BitVec n) (k : Nat → Option D.Val) :
    withW (some (bv n x)) k = k n := by
  simp [withW]

@[kanon_val] theorem withW_eq_some {a : Option D.Val} {k : Nat → Option D.Val} {v : D.Val} :
    withW a k = some v ↔ ∃ n x, a = some (bv n x) ∧ k n = some v := by
  constructor
  · intro h
    simp only [withW, Option.bind_eq_some_iff] at h
    obtain ⟨u, rfl, ⟨n, x⟩, hp, h⟩ := h
    exact ⟨n, x, by rw [Embed.proj_eq_some_iff] at hp; rw [hp], h⟩
  · rintro ⟨n, x, rfl, h⟩; rw [withW_bv]; exact h

@[simp, kanon_val] theorem ofBV_some (n : Nat) (x : BitVec n) :
    ofBV n (some x) = some (bv (D := D) n x) := rfl
@[simp, kanon_val] theorem ofB_some (b : Bool) :
    ofB (some b) = some (KanonBool.Values.vbool.inj b : D.Val) := rfl

/-! The operations on bit-vectors of option B (`ckOp` and the others), poisoned
by their operands. -/

/-- Checked arithmetic: poison when a checked flag overflows. -/
def ckOp {n : Nat} (c : CoreMod.Checked) (sovf uovf : BitVec n → BitVec n → Bool)
    (f : BitVec n → BitVec n → BitVec n) :
    Option (BitVec n) → Option (BitVec n) → Option (BitVec n)
  | some x, some y =>
    if (c.signed && sovf x y) || (c.unsigned && uovf x y) then none else some (f x y)
  | _, _ => none

/-- Plain binary operations. -/
def binOp {n : Nat} (f : BitVec n → BitVec n → BitVec n) :
    Option (BitVec n) → Option (BitVec n) → Option (BitVec n)
  | some x, some y => some (f x y)
  | _, _ => none

/-- Negation, checked against `INT_MIN`. -/
def negOp {n : Nat} (c : Bool) : Option (BitVec n) → Option (BitVec n)
  | some x => if c && x = BitVec.intMin n then none else some (-x)
  | none => none

/-- A binary predicate. -/
def binB {α : Type} (f : α → α → Bool) : Option α → Option α → Option Bool
  | some x, some y => some (f x y)
  | _, _ => none

@[simp] theorem ckOp_none_l {n c sovf uovf f} (b : Option (BitVec n)) :
    ckOp c sovf uovf f none b = none := rfl
@[simp] theorem ckOp_none_r {n c sovf uovf f} (a : Option (BitVec n)) :
    ckOp c sovf uovf f a none = none := by cases a <;> rfl
@[simp, kanon_val] theorem ckOp_some {n c sovf uovf f} (x y : BitVec n) :
    ckOp c sovf uovf f (some x) (some y) =
      if (c.signed && sovf x y) || (c.unsigned && uovf x y) then none else some (f x y) := rfl
@[simp] theorem binOp_none_l {n f} (b : Option (BitVec n)) : binOp f none b = none := rfl
@[simp] theorem binOp_none_r {n f} (a : Option (BitVec n)) : binOp f a none = none := by
  cases a <;> rfl
@[simp, kanon_val] theorem binOp_some {n f} (x y : BitVec n) :
    binOp f (some x) (some y) = some (f x y) := rfl
@[simp] theorem negOp_none {n c} : negOp (n := n) c none = none := rfl
@[simp, kanon_val] theorem negOp_some {n c} (x : BitVec n) :
    negOp c (some x) = if c && x = BitVec.intMin n then none else some (-x) := rfl
@[simp, kanon_val] theorem binB_some {α f} (x y : α) : binB f (some x) (some y) = some (f x y) :=
  rfl
@[simp] theorem binB_none_l {α f} (y : Option α) : binB f none y = none := rfl
@[simp] theorem binB_none_r {α f} (x : Option α) : binB f x none = none := by cases x <;> rfl

end

/-! ## The evaluation of the nodes -/

/-- The evaluation of a node in the environment `ρ`, at the sort `t`, given the
values of its children in every environment. -/
def Node.eval {D : Kanon.Dom} [KanonBool.Values D] [Values D] (ρ : D.Env) (t : D.Ty) :
    Node (D.Env → Option D.Val) → Option D.Val
  | .BitVec z | .LocLit z => ofBV (Values.width t) (some (BitVec.ofInt _ z))
  | .BvOfBool n a => ofBV n.toNat ((asB (a ρ)).map fun b => if b then 1 else 0)
  | .BvExtract i j a =>
    withW (a ρ) fun n => ofBV (j - i + 1).toNat ((asBV n (a ρ)).map fun x => x.extractLsb' i.toNat _)
  | .BvExtend s k a =>
    withW (a ρ) fun n =>
      ofBV (n + k.toNat) ((asBV n (a ρ)).map fun x => if s then x.signExtend _ else x.setWidth _)
  | .BvNot a => ofBV (Values.width t) ((asBV _ (a ρ)).map (~~~·))
  | .Neg c a => ofBV (Values.width t) (negOp c (asBV _ (a ρ)))
  | .Add c a b =>
    ofBV (Values.width t)
      (ckOp c BitVec.saddOverflow BitVec.uaddOverflow (· + ·) (asBV _ (a ρ)) (asBV _ (b ρ)))
  | .Sub c a b =>
    ofBV (Values.width t)
      (ckOp c BitVec.ssubOverflow BitVec.usubOverflow (· - ·) (asBV _ (a ρ)) (asBV _ (b ρ)))
  | .Mul c a b =>
    ofBV (Values.width t)
      (ckOp c BitVec.smulOverflow BitVec.umulOverflow (· * ·) (asBV _ (a ρ)) (asBV _ (b ρ)))
  | .Div s a b =>
    ofBV (Values.width t)
      (binOp (fun x y => if s then x.smtSDiv y else x.smtUDiv y) (asBV _ (a ρ)) (asBV _ (b ρ)))
  | .Rem s a b =>
    ofBV (Values.width t)
      (binOp (fun x y => if s then x.srem y else x.umod y) (asBV _ (a ρ)) (asBV _ (b ρ)))
  | .Mod a b => ofBV (Values.width t) (binOp (·.smod ·) (asBV _ (a ρ)) (asBV _ (b ρ)))
  | .AddOvf s a b =>
    withW (a ρ) fun n => ofB (binB (fun x y => if s then x.saddOverflow y else x.uaddOverflow y)
      (asBV n (a ρ)) (asBV n (b ρ)))
  | .SubOvf s a b =>
    withW (a ρ) fun n => ofB (binB (fun x y => if s then x.ssubOverflow y else x.usubOverflow y)
      (asBV n (a ρ)) (asBV n (b ρ)))
  | .MulOvf s a b =>
    withW (a ρ) fun n => ofB (binB (fun x y => if s then x.smulOverflow y else x.umulOverflow y)
      (asBV n (a ρ)) (asBV n (b ρ)))
  | .Lt s a b =>
    withW (a ρ) fun n => ofB (binB (fun x y => if s then x.slt y else x.ult y)
      (asBV n (a ρ)) (asBV n (b ρ)))
  | .Leq s a b =>
    withW (a ρ) fun n => ofB (binB (fun x y => if s then x.sle y else x.ule y)
      (asBV n (a ρ)) (asBV n (b ρ)))
  | .BvConcat a b =>
    withW (a ρ) fun n => withW (b ρ) fun m =>
      ofBV (n + m) ((asBV n (a ρ)).bind fun x => (asBV m (b ρ)).map fun y => x ++ y)
  | .BitAnd a b => ofBV (Values.width t) (binOp (· &&& ·) (asBV _ (a ρ)) (asBV _ (b ρ)))
  | .BitOr a b => ofBV (Values.width t) (binOp (· ||| ·) (asBV _ (a ρ)) (asBV _ (b ρ)))
  | .BitXor a b => ofBV (Values.width t) (binOp (· ^^^ ·) (asBV _ (a ρ)) (asBV _ (b ρ)))
  | .Shl a b => ofBV (Values.width t) (binOp (· <<< ·) (asBV _ (a ρ)) (asBV _ (b ρ)))
  | .LShr a b => ofBV (Values.width t) (binOp (· >>> ·) (asBV _ (a ρ)) (asBV _ (b ρ)))
  | .AShr a b =>
    ofBV (Values.width t) (binOp (·.sshiftRight' ·) (asBV _ (a ρ)) (asBV _ (b ρ)))

attribute [kanon_close_simp] ckOp binOp negOp binB

/-- The evaluation of the nodes is monotone in poison: it is strict in each
child. -/
theorem Node.eval_mono {D : Kanon.Dom} [KanonBool.Values D] [Values D] (ρ : D.Env) (t : D.Ty)
    {n n' : Node (D.Env → Option D.Val)} (h : n.Rel FLe n') :
    OLe (n.eval ρ t) (n'.eval ρ t) := by
  cases n <;> cases n' <;> simp only [Node.Rel] at h <;> (try contradiction)
  all_goals simp only [Node.eval]
  all_goals first
    | (subst h; exact OLe.refl _)
    | (obtain ⟨rfl, h⟩ := h; rcases (h ρ).cases with h1 | h1 <;> simp [h1])
    | (obtain ⟨rfl, rfl, h⟩ := h; rcases (h ρ).cases with h1 | h1 <;> simp [h1])
    | (obtain ⟨rfl, h1, h2⟩ := h; rcases (h1 ρ).cases with h1 | h1 <;>
        rcases (h2 ρ).cases with h2 | h2 <;> simp [h1, h2])
    | (rcases (h ρ).cases with h1 | h1 <;> simp [h1])
    | (obtain ⟨h1, h2⟩ := h; rcases (h1 ρ).cases with h1 | h1 <;>
        rcases (h2 ρ).cases with h2 | h2 <;> simp [h1, h2])

/-- The values of the sorts of the module: bit-vectors of their width, which is
positive. -/
def Srt.val {D : Kanon.Dom} [Values D] : Srt → D.Val → Prop
  | .TBitVector n, v | .TLoc n, v => 0 < n ∧ ∃ x : BitVec n.toNat, v = Values.vbv.inj ⟨_, x⟩

end BitvecMod
