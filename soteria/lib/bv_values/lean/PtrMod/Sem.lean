import PtrMod.Node
import BitvecMod.Sem

/-!
# The meaning of the nodes of the ptr module

A pointer is a location and an offset, bit-vectors of the same width
(`Values.vptr`).
-/

noncomputable section

namespace PtrMod

open Classical Kanon
open Kanon.Sem (OLe FLe)
open BitvecMod (bv asBV withW)

/-- What the ptr module needs of the values of a language: its pointers. -/
class Values (D : Kanon.Dom) where
  vptr : Embed ((n : Nat) × BitVec n × BitVec n) D.Val

section
variable {D : Kanon.Dom} [KanonBool.Values D] [BitvecMod.Values D] [Values D]

/-- The value of a pointer. -/
abbrev vp (n : Nat) (l o : BitVec n) : D.Val := Values.vptr.inj ⟨n, l, o⟩

/-- `k` at the location and offset of the value `a`, if it is a pointer. -/
def withP (a : Option D.Val) (k : (n : Nat) → BitVec n → BitVec n → Option D.Val) :
    Option D.Val :=
  a.bind fun v => (Values.vptr.proj v).bind fun p => k p.1 p.2.1 p.2.2

@[simp] theorem withP_none (k : (n : Nat) → BitVec n → BitVec n → Option D.Val) :
    withP none k = none := rfl

@[simp, kanon_val] theorem withP_vp (n : Nat) (l o : BitVec n)
    (k : (n : Nat) → BitVec n → BitVec n → Option D.Val) :
    withP (some (vp n l o)) k = k n l o := by
  simp [withP]

@[kanon_val] theorem withP_eq_some {a : Option D.Val}
    {k : (n : Nat) → BitVec n → BitVec n → Option D.Val} {v : D.Val} :
    withP a k = some v ↔ ∃ n l o, a = some (vp n l o) ∧ k n l o = some v := by
  constructor
  · intro h
    simp only [withP, Option.bind_eq_some_iff] at h
    obtain ⟨u, rfl, ⟨n, l, o⟩, hp, h⟩ := h
    exact ⟨n, l, o, by rw [Embed.proj_eq_some_iff] at hp; rw [hp], h⟩
  · rintro ⟨n, l, o, rfl, h⟩; rw [withP_vp]; exact h
end

/-- The evaluation of a node in the environment `ρ`, given the values of its
children in every environment. -/
def Node.eval {D : Kanon.Dom} [KanonBool.Values D] [BitvecMod.Values D] [Values D] (ρ : D.Env)
    (t : D.Ty) : Node (D.Env → Option D.Val) → Option D.Val
  | .Ptr l o => withW (l ρ) fun n => (asBV n (l ρ)).bind fun x => (asBV n (o ρ)).map (vp n x)
  | .GetPtrLoc p => withP (p ρ) fun n l _ => some (bv n l)
  | .GetPtrOfs p => withP (p ρ) fun n _ o => some (bv n o)

/-- The evaluation of the nodes is monotone in poison: it is strict in each
child. -/
theorem Node.eval_mono {D : Kanon.Dom} [KanonBool.Values D] [BitvecMod.Values D] [Values D]
    (ρ : D.Env) (t : D.Ty) {n n' : Node (D.Env → Option D.Val)} (h : n.Rel FLe n') :
    OLe (n.eval ρ t) (n'.eval ρ t) := by
  cases n <;> cases n' <;> simp only [Node.Rel] at h <;> (try contradiction)
  all_goals simp only [Node.eval]
  · obtain ⟨h1, h2⟩ := h
    rcases (h1 ρ).cases with h1 | h1 <;> rcases (h2 ρ).cases with h2 | h2 <;> simp [h1, h2]
  · rcases (h ρ).cases with h1 | h1 <;> simp [h1]
  · rcases (h ρ).cases with h1 | h1 <;> simp [h1]

/-- The values of the sorts of the module: pointers of their width, which is
positive. -/
def Srt.val {D : Kanon.Dom} [Values D] : Srt → D.Val → Prop
  | .TPointer n, v => 0 < n ∧ ∃ l o : BitVec n.toNat, v = Values.vptr.inj ⟨_, l, o⟩

end PtrMod
