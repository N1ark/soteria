import BitvecMod.Lang

/-!
# The primitives of the bitvec module over sorts and terms

The width of a sort (`size_of_ty`) is `n` for the sorts `TBitVector n` and
`TLoc n`, and otherwise the language's (`Values.width`): e.g. that of the sorts
of pointers, which the bitvec module cannot see. The operations on literals take the width of the sort of
their first operand (see `Ints.lean`). The subsorts `TNonzero` and `TZero` are
the terms whose bit-vector values are not zero, or are zero.

The width of a sort of bit-vectors is the width of its values (`width_sort`):
this is not assumed of the language, but follows from the values of its
literals (`Typed`).
-/

noncomputable section

namespace BitvecMod

open Classical Kanon

variable {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [Lang S]

/-- The width of a sort: `n` for the sorts `TBitVector n` and `TLoc n` of the module, which
does not depend on the values of the language (in particular in the typing of the terms),
and the language's for the others. -/
def size_of_ty (s : S.Ty) : Int :=
  match sortProj s with
  | some (.TBitVector n) | some (.TLoc n) => n
  | _ => (Values.width (D := S.toDom) s : Int)

@[simp, kanon_lits] theorem size_of_ty_TBitVector (n : Int) :
    size_of_ty (S := S) (sort (.TBitVector n)) = n := by
  simp [size_of_ty]

@[simp, kanon_lits] theorem size_of_ty_TLoc (n : Int) : size_of_ty (S := S) (sort (.TLoc n)) = n := by
  simp [size_of_ty]

def lit_add (s _ : S.Ty) (a b : Int) : Int := Prim.lit_add (size_of_ty s) a b
def lit_sub (s _ : S.Ty) (a b : Int) : Int := Prim.lit_sub (size_of_ty s) a b
def lit_mul (s _ : S.Ty) (a b : Int) : Int := Prim.lit_mul (size_of_ty s) a b
def lit_neg (s : S.Ty) (a : Int) : Int := Prim.lit_neg (size_of_ty s) a
def lit_udiv (s _ : S.Ty) (a b : Int) : Int := Prim.lit_udiv (size_of_ty s) a b
def lit_sdiv (s _ : S.Ty) (a b : Int) : Int := Prim.lit_sdiv (size_of_ty s) a b
def lit_and (s _ : S.Ty) (a b : Int) : Int := Prim.lit_and (size_of_ty s) a b
def lit_or (s _ : S.Ty) (a b : Int) : Int := Prim.lit_or (size_of_ty s) a b
def lit_xor (s _ : S.Ty) (a b : Int) : Int := Prim.lit_xor (size_of_ty s) a b
def lit_not (s : S.Ty) (a : Int) : Int := Prim.lit_not (size_of_ty s) a
def lit_shl (s _ : S.Ty) (a b : Int) : Int := Prim.lit_shl (size_of_ty s) a b
def lit_lshr (s _ : S.Ty) (a b : Int) : Int := Prim.lit_lshr (size_of_ty s) a b
def lit_ashr (s _ : S.Ty) (a b : Int) : Int := Prim.lit_ashr (size_of_ty s) a b
def lit_urem (s _ : S.Ty) (a b : Int) : Int := Prim.lit_urem (size_of_ty s) a b
def lit_srem (s _ : S.Ty) (a b : Int) : Int := Prim.lit_srem (size_of_ty s) a b
def lit_smod (s _ : S.Ty) (a b : Int) : Int := Prim.lit_smod (size_of_ty s) a b
def lit_extract (from_ to_ : Int) (_ : S.Ty) (a : Int) : Int := Prim.lit_extract from_ to_ a
def lit_zext (_ : Int) (_ : S.Ty) (a : Int) : Int := Prim.lit_zext a
def lit_sext (k : Int) (s : S.Ty) (a : Int) : Int := Prim.lit_sext k (size_of_ty s) a
def lit_concat (_ s : S.Ty) (a b : Int) : Int := Prim.lit_concat (size_of_ty s) a b

/-- The literal of width `n` of the integer `z`, masked. -/
def mk_masked (n z : Int) : S.Term := mk (.BitVec (z % 2 ^ n.toNat)) (sort (.TBitVector n))

/-- `BitVec.mk` asserts that its argument is in range; where it returns, it is
`mk_masked`. -/
def mk_bv (n z : Int) : S.Term := mk_masked n z

def bv_zero (n : Int) : S.Term := mk (.BitVec 0) (sort (.TBitVector n))
def bv_one (n : Int) : S.Term := mk (.BitVec 1) (sort (.TBitVector n))

attribute [kanon_lits] mk_masked mk_bv bv_zero bv_one

/-- The subsort `TNonzero`: the bit-vector values of the term are not zero. -/
def Nonzero (e : S.Term) : Prop :=
  ∀ ρ n (x : BitVec n), S.ev ρ e = some (Values.vbv.inj ⟨n, x⟩) → x ≠ 0

/-- The subsort `TZero`: the bit-vector values of the term are zero. -/
def Zero (e : S.Term) : Prop :=
  ∀ ρ n (x : BitVec n), S.ev ρ e = some (Values.vbv.inj ⟨n, x⟩) → x = 0

/-- The literal `0` of the sort `s`, of positive width, is well-typed. -/
theorem WT_zero {s : Srt} {n : Int} (hs : s = .TBitVector n ∨ s = .TLoc n) (h : 0 < n) :
    S.WT (mk (if s = .TLoc n then .LocLit 0 else .BitVec 0) (sort s)) := by
  have hp : (0 : Int) < 2 ^ n.toNat := Int.pow_pos (by decide)
  rw [WT_mk]
  rcases hs with rfl | rfl <;>
    simp only [reduceCtorEq, if_false, if_true, Node.wt, bv_wf, Node.All, sort_inj_iff,
      Srt.TBitVector.injEq, Srt.TLoc.injEq, or_false, false_or] <;>
    exact ⟨⟨⟨n, h, rfl⟩, fun m hm => by subst hm; exact ⟨Int.le_refl _, hp⟩⟩, trivial⟩

/-- The width of a sort of bit-vectors (or locations) of positive width is its
width: its literals are well-typed, and evaluate to bit-vectors of their sort. -/
theorem width_sort [Typed S] (ρ : S.Env) {s : Srt} {n : Int}
    (hs : s = .TBitVector n ∨ s = .TLoc n) (h : 0 < n) :
    Values.width (D := S.toDom) (sort s) = n.toNat := by
  have hv := Typed.ev_sort ρ _ _ s (WT_zero hs h) (ty_mk _ _)
    (by rw [ev_mk]; split <;> rfl)
  rcases hs with rfl | rfl <;>
    obtain ⟨-, x, hx⟩ := hv <;>
    exact congrArg Sigma.fst ((Embed.inj_eq_iff _).1 hx)

/-- `width_sort`, for a sort `τ` that is one of bit-vectors or locations. -/
theorem width_eq [Typed S] (ρ : S.Env) {τ : S.Ty} {s : Srt} {n : Int} (hτ : τ = sort s)
    (hs : s = .TBitVector n ∨ s = .TLoc n) (h : 0 < n) :
    Values.width (D := S.toDom) τ = n.toNat :=
  hτ ▸ width_sort ρ hs h

end BitvecMod
