import KanonBool.Sem
import CoreMod.Sem
import BitvecMod.Syntax
import BitvecMod.Prim
import BitvecMod.Val

/-!
# What the bitvec module needs of the semantics of a language

The rules of the bitvec module (`../rules/bitvec.kn`) are proved once, over its
interface `L` (generated, in `Syntax.lean`) and what they need of the semantics
`S` of the language, the class `BitvecMod.Sem L`:

- the bit-vectors among the values (`vbv`), which are different from each other
  and from the booleans, and which the well-typed bit-vector (and location)
  terms evaluate to (`ev_bv`, `ev_loc`);
- the values of the terms by their structure (`den`, `denB`): the value of a
  term as a bit-vector of width `n`, or as a boolean, computed from those of its
  operands on the nodes whose value is a function of them (`den_Add`, …), which
  is its value on well-typed terms (`den_iff`, `denB_iff`). A language defines
  them by recursion on its terms;
- the primitives of the module (`Prim`), the literals and the terms that the
  helpers build;
- the invariant of the literals (`bv_wf`), and what the subsorts
  `Nonzero` and `Zero` mean;
- the bound of the values of terms by `msb_of` (`den_msb`).
-/

namespace BitvecMod

open Classical Kanon

/-- What the bitvec module needs of the semantics `S` of a language, for its
interface `L`. -/
class Sem {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
    {LBool : KanonBool.Syntax B} {LCore : CoreMod.Syntax B} (L : Syntax B LBool LCore)
    [KanonBool.Sem LBool] [CoreMod.Sem LCore] where
  /-- The bit-vector values. -/
  vbv : (n : Nat) → BitVec n → S.Val
  vbv_inj : ∀ n (x y : BitVec n), vbv n x = vbv n y → x = y
  vbv_ne : ∀ n m (x : BitVec n) (y : BitVec m), n ≠ m → vbv n x ≠ vbv m y
  vbv_ne_vbool : ∀ n (x : BitVec n) b, vbv n x ≠ KanonBool.Sem.vbool LBool b
  /-- Well-typed bit-vectors (and locations) evaluate to bit-vectors of their
  width, which is positive. -/
  ev_bv : ∀ ρ t v m, S.WT t → S.ty t = L.TBitVector m → S.ev ρ t = some v →
    0 < m ∧ ∃ x, v = vbv m.toNat x
  ev_loc : ∀ ρ t v m, S.WT t → S.ty t = L.TLoc m → S.ev ρ t = some v →
    0 < m ∧ ∃ x, v = vbv m.toNat x
  /-- The literals. -/
  ev_BitVec : ∀ ρ z t, S.ev ρ (B.node (L.BitVecK z) t) =
    some (vbv (L.bitvec_size_of_ty t).toNat (BitVec.ofInt _ z))
  ev_LocLit : ∀ ρ z t, S.ev ρ (B.node (L.LocLitK z) t) =
    some (vbv (L.bitvec_size_of_ty t).toNat (BitVec.ofInt _ z))
  bv_wf_BitVec : ∀ z t, L.bv_wf (B.node (L.BitVecK z) t) ↔
    0 ≤ z ∧ z < 2 ^ (L.bitvec_size_of_ty t).toNat
  bv_wf_LocLit : ∀ z t, L.bv_wf (B.node (L.LocLitK z) t) ↔
    0 ≤ z ∧ z < 2 ^ (L.bitvec_size_of_ty t).toNat
  -- the values by the structure of the terms
  den : S.Env → (n : Nat) → S.Term → Option (BitVec n)
  denB : S.Env → S.Term → Option Bool
  den_iff : ∀ ρ (n : Nat) t x, S.WT t → S.ty t = L.TBitVector n →
    (den ρ n t = some x ↔ S.ev ρ t = some (vbv n x))
  denB_iff : ∀ ρ t b, S.WT t → S.ty t = LBool.TBool →
    (denB ρ t = some b ↔ S.ev ρ t = some (KanonBool.Sem.vbool LBool b))
  den_BitVec : ∀ ρ n z t, den ρ n (B.node (L.BitVecK z) t) = some (BitVec.ofInt n z)
  den_Add : ∀ ρ n c a b t, den ρ n (B.node (L.AddK c a b) t) =
    ckOp c BitVec.saddOverflow BitVec.uaddOverflow (· + ·) (den ρ n a) (den ρ n b)
  den_Sub : ∀ ρ n c a b t, den ρ n (B.node (L.SubK c a b) t) =
    ckOp c BitVec.ssubOverflow BitVec.usubOverflow (· - ·) (den ρ n a) (den ρ n b)
  den_Mul : ∀ ρ n c a b t, den ρ n (B.node (L.MulK c a b) t) =
    ckOp c BitVec.smulOverflow BitVec.umulOverflow (· * ·) (den ρ n a) (den ρ n b)
  den_Div : ∀ ρ n s a b t, den ρ n (B.node (L.DivK s a b) t) =
    binOp (fun x y => if s then x.smtSDiv y else x.smtUDiv y) (den ρ n a) (den ρ n b)
  den_Rem : ∀ ρ n s a b t, den ρ n (B.node (L.RemK s a b) t) =
    binOp (fun x y => if s then x.srem y else x.umod y) (den ρ n a) (den ρ n b)
  den_Mod : ∀ ρ n a b t, den ρ n (B.node (L.ModK a b) t) =
    binOp (·.smod ·) (den ρ n a) (den ρ n b)
  den_BitAnd : ∀ ρ n a b t, den ρ n (B.node (L.BitAndK a b) t) =
    binOp (· &&& ·) (den ρ n a) (den ρ n b)
  den_BitOr : ∀ ρ n a b t, den ρ n (B.node (L.BitOrK a b) t) =
    binOp (· ||| ·) (den ρ n a) (den ρ n b)
  den_BitXor : ∀ ρ n a b t, den ρ n (B.node (L.BitXorK a b) t) =
    binOp (· ^^^ ·) (den ρ n a) (den ρ n b)
  den_Shl : ∀ ρ n a b t, den ρ n (B.node (L.ShlK a b) t) =
    binOp (· <<< ·) (den ρ n a) (den ρ n b)
  den_LShr : ∀ ρ n a b t, den ρ n (B.node (L.LShrK a b) t) =
    binOp (· >>> ·) (den ρ n a) (den ρ n b)
  den_AShr : ∀ ρ n a b t, den ρ n (B.node (L.AShrK a b) t) =
    binOp (·.sshiftRight' ·) (den ρ n a) (den ρ n b)
  den_BvConcat : ∀ ρ n a b t, den ρ n (B.node (L.BvConcatK a b) t) =
    match L.asTBitVector (S.ty a), L.asTBitVector (S.ty b) with
    | some m1, some m2 =>
      match den ρ m1.toNat a, den ρ m2.toNat b with
      | some x, some y => some ((x ++ y).setWidth n)
      | _, _ => none
    | _, _ => none
  den_Neg : ∀ ρ n c a t, den ρ n (B.node (L.NegK c a) t) = negOp c (den ρ n a)
  den_BvNot : ∀ ρ n a t, den ρ n (B.node (L.BvNotK a) t) = (den ρ n a).map (~~~·)
  den_BvOfBool : ∀ ρ n k a t, den ρ n (B.node (L.BvOfBoolK k a) t) =
    (denB ρ a).map (fun b => if b then 1 else 0)
  den_BvExtend : ∀ ρ n s k a t, den ρ n (B.node (L.BvExtendK s k a) t) =
    match L.asTBitVector (S.ty a) with
    | some m => (den ρ m.toNat a).map (fun x => if s then x.signExtend n else x.setWidth n)
    | none => none
  den_BvExtract : ∀ ρ n i j a t, den ρ n (B.node (L.BvExtractK i j a) t) =
    match L.asTBitVector (S.ty a) with
    | some m => (den ρ m.toNat a).map (fun x => x.extractLsb' i.toNat n)
    | none => none
  den_Ite : ∀ ρ n g a b t, den ρ n (B.node (LBool.IteK g a b) t) =
    match denB ρ g with
    | some true => den ρ n a
    | some false => den ρ n b
    | none => none
  denB_Bool : ∀ ρ c t, denB ρ (B.node (LBool.BoolK c) t) = some c
  denB_Not : ∀ ρ a t, denB ρ (B.node (LBool.NotK a) t) = (denB ρ a).map (!·)
  denB_And : ∀ ρ a b t, denB ρ (B.node (LBool.AndK a b) t) = andB (denB ρ a) (denB ρ b)
  denB_Or : ∀ ρ a b t, denB ρ (B.node (LBool.OrK a b) t) = orB (denB ρ a) (denB ρ b)
  denB_Ite : ∀ ρ g a b t, denB ρ (B.node (LBool.IteK g a b) t) =
    match denB ρ g with
    | some true => denB ρ a
    | some false => denB ρ b
    | none => none
  denB_Eq : ∀ ρ a b t, denB ρ (B.node (LBool.EqK a b) t) =
    match L.asTBitVector (S.ty a) with
    | some m =>
      if 0 < m then binB (fun x y => decide (x = y)) (den ρ m.toNat a) (den ρ m.toNat b)
      else none
    | none =>
      if S.ty a = LBool.TBool then binB (fun x y => decide (x = y)) (denB ρ a) (denB ρ b)
      else evB LBool ρ (B.node (LBool.EqK a b) t)
  denB_Lt : ∀ ρ s a b t, denB ρ (B.node (L.LtK s a b) t) =
    match L.asTBitVector (S.ty a) with
    | some m =>
      if 0 < m then binB (fun x y => if s then x.slt y else x.ult y)
        (den ρ m.toNat a) (den ρ m.toNat b)
      else none
    | none => evB LBool ρ (B.node (L.LtK s a b) t)
  denB_Leq : ∀ ρ s a b t, denB ρ (B.node (L.LeqK s a b) t) =
    match L.asTBitVector (S.ty a) with
    | some m =>
      if 0 < m then binB (fun x y => if s then x.sle y else x.ule y)
        (den ρ m.toNat a) (den ρ m.toNat b)
      else none
    | none => evB LBool ρ (B.node (L.LeqK s a b) t)
  denB_AddOvf : ∀ ρ s a b t, denB ρ (B.node (L.AddOvfK s a b) t) =
    match L.asTBitVector (S.ty a) with
    | some m =>
      if 0 < m then binB (fun x y => if s then x.saddOverflow y else x.uaddOverflow y)
        (den ρ m.toNat a) (den ρ m.toNat b)
      else none
    | none => evB LBool ρ (B.node (L.AddOvfK s a b) t)
  denB_SubOvf : ∀ ρ s a b t, denB ρ (B.node (L.SubOvfK s a b) t) =
    match L.asTBitVector (S.ty a) with
    | some m =>
      if 0 < m then binB (fun x y => if s then x.ssubOverflow y else x.usubOverflow y)
        (den ρ m.toNat a) (den ρ m.toNat b)
      else none
    | none => evB LBool ρ (B.node (L.SubOvfK s a b) t)
  denB_MulOvf : ∀ ρ s a b t, denB ρ (B.node (L.MulOvfK s a b) t) =
    match L.asTBitVector (S.ty a) with
    | some m =>
      if 0 < m then binB (fun x y => if s then x.smulOverflow y else x.umulOverflow y)
        (den ρ m.toNat a) (den ρ m.toNat b)
      else none
    | none => evB LBool ρ (B.node (L.MulOvfK s a b) t)
  -- the primitives (`Prim`) and the terms that the helpers build
  size_of_ty_TBitVector : ∀ n, L.bitvec_size_of_ty (L.TBitVector n) = n
  size_of_ty_TLoc : ∀ n, L.bitvec_size_of_ty (L.TLoc n) = n
  mk_masked_eq : ∀ n z, L.bitvec_mk_masked n z =
    B.node (L.BitVecK (z % 2 ^ n.toNat)) (L.TBitVector n)
  mk_bv_eq : ∀ n z, L.bitvec_mk_bv n z = L.bitvec_mk_masked n z
  bv_zero_eq : ∀ n, L.bitvec_bv_zero n = B.node (L.BitVecK 0) (L.TBitVector n)
  bv_one_eq : ∀ n, L.bitvec_bv_one n = B.node (L.BitVecK 1) (L.TBitVector n)
  lit_add_eq : ∀ s s' a b, L.bitvec_lit_add s s' a b = Prim.lit_add (L.bitvec_size_of_ty s) a b
  lit_sub_eq : ∀ s s' a b, L.bitvec_lit_sub s s' a b = Prim.lit_sub (L.bitvec_size_of_ty s) a b
  lit_mul_eq : ∀ s s' a b, L.bitvec_lit_mul s s' a b = Prim.lit_mul (L.bitvec_size_of_ty s) a b
  lit_neg_eq : ∀ s a, L.bitvec_lit_neg s a = Prim.lit_neg (L.bitvec_size_of_ty s) a
  lit_udiv_eq : ∀ s s' a b, L.bitvec_lit_udiv s s' a b =
    Prim.lit_udiv (L.bitvec_size_of_ty s) a b
  lit_sdiv_eq : ∀ s s' a b, L.bitvec_lit_sdiv s s' a b =
    Prim.lit_sdiv (L.bitvec_size_of_ty s) a b
  lit_and_eq : ∀ s s' a b, L.bitvec_lit_and s s' a b = Prim.lit_and (L.bitvec_size_of_ty s) a b
  lit_or_eq : ∀ s s' a b, L.bitvec_lit_or s s' a b = Prim.lit_or (L.bitvec_size_of_ty s) a b
  lit_xor_eq : ∀ s s' a b, L.bitvec_lit_xor s s' a b = Prim.lit_xor (L.bitvec_size_of_ty s) a b
  lit_not_eq : ∀ s a, L.bitvec_lit_not s a = Prim.lit_not (L.bitvec_size_of_ty s) a
  lit_shl_eq : ∀ s s' a b, L.bitvec_lit_shl s s' a b = Prim.lit_shl (L.bitvec_size_of_ty s) a b
  lit_lshr_eq : ∀ s s' a b, L.bitvec_lit_lshr s s' a b =
    Prim.lit_lshr (L.bitvec_size_of_ty s) a b
  lit_ashr_eq : ∀ s s' a b, L.bitvec_lit_ashr s s' a b =
    Prim.lit_ashr (L.bitvec_size_of_ty s) a b
  lit_urem_eq : ∀ s s' a b, L.bitvec_lit_urem s s' a b =
    Prim.lit_urem (L.bitvec_size_of_ty s) a b
  lit_srem_eq : ∀ s s' a b, L.bitvec_lit_srem s s' a b =
    Prim.lit_srem (L.bitvec_size_of_ty s) a b
  lit_smod_eq : ∀ s s' a b, L.bitvec_lit_smod s s' a b =
    Prim.lit_smod (L.bitvec_size_of_ty s) a b
  lit_extract_eq : ∀ i j s a, L.bitvec_lit_extract i j s a = Prim.lit_extract i j a
  lit_zext_eq : ∀ k s a, L.bitvec_lit_zext k s a = Prim.lit_zext a
  lit_sext_eq : ∀ k s a, L.bitvec_lit_sext k s a = Prim.lit_sext k (L.bitvec_size_of_ty s) a
  lit_concat_eq : ∀ s s' a b, L.bitvec_lit_concat s s' a b =
    Prim.lit_concat (L.bitvec_size_of_ty s') a b
  signed_extract_eq : ∀ z o l, L.bitvec_signed_extract z o l = Prim.signed_extract z o l
  popcount_eq : ∀ z, L.bitvec_popcount z = Prim.popcount z
  log2_eq : ∀ z, L.bitvec_log2 z = Prim.log2 z
  tdiv_eq : ∀ a b, L.bitvec_tdiv a b = Prim.tdiv a b
  trem_eq : ∀ a b, L.bitvec_trem a b = Prim.trem a b
  divisible_eq : ∀ a b, L.bitvec_divisible a b = Prim.divisible a b
  z_land_eq : ∀ a b, L.bitvec_z_land a b = Prim.z_land a b
  z_lsl_eq : ∀ a b, L.bitvec_z_lsl a b = Prim.z_lsl a b
  -- the subsorts: a term of `TNonzero` (resp. `TZero`) is not zero (resp. is
  -- zero) when it has a value; literals are in them by their value
  nonzero_ev : ∀ ρ t n (x : BitVec n), L.Nonzero t → S.WT t → S.ev ρ t = some (vbv n x) →
    x ≠ 0
  zero_ev : ∀ ρ t n (x : BitVec n), L.Zero t → S.WT t → S.ev ρ t = some (vbv n x) → x = 0
  nonzero_BitVec : ∀ z t, (∀ n : Nat, L.bitvec_size_of_ty t = n → BitVec.ofInt n z ≠ 0) →
    L.Nonzero (B.node (L.BitVecK z) t)
  /-- The values of a term are below `2 ^ (msb_of v + 1)` (`msb_of` recurses on the
  terms, whose induction the interface does not give). -/
  den_msb : ∀ ρ v (n : Nat) x, S.WT v → S.ty v = L.TBitVector n → den ρ n v = some x →
    x.toNat < 2 ^ (L.bitvec_msb_of v + 1).toNat

end BitvecMod
