import BitvecMod.Lib.Rule
import KanonBool.Lib.Lift

/-!
# Refinement by congruence

The congruence lemmas of the nodes of the bitvec module, with which
`kanon_congr` proves that the specs are monotone (`Lifts.lean`): refining the
operands of a node refines the node, whose sort may be given by its operands
(the hypothesis `ht`, which `kanon_congr_side` proves). They are proved once
for the nodes of each shape (`refines_bin`, `refines_pred`, `refines_un`), by
their structural values.
-/

namespace BitvecMod

open Classical Kanon Kanon.Sem

set_option linter.unusedSectionVars false

namespace Lib

variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
  {LBool : KanonBool.Syntax B} {LCore : CoreMod.Syntax B} {L : Syntax B LBool LCore}
  [KanonBool.Sem LBool] [CoreMod.Sem LCore] [Sem L]

/-- A binary node on bit-vectors of the sort of its operands. -/
theorem refines_bin {K : S.Term → S.Term → B.Kind}
    {F : ∀ {n : Nat}, Option (BitVec n) → Option (BitVec n) → Option (BitVec n)}
    (hF : ∀ {n : Nat} {x x' y y' : Option (BitVec n)}, OLe x x' → OLe y y' → OLe (F x y) (F x' y'))
    (hWT : ∀ a b t, S.WT (B.node (K a b) t) ↔
      ((∃ n : Int, 0 < n ∧ S.ty a = L.TBitVector n) ∧ S.ty b = S.ty a ∧ t = S.ty a) ∧
        S.WT a ∧ S.WT b)
    (hden : ∀ ρ n a b t, Sem.den L ρ n (B.node (K a b) t) = F (Sem.den L ρ n a) (Sem.den L ρ n b))
    {a a' b b' : S.Term} {t t' : S.Ty} (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (K a b) t) → t' = t) :
    S.Refines (B.node (K a b) t) (B.node (K a' b') t') := by
  refine Refines.den (L := L) (fun w => ?_) (fun w => ?_) (fun n w hs ρ x e => ?_) <;>
    have e' := ht w <;> subst e' <;> rw [hWT] at w <;>
    obtain ⟨⟨⟨m, hm0, hm⟩, hb', ht'⟩, wa, wb⟩ := w
  · exact ⟨m, by rw [B.ty_node, ht', hm]⟩
  · obtain ⟨wa', sa⟩ := ha.syn wa
    obtain ⟨wb', sb⟩ := hb.syn wb
    exact ⟨(hWT _ _ _).2 ⟨⟨⟨m, hm0, sa.trans hm⟩, by rw [sa, sb, hb'], by rw [sa, ht']⟩,
      wa', wb'⟩, by rw [B.ty_node, B.ty_node]⟩
  · rw [B.ty_node, ht'] at hs
    rw [hden] at e ⊢
    exact hF (den_of ha wa hs ρ) (den_of hb wb (hb'.trans hs) ρ) x e

/-- A unary node on bit-vectors of the sort of its operand. -/
theorem refines_un {K : S.Term → B.Kind}
    {F : ∀ {n : Nat}, Option (BitVec n) → Option (BitVec n)}
    (hF : ∀ {n : Nat} {x x' : Option (BitVec n)}, OLe x x' → OLe (F x) (F x'))
    (hWT : ∀ a t, S.WT (B.node (K a) t) ↔
      ((∃ n : Int, 0 < n ∧ S.ty a = L.TBitVector n) ∧ t = S.ty a) ∧ S.WT a)
    (hden : ∀ ρ n a t, Sem.den L ρ n (B.node (K a) t) = F (Sem.den L ρ n a))
    {a a' : S.Term} {t t' : S.Ty} (ha : S.Refines a a')
    (ht : S.WT (B.node (K a) t) → t' = t) :
    S.Refines (B.node (K a) t) (B.node (K a') t') := by
  refine Refines.den (L := L) (fun w => ?_) (fun w => ?_) (fun n w hs ρ x e => ?_) <;>
    have e' := ht w <;> subst e' <;> rw [hWT] at w <;>
    obtain ⟨⟨⟨m, hm0, hm⟩, ht'⟩, wa⟩ := w
  · exact ⟨m, by rw [B.ty_node, ht', hm]⟩
  · obtain ⟨wa', sa⟩ := ha.syn wa
    exact ⟨(hWT _ _).2 ⟨⟨⟨m, hm0, sa.trans hm⟩, by rw [sa, ht']⟩, wa'⟩,
      by rw [B.ty_node, B.ty_node]⟩
  · rw [B.ty_node, ht'] at hs
    rw [hden] at e ⊢
    exact hF (den_of ha wa hs ρ) x e

/-- A binary predicate on bit-vectors of the same sort. -/
theorem refines_pred {K : S.Term → S.Term → B.Kind}
    {f : ∀ {n : Nat}, BitVec n → BitVec n → Bool}
    (hWT : ∀ a b t, S.WT (B.node (K a b) t) ↔
      ((∃ n : Int, 0 < n ∧ S.ty a = L.TBitVector n) ∧ S.ty b = S.ty a ∧ t = LBool.TBool) ∧
        S.WT a ∧ S.WT b)
    (hden : ∀ ρ a b t, Sem.denB L ρ (B.node (K a b) t) =
      match L.asTBitVector (S.ty a) with
      | some m =>
        if 0 < m then binB f (Sem.den L ρ m.toNat a) (Sem.den L ρ m.toNat b) else none
      | none => evB LBool ρ (B.node (K a b) t))
    {a a' b b' : S.Term} {t t' : S.Ty} (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (K a b) t) → t' = t) :
    S.Refines (B.node (K a b) t) (B.node (K a' b') t') := by
  refine Refines.denB (L := L) (fun w => ?_) (fun w => ?_) (fun w ρ x e => ?_) <;>
    have e' := ht w <;> subst e' <;> rw [hWT] at w <;>
    obtain ⟨⟨⟨m, hm0, hm⟩, hb', ht'⟩, wa, wb⟩ := w
  · rw [B.ty_node, ht']
  · obtain ⟨wa', sa⟩ := ha.syn wa
    obtain ⟨wb', sb⟩ := hb.syn wb
    exact ⟨(hWT _ _ _).2 ⟨⟨⟨m, hm0, sa.trans hm⟩, by rw [sa, sb, hb'], ht'⟩, wa', wb'⟩,
      by rw [B.ty_node, B.ty_node]⟩
  · obtain ⟨-, sa⟩ := ha.syn wa
    have hm' : S.ty a = L.TBitVector (m.toNat : Nat) := by
      rw [hm, Int.toNat_of_nonneg (by omega)]
    simp only [hden, hm, L.asTBitVector_sort, hm0, ite_true] at e
    simp only [hden, sa, hm, L.asTBitVector_sort, hm0, ite_true]
    exact binB_mono (den_of ha wa hm' ρ) (den_of hb wb (hb'.trans hm') ρ) x e

section
variable {a a' b b' : S.Term} {t t' : S.Ty}

theorem refines_add {c} (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.AddK c a b) t) → t' = t) :
    S.Refines (B.node (L.AddK c a b) t) (B.node (L.AddK c a' b') t') :=
  refines_bin (F := ckOp c _ _ _) ckOp_mono (L.WT_Add c) (fun ρ n => Sem.den_Add ρ n c) ha hb ht
theorem refines_sub {c} (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.SubK c a b) t) → t' = t) :
    S.Refines (B.node (L.SubK c a b) t) (B.node (L.SubK c a' b') t') :=
  refines_bin (F := ckOp c _ _ _) ckOp_mono (L.WT_Sub c) (fun ρ n => Sem.den_Sub ρ n c) ha hb ht
theorem refines_mul {c} (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.MulK c a b) t) → t' = t) :
    S.Refines (B.node (L.MulK c a b) t) (B.node (L.MulK c a' b') t') :=
  refines_bin (F := ckOp c _ _ _) ckOp_mono (L.WT_Mul c) (fun ρ n => Sem.den_Mul ρ n c) ha hb ht
theorem refines_div {s} (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.DivK s a b) t) → t' = t) :
    S.Refines (B.node (L.DivK s a b) t) (B.node (L.DivK s a' b') t') :=
  refines_bin (F := binOp _) binOp_mono (L.WT_Div s) (fun ρ n => Sem.den_Div ρ n s) ha hb ht
theorem refines_rem {s} (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.RemK s a b) t) → t' = t) :
    S.Refines (B.node (L.RemK s a b) t) (B.node (L.RemK s a' b') t') :=
  refines_bin (F := binOp _) binOp_mono (L.WT_Rem s) (fun ρ n => Sem.den_Rem ρ n s) ha hb ht
theorem refines_mod (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.ModK a b) t) → t' = t) :
    S.Refines (B.node (L.ModK a b) t) (B.node (L.ModK a' b') t') :=
  refines_bin (F := binOp _) binOp_mono L.WT_Mod Sem.den_Mod ha hb ht
theorem refines_bitAnd (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.BitAndK a b) t) → t' = t) :
    S.Refines (B.node (L.BitAndK a b) t) (B.node (L.BitAndK a' b') t') :=
  refines_bin (F := binOp _) binOp_mono L.WT_BitAnd Sem.den_BitAnd ha hb ht
theorem refines_bitOr (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.BitOrK a b) t) → t' = t) :
    S.Refines (B.node (L.BitOrK a b) t) (B.node (L.BitOrK a' b') t') :=
  refines_bin (F := binOp _) binOp_mono L.WT_BitOr Sem.den_BitOr ha hb ht
theorem refines_bitXor (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.BitXorK a b) t) → t' = t) :
    S.Refines (B.node (L.BitXorK a b) t) (B.node (L.BitXorK a' b') t') :=
  refines_bin (F := binOp _) binOp_mono L.WT_BitXor Sem.den_BitXor ha hb ht
theorem refines_shl (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.ShlK a b) t) → t' = t) :
    S.Refines (B.node (L.ShlK a b) t) (B.node (L.ShlK a' b') t') :=
  refines_bin (F := binOp _) binOp_mono L.WT_Shl Sem.den_Shl ha hb ht
theorem refines_lShr (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.LShrK a b) t) → t' = t) :
    S.Refines (B.node (L.LShrK a b) t) (B.node (L.LShrK a' b') t') :=
  refines_bin (F := binOp _) binOp_mono L.WT_LShr Sem.den_LShr ha hb ht
theorem refines_aShr (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.AShrK a b) t) → t' = t) :
    S.Refines (B.node (L.AShrK a b) t) (B.node (L.AShrK a' b') t') :=
  refines_bin (F := binOp _) binOp_mono L.WT_AShr Sem.den_AShr ha hb ht
theorem refines_neg {c} (ha : S.Refines a a') (ht : S.WT (B.node (L.NegK c a) t) → t' = t) :
    S.Refines (B.node (L.NegK c a) t) (B.node (L.NegK c a') t') :=
  refines_un (F := negOp c) negOp_mono (L.WT_Neg c) (fun ρ n => Sem.den_Neg ρ n c) ha ht
theorem refines_bvNot (ha : S.Refines a a') (ht : S.WT (B.node (L.BvNotK a) t) → t' = t) :
    S.Refines (B.node (L.BvNotK a) t) (B.node (L.BvNotK a') t') :=
  refines_un (F := Option.map (~~~·)) map_mono L.WT_BvNot Sem.den_BvNot ha ht
theorem refines_lt {s} (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.LtK s a b) t) → t' = t) :
    S.Refines (B.node (L.LtK s a b) t) (B.node (L.LtK s a' b') t') :=
  refines_pred (f := fun x y => if s then x.slt y else x.ult y) (L.WT_Lt s)
    (fun ρ => Sem.denB_Lt ρ s) ha hb ht
theorem refines_leq {s} (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.LeqK s a b) t) → t' = t) :
    S.Refines (B.node (L.LeqK s a b) t) (B.node (L.LeqK s a' b') t') :=
  refines_pred (f := fun x y => if s then x.sle y else x.ule y) (L.WT_Leq s)
    (fun ρ => Sem.denB_Leq ρ s) ha hb ht
theorem refines_addOvf {s} (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.AddOvfK s a b) t) → t' = t) :
    S.Refines (B.node (L.AddOvfK s a b) t) (B.node (L.AddOvfK s a' b') t') :=
  refines_pred (f := fun x y => if s then x.saddOverflow y else x.uaddOverflow y) (L.WT_AddOvf s)
    (fun ρ => Sem.denB_AddOvf ρ s) ha hb ht
theorem refines_subOvf {s} (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.SubOvfK s a b) t) → t' = t) :
    S.Refines (B.node (L.SubOvfK s a b) t) (B.node (L.SubOvfK s a' b') t') :=
  refines_pred (f := fun x y => if s then x.ssubOverflow y else x.usubOverflow y) (L.WT_SubOvf s)
    (fun ρ => Sem.denB_SubOvf ρ s) ha hb ht
theorem refines_mulOvf {s} (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.MulOvfK s a b) t) → t' = t) :
    S.Refines (B.node (L.MulOvfK s a b) t) (B.node (L.MulOvfK s a' b') t') :=
  refines_pred (f := fun x y => if s then x.smulOverflow y else x.umulOverflow y) (L.WT_MulOvf s)
    (fun ρ => Sem.denB_MulOvf ρ s) ha hb ht

theorem refines_bvOfBool {k} (ha : S.Refines a a')
    (ht : S.WT (B.node (L.BvOfBoolK k a) t) → t' = t) :
    S.Refines (B.node (L.BvOfBoolK k a) t) (B.node (L.BvOfBoolK k a') t') := by
  refine Refines.den (L := L) (fun w => ?_) (fun w => ?_) (fun n w hs ρ x e => ?_) <;>
    have e' := ht w <;> subst e' <;> rw [L.WT_BvOfBool] at w <;>
    obtain ⟨⟨hk, hb, rfl⟩, wa⟩ := w
  · exact ⟨k, B.ty_node _ _⟩
  · obtain ⟨wa', sa⟩ := ha.syn wa
    exact ⟨(L.WT_BvOfBool _ _ _).2 ⟨⟨hk, sa.trans hb, rfl⟩, wa'⟩, by rw [B.ty_node, B.ty_node]⟩
  · rw [Sem.den_BvOfBool] at e ⊢
    exact map_mono (denB_of ha wa hb ρ) x e

theorem refines_bvExtract {i j} (ha : S.Refines a a')
    (ht : S.WT (B.node (L.BvExtractK i j a) t) → t' = t) :
    S.Refines (B.node (L.BvExtractK i j a) t) (B.node (L.BvExtractK i j a') t') := by
  refine Refines.den (L := L) (fun w => ?_) (fun w => ?_) (fun n w hs ρ x e => ?_) <;>
    have e' := ht w <;> subst e' <;> rw [L.WT_BvExtract] at w <;>
    obtain ⟨⟨m, hm, h1, h2, h3, rfl⟩, wa⟩ := w
  · exact ⟨_, B.ty_node _ _⟩
  · obtain ⟨wa', sa⟩ := ha.syn wa
    exact ⟨(L.WT_BvExtract _ _ _ _).2 ⟨⟨m, sa.trans hm, h1, h2, h3, rfl⟩, wa'⟩,
      by rw [B.ty_node, B.ty_node]⟩
  · obtain ⟨-, sa⟩ := ha.syn wa
    have hm' : S.ty a = L.TBitVector (m.toNat : Nat) := by
      rw [hm, Int.toNat_of_nonneg (by omega)]
    simp only [Sem.den_BvExtract, hm, L.asTBitVector_sort] at e
    simp only [Sem.den_BvExtract, sa, hm, L.asTBitVector_sort]
    rw [hm] at hm'
    exact map_mono (den_of ha wa (hm.trans hm') ρ) x e

theorem refines_bvExtend {s k} (ha : S.Refines a a')
    (ht : S.WT (B.node (L.BvExtendK s k a) t) → t' = t) :
    S.Refines (B.node (L.BvExtendK s k a) t) (B.node (L.BvExtendK s k a') t') := by
  refine Refines.den (L := L) (fun w => ?_) (fun w => ?_) (fun n w hs ρ x e => ?_) <;>
    have e' := ht w <;> subst e' <;> rw [L.WT_BvExtend] at w <;>
    obtain ⟨⟨m, hm0, hm, h1, rfl⟩, wa⟩ := w
  · exact ⟨_, B.ty_node _ _⟩
  · obtain ⟨wa', sa⟩ := ha.syn wa
    exact ⟨(L.WT_BvExtend _ _ _ _).2 ⟨⟨m, hm0, sa.trans hm, h1, rfl⟩, wa'⟩,
      by rw [B.ty_node, B.ty_node]⟩
  · obtain ⟨-, sa⟩ := ha.syn wa
    have hm' : S.ty a = L.TBitVector (m.toNat : Nat) := by
      rw [hm, Int.toNat_of_nonneg (by omega)]
    simp only [Sem.den_BvExtend, hm, L.asTBitVector_sort] at e
    simp only [Sem.den_BvExtend, sa, hm, L.asTBitVector_sort]
    exact map_mono (den_of ha wa hm' ρ) x e

theorem refines_bvConcat (ha : S.Refines a a') (hb : S.Refines b b')
    (ht : S.WT (B.node (L.BvConcatK a b) t) → t' = t) :
    S.Refines (B.node (L.BvConcatK a b) t) (B.node (L.BvConcatK a' b') t') := by
  refine Refines.den (L := L) (fun w => ?_) (fun w => ?_) (fun n w hs ρ x e => ?_) <;>
    have e' := ht w <;> subst e' <;> rw [L.WT_BvConcat] at w <;>
    obtain ⟨⟨m1, m2, h1, h2, hm1, hm2, rfl⟩, wa, wb⟩ := w
  · exact ⟨_, B.ty_node _ _⟩
  · obtain ⟨wa', sa⟩ := ha.syn wa
    obtain ⟨wb', sb⟩ := hb.syn wb
    exact ⟨(L.WT_BvConcat _ _ _).2 ⟨⟨m1, m2, h1, h2, sa.trans hm1, sb.trans hm2, rfl⟩, wa', wb'⟩,
      by rw [B.ty_node, B.ty_node]⟩
  · obtain ⟨-, sa⟩ := ha.syn wa
    obtain ⟨-, sb⟩ := hb.syn wb
    have hm1' : S.ty a = L.TBitVector (m1.toNat : Nat) := by
      rw [hm1, Int.toNat_of_nonneg (by omega)]
    have hm2' : S.ty b = L.TBitVector (m2.toNat : Nat) := by
      rw [hm2, Int.toNat_of_nonneg (by omega)]
    simp only [Sem.den_BvConcat, hm1, hm2, L.asTBitVector_sort] at e
    simp only [Sem.den_BvConcat, sa, sb, hm1, hm2, L.asTBitVector_sort]
    have da := den_of ha wa hm1' ρ
    have db := den_of hb wb hm2' ρ
    rcases h : Sem.den L ρ m1.toNat a with _ | xa <;> rw [h] at e
    · cases e
    rcases h' : Sem.den L ρ m2.toNat b with _ | xb <;> rw [h'] at e
    · cases e
    rw [da xa h, db xb h']
    exact e

end

attribute [kanon_congr_lemma] refines_add refines_sub refines_mul refines_div refines_rem
  refines_mod refines_bitAnd refines_bitOr refines_bitXor refines_shl refines_lShr refines_aShr
  refines_neg refines_bvNot refines_lt refines_leq refines_addOvf refines_subOvf refines_mulOvf
  refines_bvOfBool refines_bvExtract refines_bvExtend refines_bvConcat

end Lib

open Lean Meta Elab Tactic in
/-- Adds `hty_i : S.ty x' = S.ty x` for every `S.Refines x x'` of the context
whose `x` is known to be well-typed (`S.WT x`); returns their names. -/
def tyRefines (g : MVarId) : MetaM (MVarId × Array Name) := g.withContext do
  let mut g := g
  let mut names := #[]
  let lctx ← getLCtx
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars d.type)
    unless ty.isAppOfArity ``Kanon.Sem.Refines 3 do continue
    let s := ty.getArg! 0
    let x := ty.getArg! 1
    let wt := mkApp2 (mkConst ``Kanon.Sem.WT) s x
    let mut hw? : Option Expr := none
    for d' in lctx do
      if d'.isImplementationDetail then continue
      if ← isDefEq (← instantiateMVars d'.type) wt then
        hw? := some d'.toExpr
        break
    let some hw := hw? | continue
    let pf ← mkAppM ``Kanon.Sem.ty_refines #[d.toExpr, hw]
    let n := Name.mkSimple s!"hty_{names.size}"
    let (_, g') ← (← g.assert n (← inferType pf) pf).intro1P
    g := g'
    names := names.push n
  return (g, names)

open Lean Elab Tactic in
/-- Rewrites, in the goal, the sorts of the refined terms of the context
(`S.Refines x x'`, with `S.WT x`) to the sorts of the terms they refine. -/
elab "bv_ty_refines" : tactic => do
  let (g, names) ← tyRefines (← getMainGoal)
  replaceMainGoal [g]
  if names.isEmpty then return
  let ids : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    names.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  evalTactic (← `(tactic| try simp only [Kanon.Base.ty_node, Syntax.bitvec_size_eq, $ids,*] at ⊢))

/-- The typing of the nodes (`bv_wt`: those of the bool and bitvec modules, and
of the modules that use it), and the terms that the helpers of the bitvec module
build. -/
macro "bv_wt_simp" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [bv_wt, Sem.bv_zero_eq, Sem.bv_one_eq, Sem.mk_bv_eq, Sem.mk_masked_eq] $[$loc]?)

/-- `kanon_congr` first rewrites the sorts of the refined terms, which their
refinements preserve once they are well-typed. -/
macro_rules
  | `(tactic| kanon_congr_pre) => `(tactic| (
      apply Kanon.Sem.Refines.of_WT
      intro w
      (try bv_wt_simp at w)
      (try kanon_split)
      bv_ty_refines))

/-- The side goals of the congruence lemmas: the sort of a node on the right,
given by its refined operands, is that of the node on the left (once it is
well-typed, so are its operands). -/
macro_rules | `(tactic| kanon_congr_side) => `(tactic|
  (intro w
   simp only [Syntax.WT_Add, Syntax.WT_Sub, Syntax.WT_Mul, Syntax.WT_Div, Syntax.WT_Rem,
     Syntax.WT_Mod, Syntax.WT_BitAnd, Syntax.WT_BitOr, Syntax.WT_BitXor, Syntax.WT_Shl,
     Syntax.WT_LShr, Syntax.WT_AShr, Syntax.WT_Neg, Syntax.WT_BvNot, Syntax.WT_Lt,
     Syntax.WT_Leq, Syntax.WT_AddOvf, Syntax.WT_SubOvf, Syntax.WT_MulOvf, Syntax.WT_BvOfBool,
     Syntax.WT_BvExtract, Syntax.WT_BvExtend, Syntax.WT_BvConcat] at w
   kanon_split
   first
     | exact Kanon.Sem.ty_refines (by assumption) (by assumption)
     | (congr 1; rw [Kanon.Sem.ty_refines (by assumption) (by assumption)])
     | (congr 2; rw [Kanon.Sem.ty_refines (by assumption) (by assumption)])))

end BitvecMod
