import Kanon.Staged.Interface.Bitvec
import Kanon.Lang.Bool
import Kanon.Lang.Core
import Kanon.Lib.Den
import Kanon.Lib.Lit
import Kanon.Lib.Msb
import BitvecMod.Sem

/-!
# The language, for the bitvec module

The bitvec module is proved once (`BitvecMod`): the language gives its
interface (`bitvecSyntax`) and what it needs of its semantics, the instance of
its `Sem` class. Its values by the structure of the terms are the language's
`den` and `denB` (`Lib/Den.lean`), and its primitives are those of the module
(`BitvecMod.Prim`), by definition.
-/

namespace Kanon

open Classical Lib

variable (FS : FloatSem)

namespace Lang

/-! The operations on the values of the operands of the language are those of
the module. -/

theorem ckOp_eq {n c s u f} : @Lib.ckOp n c s u f = BitvecMod.ckOp c s u f := by
  funext a b; cases a <;> cases b <;> rfl
theorem binOp_eq {n f} : @Lib.binOp n f = BitvecMod.binOp f := by
  funext a b; cases a <;> cases b <;> rfl
theorem negOp_eq {n c} : @Lib.negOp n c = BitvecMod.negOp c := by
  funext a; cases a <;> rfl
theorem andB_eq : Lib.andB = BitvecMod.andB := by
  funext a b; rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> rfl
theorem orB_eq : Lib.orB = BitvecMod.orB := by
  funext a b; rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> rfl
theorem binB_eq {α f} : @Lib.binB α f = BitvecMod.binB f := by
  funext a b; cases a <;> cases b <;> rfl

theorem evalB_eq {ρ t} : evalB FS ρ t = BitvecMod.evB (boolSyntax FS) ρ t := by
  cases h : evalB FS ρ t with
  | none =>
    cases h' : BitvecMod.evB (boolSyntax FS) ρ t with
    | none => rfl
    | some b => rw [BitvecMod.evB_eq_some (S := sem FS)] at h'; rw [(evalB_eq_some).2 h'] at h; cases h
  | some b => exact ((BitvecMod.evB_eq_some (S := sem FS)).2 ((evalB_eq_some).1 h)).symm

theorem evalBV_eq {ρ n t} : evalBV FS ρ n t = BitvecMod.evBVof (S := sem FS) Val.bv ρ n t := by
  have inj : ∀ n (x y : BitVec n), Val.bv n x = Val.bv n y → x = y := by
    intro n x y h; cases h; rfl
  cases h : evalBV FS ρ n t with
  | none =>
    cases h' : BitvecMod.evBVof (S := sem FS) Val.bv ρ n t with
    | none => rfl
    | some x =>
      rw [BitvecMod.evBVof_eq_some (S := sem FS) inj] at h'; rw [(evalBV_eq_some).2 h'] at h; cases h
  | some x => exact ((BitvecMod.evBVof_eq_some (S := sem FS) inj).2 ((evalBV_eq_some).1 h)).symm

theorem popcountNat_eq : ∀ k, popcountNat k = BitvecMod.Prim.popcountNat k
  | 0 => by simp [popcountNat, BitvecMod.Prim.popcountNat]
  | k + 1 => by
    rw [popcountNat, BitvecMod.Prim.popcountNat, popcountNat_eq ((k + 1) / 2)]
termination_by k => k
decreasing_by omega

theorem vbv_inj' : ∀ n m (x : BitVec n) (y : BitVec m), Val.bv n x = Val.bv m y →
    (⟨n, x⟩ : Σ n, BitVec n) = ⟨m, y⟩ := by
  intro n m x y h; cases h; rfl

/-- The bit-vector that a value of the language is. -/
theorem decBV_eq (v : Val) : BitvecMod.decBV Val.bv (some v) =
    match v with
    | .bv n x => some ⟨n, x⟩
    | _ => none := by
  cases v with
  | bv n x => exact BitvecMod.decBV_some vbv_inj' n x
  | _ => rw [BitvecMod.decBV, dif_neg]; rintro ⟨_, _, h⟩; cases h

end Lang

open Lang in
/-- Unfolds `den` or `denB` once, at a node of the module, and rewrites the
operations of the language to those of the module. -/
macro "lang_den" : tactic => `(tactic| (
  intros
  simp only [bitvecSyntax, boolSyntax, modBase, Kanon.Lib.den, Kanon.Lib.denB, ckOp_eq,
    binOp_eq, negOp_eq, andB_eq, orB_eq, binB_eq, evalB_eq]))

/-- What the bitvec module needs of the semantics. -/
noncomputable instance bitvecSem : BitvecMod.Sem (S := sem FS) (bitvecSyntax FS) where
  vbv := Val.bv
  vbv_inj _ _ _ h := by cases h; rfl
  vbv_ne _ _ _ _ h e := by cases e; exact h rfl
  vbv_ne_vbool _ _ _ e := by cases e
  ev_bv ρ t v m w ht e := by
    have := ev_hasSort t w v e
    simp only [bitvecSyntax, sem] at ht
    rw [ht] at this
    rcases v with _ | ⟨k, x⟩ | _ | _ | _ | _ <;> simp [Val.hasSort] at this
    obtain ⟨rfl, hk⟩ := this
    exact ⟨by omega, x, by simp⟩
  ev_loc ρ t v m w ht e := by
    have := ev_hasSort t w v e
    simp only [bitvecSyntax, sem] at ht
    rw [ht] at this
    rcases v with _ | ⟨k, x⟩ | _ | _ | _ | _ <;> simp [Val.hasSort] at this
    obtain ⟨rfl, hk⟩ := this
    exact ⟨by omega, x, by simp⟩
  ev_BitVec _ _ _ := by simp [bitvecSyntax, modBase, sem, ev, Ty.width]
  ev_LocLit _ _ _ := by simp [bitvecSyntax, modBase, sem, ev, Ty.width]
  bv_wf_BitVec _ _ := by simp [bitvecSyntax, modBase, bv_wf]
  bv_wf_LocLit _ _ := by simp [bitvecSyntax, modBase, bv_wf]
  den := den FS
  denB := denB FS
  den_iff ρ n t x w ht := by
    simp only [bitvecSyntax, sem] at w ht ⊢
    rw [← evalBV_den t w ht, evalBV_eq_some, eval_eq_ev w]
  denB_iff ρ t b w ht := by
    simp only [boolSyntax, sem] at w ht ⊢
    rw [← evalB_denB t w ht, evalB_eq_some, eval_eq_ev w]; rfl
  den_BitVec := by lang_den
  den_Add := by lang_den
  den_Sub := by lang_den
  den_Mul := by lang_den
  den_Div := by lang_den
  den_Rem := by lang_den
  den_Mod := by lang_den
  den_BitAnd := by lang_den
  den_BitOr := by lang_den
  den_BitXor := by lang_den
  den_Shl := by lang_den
  den_LShr := by lang_den
  den_AShr := by lang_den
  den_BvConcat ρ n a b t := by
    lang_den
    rcases a with ⟨_, ta⟩; rcases b with ⟨_, tb⟩
    cases ta <;> cases tb <;> rfl
  den_Neg := by lang_den
  den_BvNot := by lang_den
  den_BvOfBool := by lang_den
  den_BvExtend ρ n s k a t := by
    lang_den
    rcases a with ⟨_, ta⟩; cases ta <;> rfl
  den_BvExtract ρ n i j a t := by
    lang_den
    rcases a with ⟨_, ta⟩; cases ta <;> rfl
  den_Ite ρ n g a b t := by
    lang_den
    rcases denB FS ρ g with _ | _ | _ <;> rfl
  denB_Bool := by lang_den
  denB_Not := by lang_den
  denB_And := by lang_den
  denB_Or := by lang_den
  denB_Ite ρ g a b t := by
    lang_den
    rcases denB FS ρ g with _ | _ | _ <;> rfl
  denB_Eq ρ a b t := by
    lang_den
    rcases a with ⟨_, ta⟩; cases ta <;> simp [sem]
  denB_Lt ρ s a b t := by
    lang_den
    rcases a with ⟨_, ta⟩; cases ta <;> rfl
  denB_Leq ρ s a b t := by
    lang_den
    rcases a with ⟨_, ta⟩; cases ta <;> rfl
  denB_AddOvf ρ s a b t := by
    lang_den
    rcases a with ⟨_, ta⟩; cases ta <;> rfl
  denB_SubOvf ρ s a b t := by
    lang_den
    rcases a with ⟨_, ta⟩; cases ta <;> rfl
  denB_MulOvf ρ s a b t := by
    lang_den
    rcases a with ⟨_, ta⟩; cases ta <;> rfl
  size_of_ty_TBitVector _ := rfl
  size_of_ty_TLoc _ := rfl
  mk_masked_eq _ _ := rfl
  mk_bv_eq _ _ := rfl
  bv_zero_eq _ := rfl
  bv_one_eq _ := rfl
  lit_add_eq _ _ _ _ := rfl
  lit_sub_eq _ _ _ _ := rfl
  lit_mul_eq _ _ _ _ := rfl
  lit_neg_eq _ _ := rfl
  lit_udiv_eq _ _ _ _ := rfl
  lit_sdiv_eq _ _ _ _ := rfl
  lit_and_eq _ _ a b := by
    simp only [bitvecSyntax, lit_and, BitvecMod.Prim.lit_and, BitvecMod.Prim.masked, masked]
    cases a <;> cases b <;> rfl
  lit_or_eq _ _ a b := by
    simp only [bitvecSyntax, lit_or, BitvecMod.Prim.lit_or, BitvecMod.Prim.masked, masked]
    cases a <;> cases b <;> rfl
  lit_xor_eq _ _ a b := by
    simp only [bitvecSyntax, lit_xor, BitvecMod.Prim.lit_xor, BitvecMod.Prim.masked, masked]
    cases a <;> cases b <;> rfl
  lit_not_eq _ _ := rfl
  lit_shl_eq _ _ _ _ := rfl
  lit_lshr_eq _ _ _ _ := rfl
  lit_ashr_eq _ _ _ _ := rfl
  lit_urem_eq _ _ _ _ := rfl
  lit_srem_eq _ _ _ _ := rfl
  lit_smod_eq _ _ _ _ := rfl
  lit_extract_eq _ _ _ _ := rfl
  lit_zext_eq _ _ _ := rfl
  lit_sext_eq _ _ _ := rfl
  lit_concat_eq _ _ a b := by
    simp only [bitvecSyntax, lit_concat, BitvecMod.Prim.lit_concat, z_lsl, BitvecMod.Prim.z_lsl]
    generalize a * 2 ^ _ = c
    cases c <;> cases b <;> rfl
  signed_extract_eq _ _ _ := rfl
  popcount_eq z := by
    simp only [bitvecSyntax, popcount, BitvecMod.Prim.popcount, Lang.popcountNat_eq]
  log2_eq _ := rfl
  tdiv_eq _ _ := rfl
  trem_eq _ _ := rfl
  divisible_eq _ _ := rfl
  z_land_eq a b := by cases a <;> cases b <;> rfl
  z_lsl_eq _ _ := rfl
  nonzero_ev ρ t n x hs w e := hs FS ρ n x (by rw [eval_eq_ev w]; exact e)
  zero_ev ρ t n x hs w e := hs FS ρ n x (by rw [eval_eq_ev w]; exact e)
  nonzero_BitVec z t h := by
    intro FS' ρ n x e
    simp only [bitvecSyntax, modBase] at e h
    have w := eval_WT e
    obtain ⟨k, hk, ht, h0, h1⟩ := WT_bitVec.1 w
    rw [eval_bitVec' w ht] at e
    simp only [Option.some.injEq, Val.bv.injEq] at e
    obtain ⟨rfl, e⟩ := e
    cases e
    exact h k (by simp [ht])
  den_msb ρ v n x w ht e := Kanon.Lib.den_msb w ht e

@[simp] theorem bitvecSem_vbv (n : Nat) (x : BitVec n) :
    BitvecMod.Sem.vbv (bitvecSyntax FS) n x = Val.bv n x := rfl
@[simp] theorem bitvecSem_vbv' : BitvecMod.Sem.vbv (bitvecSyntax FS) = Val.bv := rfl

end Kanon
