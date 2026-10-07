import BitvecMod.Proofs.ArithLib
import BitvecMod.Statements.Comm
import BitvecMod.Statements.Bitvec.add
import BitvecMod.Statements.Bitvec.and_
import BitvecMod.Statements.Bitvec.mul
import BitvecMod.Statements.Bitvec.neg
import BitvecMod.Statements.Bitvec.not_
import BitvecMod.Statements.Bitvec.or_
import BitvecMod.Statements.Bitvec.sub
import BitvecMod.Proofs.IteLib

/-!
# The proofs of the arithmetic arms of the bitvec module

The arms of `Bitvec.add`, `sub`, `mul`, `neg`, `not_`, `and_`, `or_`, `xor`,
`of_bool`, `to_bool`, `not_bool` and of the overflow functions are proved by
`bv_arith` (`Proofs/ArithLib.lean`), the foldings of constants by `bv_fold`;
`Bitvec.or_.r_extend_shl` by hand, on its bits, `Bitvec.and_.r_ites` by hand, by cases on its
guards, `Bitvec.add.r_default` by the bounds of its terms (`add_no_wrap`),
`Bitvec.sub.r_add_const.swap` from its main arm, and the arms that distribute an
operation over conditionals by `bv_ite_arm` (`Proofs/IteLib.lean`).
-/

namespace BitvecMod

@[kanon_arm] theorem Bitvec.add.r_ite.main.proof : Bitvec.add.r_ite.main.Stmt := by bv_ite_arm
@[kanon_arm] theorem Bitvec.sub.r_ite_ite.main.proof : Bitvec.sub.r_ite_ite.main.Stmt := by
  bv_ite_arm
@[kanon_arm] theorem Bitvec.sub.r_ite_l.main.proof : Bitvec.sub.r_ite_l.main.Stmt := by bv_ite_arm
@[kanon_arm] theorem Bitvec.sub.r_ite_r.main.proof : Bitvec.sub.r_ite_r.main.Stmt := by bv_ite_arm
@[kanon_arm] theorem Bitvec.mul.r_ite.main.proof : Bitvec.mul.r_ite.main.Stmt := by bv_ite_arm
@[kanon_arm] theorem Bitvec.neg.r_ite.main.proof : Bitvec.neg.r_ite.main.Stmt := by bv_ite_arm
@[kanon_arm] theorem Bitvec.not_.r_ite.main.proof : Bitvec.not_.r_ite.main.Stmt := by bv_ite_arm
@[kanon_arm] theorem Bitvec.and_.r_ite.main.proof : Bitvec.and_.r_ite.main.Stmt := by bv_ite_arm

/-- The conjunction of two conditionals with a zero branch, as the conditional of the
conjunction of their guards: by the typing and values of the nodes, by cases on the guards
(without `bv_arith`, whose case splits on the values of the six atoms are slow). -/
@[kanon_arm] theorem Bitvec.and_.r_ites.main.proof : Bitvec.and_.r_ites.main.Stmt := by
  intro S _ _ _ _ _ _ O hO b1 l1 _ t5 t6 b2 l2 _ t11 t12 _
  kanon_rule_lift
  refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;>
    simp only [WT_mk, KanonBool.WT_mk, Node.wt, KanonBool.Node.wt, Node.All, KanonBool.Node.All,
      ty_mk, KanonBool.ty_mk, bv_wf] at w <;>
    obtain ⟨⟨⟨N, hN, h6⟩, rfl, -⟩, ⟨⟨hb1, rfl, h6'⟩, wb1, wl1, -⟩,
      ⟨hb2, h11, h12⟩, wb2, wl2, -⟩ := w <;>
    subst h6' <;> subst h11
  · simp only [bv_zero, WT_mk, Node.wt, Node.All, ty_mk, bv_wf, KanonBool.WT_mk, KanonBool.Node.wt,
      KanonBool.Node.All, KanonBool.ty_mk, h6, hb1, hb2, wb1, wb2, wl1, wl2,
      size_of_ty_TBitVector, true_and, and_true]
    exact ⟨⟨⟨N, hN, rfl⟩, h12 ▸ h6⟩, ⟨N, hN, rfl⟩,
      fun n h => ⟨Int.le_refl 0, Int.pow_pos (by decide)⟩⟩
  · have hw : Values.width (D := S.toDom) (S.ty l1) = N.toNat := by
      rw [h6]; exact width_sort ρ (.inl rfl) hN
    have hw' : Values.width (D := S.toDom) (sort (.TBitVector N)) = N.toNat :=
      width_sort ρ (.inl rfl) hN
    simp only [ev_mk, KanonBool.ev_mk, Node.map, KanonBool.Node.map, Node.eval,
      KanonBool.Node.eval, KanonBool.ty_mk, bv_zero, ty_mk, h6, size_of_ty_TBitVector] at e ⊢
    rw [← h12, ← h6, hw] at e
    rw [← h6, hw]
    rcases KanonBool.ev_cases (ρ := ρ) wb1 hb1 with h1 | ⟨_, h1, rfl | rfl⟩ <;>
    rcases KanonBool.ev_cases (ρ := ρ) wb2 hb2 with h2 | ⟨_, h2, rfl | rfl⟩ <;>
    simp only [h1, h2, KanonBool.pite, KanonBool.pand, Kanon.Embed.inj_eq_iff, Option.some.injEq,
      Bool.true_eq_false, Bool.false_eq_true, or_self, or_true, true_or, and_self, ite_true,
      ite_false, ofBV_some, asBV_bv, asBV_none, binOp_none_l, binOp_none_r, ofBV_none, reduceCtorEq]
      at e ⊢
    all_goals (try rw [hw'])
    all_goals first
      | exact e
      | ((try generalize asBV N.toNat (S.ev ρ l1) = o1 at e)
         (try generalize asBV N.toNat (S.ev ρ l2) = o2 at e)
         rcases o1 with _ | x1 <;> rcases o2 with _ | x2 <;>
           simp only [binOp_none_l, binOp_none_r, binOp_some, ofBV_none, ofBV_some, reduceCtorEq,
             Option.some.injEq, ofInt_zero', BitVec.and_zero, BitVec.zero_and] at e ⊢ <;>
           exact e)

section
variable {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [Lang S] [KanonBool.Typed S]
  [CoreMod.Typed S] [Typed S]

omit [KanonBool.Typed S] [CoreMod.Typed S] in
/-- A sum is checked unsigned when the bounds of its terms (`unsigned_ub`) keep it in range
(`Bitvec.no_wrap`). -/
theorem add_no_wrap {c : CoreMod.Checked} {v1 v2 : S.Term} :
    S.Refines (mk (.Add c v1 v2) (S.ty v1))
      (mk (.Add (Bitvec.no_wrap c v1 v2) v1 v2) (S.ty v1)) := by
  refine Kanon.Sem.Refines.intro (fun w => ⟨?_, by simp only [ty_mk]⟩) (fun ρ v w _ e => ?_)
  · simpa only [WT_mk, Node.wt, Node.All] using w
  · unfold Bitvec.no_wrap
    split
    · rename_i hc
      simp only [WT_mk, Node.wt, Node.All] at w
      obtain ⟨⟨⟨N, hN, h1⟩, h2, -⟩, w1, w2⟩ := w
      obtain ⟨n, rfl⟩ : ∃ n : Nat, N = n := ⟨N.toNat, by omega⟩
      have h2' := h2.trans h1
      have hw : Values.width (D := S.toDom) (S.ty v1) = n := by
        rw [h1]; simpa using width_sort (S := S) ρ (.inl rfl) hN
      rcases ev_cases (ρ := ρ) w1 h1 with hv1 | ⟨_, hv1, -, x, rfl⟩
      · simp [ev_mk, Node.eval, Node.map, hv1] at e
      rcases ev_cases (ρ := ρ) w2 h2' with hv2 | ⟨_, hv2, -, y, rfl⟩
      · simp [ev_mk, Node.eval, Node.map, hv2] at e
      replace hv1 : S.ev ρ v1 = some (bv n x) := hv1
      replace hv2 : S.ev ρ v2 = some (bv n y) := hv2
      have b1 := msb_bound_int ρ w1 h1 n x hv1
      have b2 := msb_bound_int ρ w2 h2' n y hv2
      have hu : x.uaddOverflow y = false := by
        simp only [Bitvec.is_bv, Bool.and_eq_true, decide_eq_true_eq, Bitvec.unsigned_ub,
          Bitvec.size, h1, size_of_ty_TBitVector, z_lsl_one, Int.toNat_natCast] at hc
        rw [uadd_ok]
        have : ((2 ^ (n : Int).toNat : Nat) : Int) = 2 ^ n := by simp
        omega
      simp only [ev_mk, Node.eval, Node.map, hv1, hv2] at e ⊢
      rw [hw] at e ⊢
      simpa only [asBV_bv, ckOp_some, hu, Bool.and_false, Bool.or_false] using e
    · exact e
end

/-- `add.r_default`: the sum, checked unsigned when the bounds of its terms keep it in range, its
terms ordered (`add_no_wrap` and `Add.comm`). -/
@[kanon_arm] theorem Bitvec.add.r_default.main.proof : Bitvec.add.r_default.main.Stmt := by
  intro S _ _ _ _ _ _ O hO checked v1 v2
  simp only [Bitvec.add.spec]
  split
  · exact add_no_wrap
  · exact Kanon.Sem.Refines.trans add_no_wrap (Add.comm.proof ..)

/-! The foldings of constants, by `bv_fold` (`Proofs/ArithLib.lean`). -/

@[kanon_arm] theorem Bitvec.add.r_add_const.main.proof : Bitvec.add.r_add_const.main.Stmt := by
  bv_fold
@[kanon_arm] theorem Bitvec.add.r_sub_const_l.main.proof : Bitvec.add.r_sub_const_l.main.Stmt := by
  bv_fold
@[kanon_arm] theorem Bitvec.add.r_sub_const_r.main.proof : Bitvec.add.r_sub_const_r.main.Stmt := by
  bv_fold
@[kanon_arm] theorem Bitvec.sub.r_sub_const_l.main.proof : Bitvec.sub.r_sub_const_l.main.Stmt := by
  bv_fold
@[kanon_arm] theorem Bitvec.sub.r_sub_const_r.main.proof : Bitvec.sub.r_sub_const_r.main.Stmt := by
  bv_fold
@[kanon_arm] theorem Bitvec.sub.r_const_add.main.proof : Bitvec.sub.r_const_add.main.Stmt := by
  bv_fold
@[kanon_arm] theorem Bitvec.sub.r_add_const.main.proof : Bitvec.sub.r_add_const.main.Stmt := by
  bv_fold

/-- `sub.r_add_const` with the sum swapped, from the main arm by `Add.comm` (the generated
proof re-runs `bv_arith`, as the right-hand side mentions the sum). -/
@[kanon_arm] theorem Bitvec.sub.r_add_const.swap.proof : Bitvec.sub.r_add_const.swap.Stmt := by
  intro S _ _ _ _ _ _ O hO checked c l k1 t__4 t__6 k2 t__9
  have hm := Bitvec.sub.r_add_const.main.proof O hO checked c k1 t__4 l t__6 k2 t__9
  simp only [Bitvec.size, ty_mk] at hm ⊢
  refine Kanon.Sem.Refines.trans ?_ hm
  have := Add.comm.proof c l (mk (.BitVec k1) t__4) t__6
  simp only [Bitvec.sub.spec, ty_mk]
  kanon_congr

/-- The bits of `zext base ||| (zext tail << size base)` are those of the
concatenation of `tail` (or of its low bits) and `base`, of the widths that the
typing gives (equal up to arithmetic, `bv_eq_cast`). -/
@[kanon_arm] theorem Bitvec.or_.r_extend_shl.main.proof : Bitvec.or_.r_extend_shl.main.Stmt := by
  (try intro _)
  intros
  kanon_rule_lift
  all_goals kanon_on_refines (
    (try dsimp only)
    bv_split_ifs
    all_goals (try kanon_lift_body)
    all_goals (try simp only [kanon_spec, kanon_body]))
  all_goals kanon_on_refines (
    refine Kanon.Sem.Refines.intro ?_ ?_
    · bv_arith_wt)
  all_goals bv_arith_sem_core
  all_goals (try simp only [withW_none, asBV_none, binOp_none_l, binOp_none_r, Option.map_none,
    reduceCtorEq] at e)
  all_goals (try simp (disch := omega) only [Arith.asBV_bv_cast, binOp_some, Option.map_some,
    Option.some.injEq] at e)
  all_goals (try subst e)
  all_goals (try (refine ⟨_, _, ⟨rfl, HEq.rfl⟩, ?_⟩))
  all_goals (try simp only [asBV_bv, Option.map_some, Option.bind_some, Option.some.injEq])
  all_goals (try (refine Arith.bv_eq_cast (by omega) ?_))
  all_goals (apply BitVec.eq_of_getLsbD_eq; intro i hi)
  all_goals (simp only [BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_or,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, BitVec.shiftLeft_eq', BitVec.getLsbD_extractLsb',
    BitVec.toNat_cast])
  all_goals (simp (disch := omega) only [Arith.toNat_ofInt_natCast_of_le])
  all_goals (split <;> rename_i hc)
  all_goals (try simp (disch := omega) only [BitVec.getLsbD_of_ge, decide_eq_true, decide_eq_false,
    Nat.zero_add, Bool.true_and, Bool.and_true, Bool.not_true, Bool.not_false, Bool.false_and,
    Bool.and_false, Bool.or_false, Bool.false_or])

end BitvecMod
