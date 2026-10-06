import FloatMod.Lib.Rule
import FloatMod.Statements.Bool.eq

/-! The equality of two float literals: their values are equal exactly when
the literals are, as they are well formed (`Sem.vfloat_inj`). -/

namespace FloatMod

open Classical Kanon Kanon.Sem CoreMod Lib

@[kanon_arm] theorem Bool.eq.r_floats.main.proof : Bool.eq.r_floats.main.Stmt := by
  intro S _ _ B LBool LCore LBitvec L _ _ _ _ O hO f1 t1 f2 t2
  have hr : LBool.bool_of_bool (L.float_f_bits_equal f1 f2) =
      B.node (LBool.BoolK (decide (f1 = f2))) LBool.TBool := by
    rw [LBool.bool_of_bool_eq, Sem.f_bits_equal_eq, Prim.f_bits_equal]
    by_cases h : f1 = f2 <;> simp [h, KanonBool.Sem.v_true_eq, KanonBool.Sem.v_false_eq]
  rw [hr, KanonBool.Bool.eq.spec]
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> rw [LBool.WT_Eq] at w
  · exact ⟨(LBool.WT_Bool _ _).2 rfl, by rw [B.ty_node, B.ty_node]⟩
  · obtain ⟨⟨h2, -⟩, w1, w2⟩ := w
    obtain ⟨rfl, wf1⟩ := WT_lit.1 w1
    obtain ⟨rfl, wf2⟩ := WT_lit.1 w2
    rw [B.ty_node, B.ty_node] at h2
    have hp := L.TFloat_inj _ _ h2
    rw [KanonBool.Sem.ev_Eq, Sem.ev_Float, Sem.ev_Float, KanonBool.peq_some] at e
    rw [KanonBool.Sem.ev_Bool, ← e]
    congr 2
    simp only [decide_eq_decide]
    constructor
    · rintro rfl; rfl
    · intro h
      have hv := Sem.vfloat_inj _ _ _ _ h
      obtain ⟨p1, b1⟩ := f1
      obtain ⟨p2, b2⟩ := f2
      simp only [CoreMod.Float.WF] at wf1 wf2 hp
      subst hp
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and, CoreMod.Float.val] at hv
      have hb := congrArg BitVec.toNat hv
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt wf1, Nat.mod_eq_of_lt wf2] at hb
      rw [hb]

end FloatMod
