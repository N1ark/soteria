import FloatMod.Statements.Comm
import FloatMod.Statements.Bool.eq
import FloatMod.Statements.Bool.sure_neq
import FloatMod.Statements.Float.abs
import FloatMod.Statements.Float.add
import FloatMod.Statements.Float.cast
import FloatMod.Statements.Float.div
import FloatMod.Statements.Float.eq
import FloatMod.Statements.Float.fma
import FloatMod.Statements.Float.fmod
import FloatMod.Statements.Float.fmod_of_rem
import FloatMod.Statements.Float.is_floatclass
import FloatMod.Statements.Float.is_negative
import FloatMod.Statements.Float.is_positive
import FloatMod.Statements.Float.leq
import FloatMod.Statements.Float.lt
import FloatMod.Statements.Float.max
import FloatMod.Statements.Float.min
import FloatMod.Statements.Float.mul
import FloatMod.Statements.Float.neg
import FloatMod.Statements.Float.of_float
import FloatMod.Statements.Float.rem
import FloatMod.Statements.Float.round
import FloatMod.Statements.Float.sqrt
import FloatMod.Statements.Float.sub
import FloatMod.Statements.Float.to_float
import FloatMod.Statements.Float.to_float_bits

namespace FloatMod

open Classical Kanon CoreMod

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section

variable {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [BitvecMod.Lang S] [Lang S]

theorem wt_lit {f : CoreMod.Float} {t : S.Ty} :
    S.WT (mk (.Float f) t) ↔ t = sort (.TFloat f.prec) ∧ f.WF := by
  rw [WT_mk]; simp [Node.wt, float_wf, Node.All]

theorem ev_lit (ρ : S.Env) (f : CoreMod.Float) (t : S.Ty) :
    S.ev ρ (mk (.Float f) t) = some (vlit f) := by
  rw [ev_mk]; rfl

/-- A binary operation that `lit` computes on literals. -/
theorem lits_bin {op : (p : Fp) → FBits p → FBits p → FBits p} {lit}
    (hc : Bin (S := S) op lit) (C : S.Term → S.Term → Node S.Term)
    (hwt : ∀ a b t, S.WT (mk (C a b) t) → S.WT a ∧ S.WT b ∧ S.ty b = S.ty a ∧ t = S.ty a)
    (hev : ∀ ρ a b t, S.ev ρ (mk (C a b) t) =
      fBin (fun p x y => some (vf p (op p x y))) (S.ev ρ a) (S.ev ρ b))
    (f1 f2 : CoreMod.Float) (t1 t2 : S.Ty) :
    S.Refines (mk (C (mk (.Float f1) t1) (mk (.Float f2) t2)) (S.ty (mk (.Float f1) t1)))
      (mk (.Float (lit f1 f2)) (sort (.TFloat (f_prec (lit f1 f2))))) := by
  refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;>
    obtain ⟨w1, w2, ht, -⟩ := hwt _ _ _ w <;>
    obtain ⟨rfl, wf1⟩ := wt_lit.1 w1 <;> obtain ⟨rfl, wf2⟩ := wt_lit.1 w2 <;>
    simp only [ty_mk, sort_inj_iff, Srt.TFloat.injEq] at ht <;>
    obtain ⟨hp, hwf, hv⟩ := hc f1 f2 wf1 wf2 ht
  · exact ⟨wt_lit.2 ⟨rfl, hwf⟩, by simp [hp]⟩
  · rw [hev, ev_lit, ev_lit] at e
    rw [ev_lit, hv, ← e]
    obtain ⟨p1, b1⟩ := f1; obtain ⟨p2, b2⟩ := f2
    simp only at ht; subst ht
    simp [vlit]

end

local macro "float_bin_wt" : tactic => `(tactic| (
  intro a b t w
  rw [WT_mk] at w
  obtain ⟨⟨-, h2, h3⟩, w1, w2⟩ := w
  exact ⟨w1, w2, h2, h3⟩))

@[kanon_arm] theorem Float.add.r_lits.main.proof : Float.add.r_lits.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO f1 t1 f2 t2
  exact lits_bin hO.float_orc.add (fun a b => .FAdd a b) (by float_bin_wt) (fun _ _ _ _ => by
    rw [ev_mk]; rfl) f1 f2 t1 t2

@[kanon_arm] theorem Float.sub.r_lits.main.proof : Float.sub.r_lits.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO f1 t1 f2 t2
  exact lits_bin hO.float_orc.sub (fun a b => .FSub a b) (by float_bin_wt) (fun _ _ _ _ => by
    rw [ev_mk]; rfl) f1 f2 t1 t2

@[kanon_arm] theorem Float.mul.r_lits.main.proof : Float.mul.r_lits.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO f1 t1 f2 t2
  exact lits_bin hO.float_orc.mul (fun a b => .FMul a b) (by float_bin_wt) (fun _ _ _ _ => by
    rw [ev_mk]; rfl) f1 f2 t1 t2

@[kanon_arm] theorem Float.div.r_lits.main.proof : Float.div.r_lits.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO f1 t1 f2 t2
  exact lits_bin hO.float_orc.div (fun a b => .FDiv a b) (by float_bin_wt) (fun _ _ _ _ => by
    rw [ev_mk]; rfl) f1 f2 t1 t2

@[kanon_arm] theorem Float.rem.r_lits.main.proof : Float.rem.r_lits.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO f1 t1 f2 t2
  exact lits_bin hO.float_orc.rem (fun a b => .FRem a b) (by float_bin_wt) (fun _ _ _ _ => by
    rw [ev_mk]; rfl) f1 f2 t1 t2

@[kanon_arm] theorem Float.min.r_lits.main.proof : Float.min.r_lits.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO f1 t1 f2 t2
  exact lits_bin hO.float_orc.min (fun a b => .FMin a b) (by float_bin_wt) (fun _ _ _ _ => by
    rw [ev_mk]; rfl) f1 f2 t1 t2

@[kanon_arm] theorem Float.max.r_lits.main.proof : Float.max.r_lits.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO f1 t1 f2 t2
  exact lits_bin hO.float_orc.max (fun a b => .FMax a b) (by float_bin_wt) (fun _ _ _ _ => by
    rw [ev_mk]; rfl) f1 f2 t1 t2

section

variable {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [BitvecMod.Lang S] [Lang S]

theorem fBin_eq_some {f : (p : Fp) → FBits p → FBits p → Option S.Val} {a b : Option S.Val}
    {v : S.Val} : fBin f a b = some v ↔
      ∃ p x y, a = some (vf p x) ∧ b = some (vf p y) ∧ f p x y = some v := by
  simp only [fBin, withF_eq_some, Option.bind_eq_some_iff, asF_eq_some]
  constructor
  · rintro ⟨p, x, ha, y, hb, h⟩; exact ⟨p, x, y, ha, hb, h⟩
  · rintro ⟨p, x, y, ha, hb, h⟩; exact ⟨p, x, ha, y, hb, h⟩

/-- Well-formed literals have the same value exactly when they are equal. -/
theorem vlit_inj {f1 f2 : CoreMod.Float} (h1 : f1.WF) (h2 : f2.WF)
    (h : vlit (D := S.toDom) f1 = vlit f2) : f1 = f2 := by
  obtain ⟨p1, b1⟩ := f1; obtain ⟨p2, b2⟩ := f2
  simp only [vlit, vf, Embed.inj_eq_iff, Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  simp only [CoreMod.Float.WF] at h1 h2
  have hb := congrArg BitVec.toNat (eq_of_heq h)
  simp only [CoreMod.Float.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hb
  rw [hb]

theorem wt_bool {b : Bool} {t : S.Ty} :
    S.WT (KanonBool.mk (.Bool b) t) ↔ t = KanonBool.sort .TBool := by
  rw [KanonBool.WT_mk]; simp [KanonBool.Node.wt, KanonBool.Node.All]

theorem ev_bool (ρ : S.Env) (b : Bool) (t : S.Ty) :
    S.ev ρ (KanonBool.mk (.Bool b) t) = some (KanonBool.Values.vbool.inj b) := by
  rw [KanonBool.ev_mk]; rfl

/-- A comparison of float literals. -/
theorem cmp_lits {c : ∀ {p : Fp}, FBits p → FBits p → Bool} (C : S.Term → S.Term → Node S.Term)
    (hwt : ∀ a b t, S.WT (mk (C a b) t) → S.WT a ∧ S.WT b ∧ S.ty b = S.ty a ∧
      t = KanonBool.sort .TBool)
    (hev : ∀ ρ a b t, S.ev ρ (mk (C a b) t) =
      fBin (fun _ x y => some (KanonBool.Values.vbool.inj (c x y))) (S.ev ρ a) (S.ev ρ b))
    (f1 f2 : CoreMod.Float) (t1 t2 t : S.Ty) :
    S.Refines (mk (C (mk (.Float f1) t1) (mk (.Float f2) t2)) t)
      (KanonBool.mk (.Bool (CoreMod.Float.cmp c f1 f2)) (KanonBool.sort .TBool)) := by
  refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;>
    obtain ⟨w1, w2, ht, rfl⟩ := hwt _ _ _ w <;>
    obtain ⟨rfl, -⟩ := wt_lit.1 w1 <;> obtain ⟨rfl, -⟩ := wt_lit.1 w2 <;>
    simp only [ty_mk, sort_inj_iff, Srt.TFloat.injEq] at ht
  · exact ⟨wt_bool.2 rfl, by simp⟩
  · rw [hev, ev_lit, ev_lit] at e
    rw [ev_bool, ← e]
    obtain ⟨p1, b1⟩ := f1; obtain ⟨p2, b2⟩ := f2
    simp only at ht; subst ht
    simp [vlit, CoreMod.Float.cmp]

/-- A predicate on a float literal. -/
theorem pred_lit {c : ∀ {p : Fp}, FBits p → Bool} (C : S.Term → Node S.Term)
    (hwt : ∀ a t, S.WT (mk (C a) t) → S.WT a ∧ t = KanonBool.sort .TBool)
    (hev : ∀ ρ a t, S.ev ρ (mk (C a) t) =
      withF (S.ev ρ a) (fun _ x => some (KanonBool.Values.vbool.inj (c x))))
    (f : CoreMod.Float) (t1 t : S.Ty) :
    S.Refines (mk (C (mk (.Float f) t1)) t)
      (KanonBool.mk (.Bool (c f.val)) (KanonBool.sort .TBool)) := by
  refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;>
    obtain ⟨-, rfl⟩ := hwt _ _ w
  · exact ⟨wt_bool.2 rfl, by simp⟩
  · rw [hev, ev_lit] at e
    rw [ev_bool, ← e]
    simp [vlit]

end

local macro "float_cmp_wt" : tactic => `(tactic| (
  intro a b t w
  rw [WT_mk] at w
  obtain ⟨⟨-, h2, h3⟩, w1, w2⟩ := w
  exact ⟨w1, w2, h2, h3⟩))

local macro "float_pred_wt" : tactic => `(tactic| (
  intro a t w
  rw [WT_mk] at w
  obtain ⟨⟨-, h2⟩, w1⟩ := w
  exact ⟨w1, h2⟩))

@[kanon_arm] theorem Float.eq.r_lits.main.proof : Float.eq.r_lits.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO f1 t1 f2 t2
  exact cmp_lits (c := fun x y => x.eq y) (fun a b => .FEq a b) (by float_cmp_wt)
    (fun _ _ _ _ => by rw [ev_mk]; rfl) f1 f2 t1 t2 _

@[kanon_arm] theorem Float.lt.r_lits.main.proof : Float.lt.r_lits.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO f1 t1 f2 t2
  exact cmp_lits (c := fun x y => x.lt y) (fun a b => .FLt a b) (by float_cmp_wt)
    (fun _ _ _ _ => by rw [ev_mk]; rfl) f1 f2 t1 t2 _

@[kanon_arm] theorem Float.leq.r_lits.main.proof : Float.leq.r_lits.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO f1 t1 f2 t2
  exact cmp_lits (c := fun x y => x.le y) (fun a b => .FLeq a b) (by float_cmp_wt)
    (fun _ _ _ _ => by rw [ev_mk]; rfl) f1 f2 t1 t2 _

@[kanon_arm] theorem Float.is_floatclass.r_lit.main.proof : Float.is_floatclass.r_lit.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO fc f t
  exact pred_lit (c := fun x => x.isClass fc) (fun a => .FIs fc a) (by float_pred_wt)
    (fun _ _ _ => by rw [ev_mk]; rfl) f t _

@[kanon_arm] theorem Float.is_negative.r_lit.main.proof : Float.is_negative.r_lit.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO f t
  exact pred_lit (c := fun x => x.isNeg) (fun a => .FIsNeg a) (by float_pred_wt)
    (fun _ _ _ => by rw [ev_mk]; rfl) f t _

@[kanon_arm] theorem Float.is_positive.r_lit.main.proof : Float.is_positive.r_lit.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO f t
  exact pred_lit (c := fun x => x.isPos) (fun a => .FIsPos a) (by float_pred_wt)
    (fun _ _ _ => by rw [ev_mk]; rfl) f t _

section

variable {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [BitvecMod.Lang S] [Lang S]

theorem fbits_eq_comm {p : Fp} (x y : FBits p) : x.eq y = y.eq x := by
  unfold FBits.eq
  by_cases hxy : x = y
  · subst hxy; rfl
  · have h1 : (x == y) = false := by simp [hxy]
    have h2 : (y == x) = false := by simp [Ne.symm hxy]
    rw [h1, h2]
    cases x.isNaN <;> cases y.isNaN <;> cases x.isZero <;> cases y.isZero <;> rfl

theorem fbits_abs_abs {p : Fp} (x : FBits p) : x.abs.abs = x.abs := by
  simp only [FBits.abs, BitVec.and_assoc, BitVec.and_self]

theorem fbits_neg_neg {p : Fp} (x : FBits p) : x.neg.neg = x := by
  simp only [FBits.neg, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem fUn_fUn (g h : (p : Fp) → FBits p → FBits p) (a : Option S.Val) :
    fUn g (fUn h a) = fUn (fun p x => g p (h p x)) a := by
  rcases a with _ | u
  · rfl
  · rcases hu : (Values.vfloat (D := S.toDom)).proj u with _ | ⟨p, x⟩
    · simp [fUn, withF, hu]
    · rw [Embed.proj_eq_some_iff] at hu; subst hu; simp [fUn]

/-- A unary operation, at the precision of its operand, on a float literal. -/
theorem un_lits {op : (p : Fp) → FBits p → FBits p} {lit}
    (hc : Un (S := S) op lit) (C : S.Term → Node S.Term)
    (hwt : ∀ a t, S.WT (mk (C a) t) → S.WT a)
    (hev : ∀ ρ a t, S.ev ρ (mk (C a) t) = fUn op (S.ev ρ a))
    (f : CoreMod.Float) (t1 : S.Ty) :
    S.Refines (mk (C (mk (.Float f) t1)) (S.ty (mk (.Float f) t1)))
      (mk (.Float (lit f)) (sort (.TFloat (f_prec (lit f))))) := by
  refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;>
    obtain ⟨rfl, wf⟩ := wt_lit.1 (hwt _ _ w) <;>
    obtain ⟨hp, hwf, hv⟩ := hc f wf
  · exact ⟨wt_lit.2 ⟨rfl, hwf⟩, by simp [hp]⟩
  · rw [hev, ev_lit] at e
    rw [ev_lit, hv, ← e]
    simp [vlit, fUn]

/-- A unary operation on bits computed on the literal. -/
theorem un_bits (op : (p : Fp) → FBits p → FBits p) :
    Un (S := S) op (fun f => ⟨f.prec, (op f.prec f.val).toNat⟩) := by
  intro f _
  refine ⟨rfl, BitVec.isLt _, ?_⟩
  simp [vlit, CoreMod.Float.val]

end

local macro "float_un_wt" : tactic => `(tactic| (
  intro a t w
  rw [WT_mk] at w
  exact w.2))

@[kanon_arm] theorem FEq.comm.proof : FEq.comm.Stmt := by
  intro S _ _ _ _ _ _ _ _ a b t
  refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · rw [WT_mk] at w ⊢
    obtain ⟨⟨⟨p, hp⟩, h2, h3⟩, wa, wb⟩ := w
    exact ⟨⟨⟨⟨p, h2.trans hp⟩, h2.symm, h3⟩, wb, wa⟩, by simp⟩
  · rw [ev_mk] at e ⊢
    simp only [Node.map, Node.eval, fCmp] at e ⊢
    obtain ⟨p, x, y, ha, hb, h⟩ := fBin_eq_some.1 e
    exact fBin_eq_some.2 ⟨p, y, x, hb, ha, by rw [← h, fbits_eq_comm]⟩

@[kanon_arm] theorem Bool.eq.r_floats.main.proof : Bool.eq.r_floats.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO f1 t1 f2 t2
  have hr : KanonBool.Bool.of_bool (S := S) (f_bits_equal f1 f2) =
      KanonBool.mk (.Bool (decide (f1 = f2))) (KanonBool.sort .TBool) := by
    by_cases h : f1 = f2 <;>
      simp [h, KanonBool.Bool.of_bool, f_bits_equal, KanonBool.v_true, KanonBool.v_false]
  rw [hr, KanonBool.Bool.eq.spec]
  refine Kanon.Sem.Refines.intro (fun _ => ⟨wt_bool.2 rfl, by simp⟩) (fun ρ v w _ e => ?_)
  rw [KanonBool.WT_mk] at w
  obtain ⟨-, w1, w2⟩ := w
  obtain ⟨-, wf1⟩ := wt_lit.1 w1
  obtain ⟨-, wf2⟩ := wt_lit.1 w2
  rw [KanonBool.ev_mk] at e
  simp only [KanonBool.Node.map, KanonBool.Node.eval, ev_lit, KanonBool.peq] at e
  rw [ev_bool, ← e]
  have : vlit (D := S.toDom) f1 = vlit f2 ↔ f1 = f2 := ⟨vlit_inj wf1 wf2, by rintro rfl; rfl⟩
  simp only [this]

@[kanon_arm] theorem Bool.sure_neq.c1.proof : Bool.sure_neq.c1.Stmt := by
  intro S _ _ _ _ _ _ _ _ a b r h
  simp only [Bool.sure_neq.c1] at h
  split at h
  · rename_i fa fb ha hb
    cases h
    intro hr wa wb _ ρ u ea eb
    obtain ⟨ta, rfl⟩ := Kanon.NodeEmbed.exists_of_proj _ ha
    obtain ⟨tb, rfl⟩ := Kanon.NodeEmbed.exists_of_proj _ hb
    obtain ⟨-, wfa⟩ := wt_lit.1 wa
    obtain ⟨-, wfb⟩ := wt_lit.1 wb
    rw [ev_lit] at ea eb
    have := vlit_inj wfa wfb (Option.some.inj (ea.trans eb.symm))
    simp [f_equal, this] at hr
  · cases h

@[kanon_arm] theorem Float.abs.r_lit.main.proof : Float.abs.r_lit.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO f t
  exact un_lits (lit := f_abs) (un_bits fun _ x => x.abs) (fun a => .FAbs a) (by float_un_wt)
    (fun _ _ _ => by rw [ev_mk]; rfl) f t

@[kanon_arm] theorem Float.neg.r_lit.main.proof : Float.neg.r_lit.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO f t
  exact un_lits (lit := f_neg) (un_bits fun _ x => x.neg) (fun a => .FNeg a) (by float_un_wt)
    (fun _ _ _ => by rw [ev_mk]; rfl) f t

@[kanon_arm] theorem Float.sqrt.r_lit.main.proof : Float.sqrt.r_lit.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO f t
  exact un_lits hO.float_orc.sqrt (fun a => .FSqrt a) (by float_un_wt)
    (fun _ _ _ => by rw [ev_mk]; rfl) f t

@[kanon_arm] theorem Float.round.r_lit.main.proof : Float.round.r_lit.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO rm f t
  exact un_lits (hO.float_orc.round rm) (fun a => .FRound rm a) (by float_un_wt)
    (fun _ _ _ => by rw [ev_mk]; rfl) f t

@[kanon_arm] theorem Float.abs.r_abs.main.proof : Float.abs.r_abs.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO w t
  refine Kanon.Sem.Refines.intro (fun hw => ⟨?_, by simp [Float.abs.spec]⟩) (fun ρ v _ _ e => ?_)
  · rw [Float.abs.spec, WT_mk] at hw; exact hw.2
  · simp only [Float.abs.spec, ev_mk, Node.map, Node.eval, fUn_fUn, fbits_abs_abs] at e ⊢
    exact e

@[kanon_arm] theorem Float.neg.r_neg.main.proof : Float.neg.r_neg.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO v t
  refine Kanon.Sem.Refines.intro (fun hw => ?_) (fun ρ u _ _ e => ?_)
  · rw [Float.neg.spec, WT_mk] at hw
    obtain ⟨-, hw⟩ := hw
    simp only [Node.All] at hw
    rw [WT_mk] at hw
    obtain ⟨⟨-, ht'⟩, hw⟩ := hw
    simp only [Float.neg.spec, ty_mk] at ht' ⊢
    exact ⟨hw, ht'.symm⟩
  · simp only [Float.neg.spec, ev_mk, Node.map, Node.eval, fUn_fUn, fbits_neg_neg] at e
    obtain ⟨p, x, h, hx⟩ := withF_eq_some.1 e
    rw [h, ← Option.some.inj hx]

@[kanon_arm] theorem Float.cast.r_lit.main.proof : Float.cast.r_lit.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO rm fp f t
  simp only [Float.cast.spec, f_prec]
  refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;>
    rw [WT_mk] at w <;>
    obtain ⟨⟨-, -⟩, w1⟩ := w <;>
    obtain ⟨rfl, wf⟩ := wt_lit.1 w1 <;>
    obtain ⟨hp, hwf, hv⟩ := hO.float_orc.convert rm fp f wf
  · exact ⟨wt_lit.2 ⟨rfl, hwf⟩, by simp [hp]⟩
  · rw [ev_mk] at e
    simp only [Node.map, Node.eval, ev_lit, vlit, withF_vf] at e
    rw [ev_lit, hv, ← e]

@[kanon_arm] theorem Float.fma.r_lits.main.proof : Float.fma.r_lits.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO fa ta fb tb fc tc
  simp only [Float.fma.spec, f_prec]
  refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;>
    rw [WT_mk] at w <;>
    obtain ⟨⟨-, h2, h3, -⟩, w1, w2, w3⟩ := w <;>
    obtain ⟨rfl, wf1⟩ := wt_lit.1 w1 <;> obtain ⟨rfl, wf2⟩ := wt_lit.1 w2 <;>
    obtain ⟨rfl, wf3⟩ := wt_lit.1 w3 <;>
    simp only [ty_mk, sort_inj_iff, Srt.TFloat.injEq] at h2 h3 <;>
    obtain ⟨hp, hwf, hv⟩ := hO.float_orc.fma fa fb fc wf1 wf2 wf3 h2 h3
  · exact ⟨wt_lit.2 ⟨rfl, hwf⟩, by simp [hp]⟩
  · rw [ev_mk] at e
    simp only [Node.map, Node.eval, ev_lit] at e
    rw [ev_lit, hv, ← e]
    obtain ⟨p1, b1⟩ := fa; obtain ⟨p2, b2⟩ := fb; obtain ⟨p3, b3⟩ := fc
    simp only at h2 h3; subst h2; subst h3
    simp [vlit]

@[kanon_arm] theorem Float.of_float.r_lit.main.proof : Float.of_float.r_lit.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO rm sg sz f t
  cases h : O.float_f_to_int rm sg sz f with
  | none =>
    simp [Kanon.firstSome]
    exact Kanon.Sem.Refines.refl
  | some z =>
    simp [Kanon.firstSome]
    simp only [Float.of_float.spec, BitvecMod.mk_masked]
    refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;>
      rw [WT_mk] at w <;> obtain ⟨⟨hsz, -, -⟩, w1⟩ := w <;> obtain ⟨-, wf⟩ := wt_lit.1 w1
    · refine ⟨?_, by simp⟩
      have hp : (0 : Int) < 2 ^ sz.toNat := Int.pow_pos (by decide)
      rw [BitvecMod.WT_mk]
      simp only [BitvecMod.Node.wt, BitvecMod.bv_wf, BitvecMod.Node.All, BitvecMod.sort_inj_iff,
        BitvecMod.Srt.TBitVector.injEq, reduceCtorEq, or_false]
      exact ⟨⟨⟨sz, hsz, rfl⟩, fun m hm => by
        subst hm; exact ⟨Int.emod_nonneg _ (Int.ne_of_gt hp), Int.emod_lt_of_pos _ hp⟩⟩, trivial⟩
    · rw [ev_mk] at e
      simp only [Node.map, Node.eval, ev_lit, vlit, withF_vf,
        hO.float_orc.to_int rm sg sz f z wf hsz h] at e
      rw [BitvecMod.ev_mk]
      simp only [BitvecMod.Node.map, BitvecMod.Node.eval]
      rw [BitvecMod.width_sort ρ (Or.inl rfl) hsz, BitvecMod.ofBV_some, ← e]
      congr 2
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofInt]

@[kanon_arm] theorem Float.to_float.r_lit.main.proof : Float.to_float.r_lit.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO rm sg fp z t
  cases h : O.float_f_of_int rm sg fp (BitvecMod.Bitvec.size (BitvecMod.mk (.BitVec z) t)) z with
  | none =>
    simp [Kanon.firstSome]
    exact Kanon.Sem.Refines.refl
  | some g =>
    simp [Kanon.firstSome]
    obtain ⟨hp, hg⟩ := hO.float_orc.of_int_prec _ _ _ _ _ _ h
    simp only [Float.to_float.spec]
    refine Kanon.Sem.Refines.intro (fun _ => ⟨wt_lit.2 ⟨by simp, hg⟩, by simp [hp]⟩)
      (fun ρ v w _ e => ?_)
    rw [WT_mk] at w
    obtain ⟨⟨⟨n, hn, ht⟩, -⟩, wl⟩ := w
    simp only [BitvecMod.ty_mk] at ht; subst ht
    simp only [Node.All] at wl
    rw [BitvecMod.WT_mk] at wl
    obtain ⟨⟨-, hwf⟩, -⟩ := wl
    obtain ⟨hz0, hz1⟩ := hwf n (Or.inl rfl)
    have hw := BitvecMod.width_sort ρ (Or.inl rfl) hn
    simp only [BitvecMod.Bitvec.size, BitvecMod.ty_mk, BitvecMod.size_of_ty_TBitVector] at h
    have hv := hO.float_orc.of_int rm sg fp _ z g hn hz0 hz1 h
    rw [ev_mk] at e
    simp only [Node.map, Node.eval, BitvecMod.ev_mk, BitvecMod.Node.map, BitvecMod.Node.eval] at e
    rw [hw] at e
    simp only [BitvecMod.ofBV_some, BitvecMod.withW_bv, BitvecMod.asBV_bv, Option.map_some] at e
    rw [ev_lit, hv, ← e]

@[kanon_arm] theorem Float.to_float_bits.r_lit.main.proof :
    Float.to_float_bits.r_lit.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO fp z t
  simp only [Float.to_float_bits.spec, f_of_bits, f_prec]
  have hs : (0 : Int) < fp_size fp := by cases fp <;> decide
  have hp : (0 : Int) < 2 ^ fp.size := Int.pow_pos (by decide)
  have e2 : ((2 ^ fp.size : Nat) : Int) = 2 ^ fp.size := by simp
  have h1 := Int.emod_lt_of_pos z hp
  have h2 := Int.emod_nonneg z (Int.ne_of_gt hp)
  refine Kanon.Sem.Refines.intro (fun _ => ⟨wt_lit.2 ⟨rfl, ?_⟩, by simp⟩) (fun ρ v w _ e => ?_)
  · show (z % 2 ^ fp.size).toNat < 2 ^ fp.size
    omega
  · rw [WT_mk] at w
    obtain ⟨⟨ht, -⟩, -⟩ := w
    simp only [BitvecMod.ty_mk] at ht; subst ht
    have hw := BitvecMod.width_sort ρ (Or.inl rfl) hs
    have : (fp_size fp).toNat = fp.size := by simp [fp_size]
    rw [this] at hw
    rw [ev_mk] at e
    simp only [Node.map, Node.eval, BitvecMod.ev_mk, BitvecMod.Node.map, BitvecMod.Node.eval] at e
    rw [hw] at e
    simp only [BitvecMod.ofBV_some, BitvecMod.asBV_bv, Option.map_some] at e
    rw [ev_lit, ← e]
    simp only [vlit, CoreMod.Float.val]
    congr 2
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofInt, Nat.mod_eq_of_lt (by omega)]
    rw [e2]

section

variable {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [BitvecMod.Lang S] [Lang S]

theorem fbits_eq_self {p : Fp} (x : FBits p) : x.eq x = !x.isNaN := by
  simp [FBits.eq]

theorem fbits_not_isNaN_of_isZero {p : Fp} {x : FBits p} (h : x.isZero = true) :
    x.isNaN = false := by
  simp only [FBits.isZero, FBits.isNaN, Bool.and_eq_true, beq_iff_eq] at h ⊢
  simp [h.2]

theorem fbits_eq_of_isNaN_left {p : Fp} {x : FBits p} (y : FBits p) (h : x.isNaN = true) :
    x.eq y = false := by
  simp [FBits.eq, h]

theorem fbits_eq_of_isZero_left {p : Fp} {x : FBits p} (y : FBits p) (h : x.isZero = true) :
    x.eq y = y.isZero := by
  have hx := fbits_not_isNaN_of_isZero h
  unfold FBits.eq
  by_cases hy : y.isZero = true
  · simp [hx, hy, h, fbits_not_isNaN_of_isZero hy]
  · have : (x == y) = false := by
      simp only [beq_eq_false_iff_ne]; rintro rfl; exact hy h
    simp [hx, hy, this]

theorem fbits_eq_of_ne_left {p : Fp} {x : FBits p} (y : FBits p) (h1 : x.isNaN = false)
    (h2 : x.isZero = false) : x.eq y = decide (x = y) := by
  unfold FBits.eq
  by_cases hxy : x = y
  · subst hxy; simp [h1]
  · have : (x == y) = false := by simp [hxy]
    simp [h2, this, hxy]

theorem vf_inj {p : Fp} {x y : FBits p} : vf (D := S.toDom) p x = vf p y ↔ x = y := by
  simp [vf, Embed.inj_eq_iff]

/-- `v == v` on floats is `v` not being NaN. -/
theorem feq_self {v : S.Term} {t : S.Ty} :
    S.Refines (mk (.FEq v v) t)
      (KanonBool.mk (.Not (mk (.FIs .NaN v) (KanonBool.sort .TBool))) (KanonBool.sort .TBool)) := by
  refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ u w _ e => ?_)
  · rw [WT_mk] at w
    obtain ⟨⟨hp, -, rfl⟩, wv, -⟩ := w
    refine ⟨?_, by simp⟩
    rw [KanonBool.WT_mk]
    refine ⟨⟨by simp, rfl⟩, ?_⟩
    simp only [KanonBool.Node.All]
    rw [WT_mk]
    exact ⟨⟨hp, rfl⟩, wv⟩
  · rw [ev_mk] at e
    simp only [Node.map, Node.eval, fCmp] at e
    obtain ⟨p, x, y, ha, hb, h⟩ := fBin_eq_some.1 e
    rw [ha] at hb
    obtain rfl := vf_inj.1 (Option.some.inj hb)
    rw [KanonBool.ev_mk]
    simp only [KanonBool.Node.map, KanonBool.Node.eval, ev_mk, Node.map, Node.eval, fPred, ha,
      withF_vf, ← Option.some.inj h, fbits_eq_self]
    cases hx : x.isNaN <;> simp [KanonBool.pnot, FBits.isClass, hx]

/-- `fp.eq` against a float literal, by the value it compares to. -/
theorem feq_lit {f : CoreMod.Float} {t2 t : S.Ty} {v r : S.Term}
    (hr : S.WT v → S.ty v = sort (.TFloat f.prec) → S.WT (mk (.Float f) t2) →
      t2 = sort (.TFloat f.prec) → S.WT r ∧ S.ty r = KanonBool.sort .TBool)
    (hv : ∀ ρ (y : FBits f.prec), S.ev ρ v = some (vf f.prec y) →
      S.ev ρ r = some (KanonBool.Values.vbool.inj (f.val.eq y))) :
    S.Refines (mk (.FEq (mk (.Float f) t2) v) t) r := by
  refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ u w _ e => ?_) <;>
    rw [WT_mk] at w <;> obtain ⟨⟨-, h2, ht⟩, w1, wv⟩ := w <;>
    obtain ⟨rfl, -⟩ := wt_lit.1 w1 <;> rw [ty_mk] at h2
  · rw [ty_mk, ht]; exact hr wv h2 w1 rfl
  · rw [ev_mk] at e
    simp only [Node.map, Node.eval, fCmp, fBin, ev_lit, vlit, withF_vf,
      Option.bind_eq_some_iff, asF_eq_some] at e
    obtain ⟨y, hy, h⟩ := e
    exact (hv ρ y hy).trans h

end

@[kanon_arm] theorem Float.eq.r_same.main.proof : Float.eq.r_same.main.Stmt := by
  kanon_rule_lift
  exact feq_self

@[kanon_arm] theorem Float.eq.r_lit.main.proof : Float.eq.r_lit.main.Stmt := by
  kanon_rule_lift
  · rename_i hn
    refine feq_lit (fun _ _ _ _ => ⟨wt_bool.2 rfl, by simp [KanonBool.v_false]⟩) (fun ρ y _ => ?_)
    rw [KanonBool.v_false, ev_bool, fbits_eq_of_isNaN_left y hn]
  · rename_i hz
    refine feq_lit (fun wv hv _ _ => ⟨?_, by simp⟩) (fun ρ y ev => ?_)
    · rw [WT_mk]; exact ⟨⟨⟨_, hv⟩, rfl⟩, wv⟩
    · rw [ev_mk]
      simp only [Node.map, Node.eval, fPred, ev, withF_vf, fbits_eq_of_isZero_left y hz]
      rfl
  · rename_i hn hz
    simp only [f_is_nan, f_is_zero, Bool.not_eq_true] at hn hz
    refine feq_lit (fun wv hv w1 ht2 => ⟨?_, by simp⟩) (fun ρ y ev => ?_)
    · rw [KanonBool.WT_mk]
      exact ⟨⟨by rw [hv, ty_mk, ht2], rfl⟩, w1, wv⟩
    · rw [KanonBool.ev_mk]
      simp only [KanonBool.Node.map, KanonBool.Node.eval, ev, ev_lit, vlit, KanonBool.peq,
        vf_inj, fbits_eq_of_ne_left y hn hz]

@[kanon_arm] theorem Float.fmod.r_lits.main.proof : Float.fmod.r_lits.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO f1 t1 f2 t2
  simp only [Float.fmod.spec, Float.raw_fmod_of_rem, f_prec]
  refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;>
    rw [KanonBool.WT_mk] at w <;> obtain ⟨-, -, wr, -⟩ := w <;>
    rw [WT_mk] at wr <;> obtain ⟨⟨-, h2, -⟩, w1, w2⟩ := wr <;>
    obtain ⟨rfl, wf1⟩ := wt_lit.1 w1 <;> obtain ⟨rfl, wf2⟩ := wt_lit.1 w2 <;>
    simp only [ty_mk, sort_inj_iff, Srt.TFloat.injEq] at h2 <;>
    obtain ⟨hp, hwf, hv⟩ := hO.float_orc.fmod f1 f2 wf1 wf2 h2
  · exact ⟨wt_lit.2 ⟨rfl, hwf⟩, by simp [hp]⟩
  · rw [ev_lit, hv, ← e]
    obtain ⟨p1, b1⟩ := f1; obtain ⟨p2, b2⟩ := f2
    simp only at h2; subst h2
    simp only [KanonBool.ev_mk, ev_mk, KanonBool.Node.map, KanonBool.Node.eval, Node.map,
      Node.eval, vlit, fArith, fUn, fPred, fBin_vf, withF_vf, KanonBool.peq,
      KanonBool.pite, Embed.inj_eq_iff, fmodBits, Option.some.injEq]
    generalize Values.rem S.toDom p2 _ _ = r
    cases hr : r.isNeg <;> cases hx : (CoreMod.Float.val ⟨p2, b1⟩).isNeg <;> simp [hr, hx]
end FloatMod
