import PtrMod.Statements.Bool.eq
import PtrMod.Statements.Bool.sure_neq
import PtrMod.Statements.Ptr.loc
import PtrMod.Statements.Ptr.ofs

/-!
# The proofs of the ptr module that the tactics do not find

A pointer is the pair of its location and offset, which have the width of the
pointer: projecting a pointer gives back the projected child, and pointers are
equal exactly when their locations and offsets are.
-/

namespace PtrMod

open Classical Kanon
open BitvecMod (bv)

section

variable {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [BitvecMod.Lang S] [Lang S]

/-- The value of a pointer node: the location and offset of its children. -/
theorem ev_ptr {ρ : S.Env} {l o : S.Term} {t : S.Ty} {v : S.Val}
    (e : S.ev ρ (mk (.Ptr l o) t) = some v) :
    ∃ n x y, S.ev ρ l = some (bv n x) ∧ S.ev ρ o = some (bv n y) ∧ v = vp n x y := by
  rw [ev_mk] at e
  simp only [Node.map, Node.eval] at e
  obtain ⟨n, x, hl, e⟩ := BitvecMod.withW_eq_some.1 e
  simp only [hl, BitvecMod.asBV_bv, Option.bind_some, Option.map_eq_some_iff,
    BitvecMod.asBV_eq_some] at e
  obtain ⟨y, hy, rfl⟩ := e
  exact ⟨n, x, y, hl, hy, rfl⟩

/-- The typing of a pointer node: a location and an offset of its width. -/
theorem wt_ptr {l o : S.Term} {t : S.Ty} (w : S.WT (mk (.Ptr l o) t)) :
    ∃ n : Int, S.WT l ∧ S.WT o ∧ S.ty l = BitvecMod.sort (.TLoc n) ∧
      S.ty o = BitvecMod.sort (.TBitVector n) ∧ t = sort (.TPointer n) := by
  rw [WT_mk] at w
  obtain ⟨⟨n, -, hl, ho, ht⟩, wl, wo⟩ := w
  exact ⟨n, wl, wo, hl, ho, ht⟩

/-- Pointers are equal exactly when their locations and offsets are. -/
theorem vp_eq_iff {n m : Nat} {x y : BitVec n} {x' y' : BitVec m} :
    vp (D := S.toDom) n x y = vp m x' y' ↔
      bv (D := S.toDom) n x = bv m x' ∧ bv (D := S.toDom) n y = bv m y' := by
  simp only [vp, bv, Embed.inj_eq_iff]
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    cases h1; cases h2; rfl

end

@[kanon_arm] theorem Ptr.loc.r_ptr.main.proof : Ptr.loc.r_ptr.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO l o t
  refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · rw [Ptr.loc.spec, WT_mk] at w
    obtain ⟨⟨n, -, hp, ht⟩, wp⟩ := w
    obtain ⟨m, wl, -, hl, -, rfl⟩ := wt_ptr wp
    rw [ty_mk, sort_inj_iff, Srt.TPointer.injEq] at hp
    subst hp
    simp only [Ptr.loc.spec, ty_mk]
    exact ⟨wl, hl.trans ht.symm⟩
  · rw [Ptr.loc.spec, ev_mk] at e
    simp only [Node.map, Node.eval] at e
    obtain ⟨n, a, b, hp, ⟨⟩⟩ := withP_eq_some.1 e
    obtain ⟨m, x, y, hl, -, h⟩ := ev_ptr hp
    simp only [Embed.inj_eq_iff] at h
    cases h
    exact hl

@[kanon_arm] theorem Ptr.ofs.r_ptr.main.proof : Ptr.ofs.r_ptr.main.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO l o t
  refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · rw [Ptr.ofs.spec, WT_mk] at w
    obtain ⟨⟨n, -, hp, ht⟩, wp⟩ := w
    obtain ⟨m, -, wo, -, ho, rfl⟩ := wt_ptr wp
    rw [ty_mk, sort_inj_iff, Srt.TPointer.injEq] at hp
    subst hp
    simp only [Ptr.ofs.spec, ty_mk]
    exact ⟨wo, ho.trans ht.symm⟩
  · rw [Ptr.ofs.spec, ev_mk] at e
    simp only [Node.map, Node.eval] at e
    obtain ⟨n, a, b, hp, ⟨⟩⟩ := withP_eq_some.1 e
    obtain ⟨m, x, y, -, ho, h⟩ := ev_ptr hp
    simp only [Embed.inj_eq_iff] at h
    cases h
    exact ho

@[kanon_arm] theorem Bool.eq.r_ptrs.main.proof : Bool.eq.r_ptrs.main.Stmt := by
  kanon_rule_lift
  rename_i S _ _ _ _ _ _ _ _ O hO l1 o1 t1 l2 o2 t2
  refine Kanon.Sem.Refines.intro (by kanon_wt) (fun ρ v w _ e => ?_)
  rw [KanonBool.ev_mk] at e
  simp only [KanonBool.Node.map, KanonBool.Node.eval, KanonBool.peq_eq_some] at e
  obtain ⟨u1, u2, e1, e2, rfl⟩ := e
  obtain ⟨n1, x1, y1, hl1, ho1, rfl⟩ := ev_ptr e1
  obtain ⟨n2, x2, y2, hl2, ho2, rfl⟩ := ev_ptr e2
  rw [KanonBool.ev_mk]
  simp only [KanonBool.Node.map, KanonBool.Node.eval, KanonBool.ev_mk, KanonBool.peq, hl1, hl2,
    ho1, ho2]
  by_cases h1 : bv (D := S.toDom) n1 x1 = bv n2 x2 <;>
    by_cases h2 : bv (D := S.toDom) n1 y1 = bv n2 y2
  · rw [decide_eq_true (vp_eq_iff.2 ⟨h1, h2⟩)]; simp [KanonBool.pand, h1, h2]
  · rw [decide_eq_false (p := vp n1 x1 y1 = vp n2 x2 y2) fun h => h2 (vp_eq_iff.1 h).2]
    simp [KanonBool.pand, h1, h2]
  all_goals
    rw [decide_eq_false (p := vp n1 x1 y1 = vp n2 x2 y2) fun h => h1 (vp_eq_iff.1 h).1]
    simp [KanonBool.pand, h1, h2]

@[kanon_arm] theorem Bool.sure_neq.c1.proof : Bool.sure_neq.c1.Stmt := by
  intro S _ _ _ _ _ _ _ _ O hO a b r h
  simp only [Bool.sure_neq.c1] at h
  split at h
  · rename_i la oa lb ob ha hb
    cases h
    intro hr wa wb hty ρ u ea eb
    obtain ⟨t, rfl⟩ := Kanon.NodeEmbed.exists_of_proj _ ha
    obtain ⟨t', rfl⟩ := Kanon.NodeEmbed.exists_of_proj _ hb
    obtain ⟨n, wla, woa, hla, hoa, rfl⟩ := wt_ptr wa
    obtain ⟨m, wlb, wob, hlb, hob, rfl⟩ := wt_ptr wb
    simp only [ty_mk, sort_inj_iff, Srt.TPointer.injEq] at hty
    subst hty
    obtain ⟨n1, x1, y1, hl1, ho1, rfl⟩ := ev_ptr ea
    obtain ⟨n2, x2, y2, hl2, ho2, h⟩ := ev_ptr eb
    obtain ⟨h1, h2⟩ := vp_eq_iff.1 h
    rcases Bool.or_eq_true_iff.1 hr with hr | hr
    · exact hO.bool_sure_neq la lb hr wla wlb (hla.trans hlb.symm) ρ _ hl1
        (hl2.trans (congrArg some h1.symm))
    · exact hO.bool_sure_neq oa ob hr woa wob (hoa.trans hob.symm) ρ _ ho1
        (ho2.trans (congrArg some h2.symm))
  · cases h

end PtrMod
