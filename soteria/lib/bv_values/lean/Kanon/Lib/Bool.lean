import Kanon.Lib.Float
import Kanon.Model.Bool.sure_neq

/-!
# The laws of the bool and exists modules

Kanon's library proves the rules of the bool module once (`KanonBool`), for
any language that gives its interface and an instance of `KanonBool.Sem` (in
`Lang.lean`). The only law that is more than the typing and evaluation of the
nodes is that of `Bool.sure_neq`, which the other modules extend; the exists
module needs that the unused binders of an `Exists` do not matter.
-/

namespace Kanon.Lib

open CoreMod

open Classical

/-! ## `Bool.sure_neq` -/

theorem getD_firstSome_orElse {α} {o : Option α} {l : List (Option α)} {d : α} :
    (firstSome (o :: l)).getD d = match o with | some x => x | none => (firstSome l).getD d := by
  cases o <;> simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

theorem sure_neq_cases {a b : Term} (h : Bool.sure_neq a b = true) :
    a.ty ≠ b.ty ∨
    (∃ za zb Ta Tb, a = .mk (.BitVec za) Ta ∧ b = .mk (.BitVec zb) Tb ∧ za ≠ zb) ∨
    (∃ za zb Ta Tb, a = .mk (.LocLit za) Ta ∧ b = .mk (.LocLit zb) Tb ∧ za ≠ zb) ∨
    (∃ fa fb Ta Tb, a = .mk (.Float fa) Ta ∧ b = .mk (.Float fb) Tb ∧ fa ≠ fb) ∨
    (∃ ba bb Ta Tb, a = .mk (.Bool ba) Ta ∧ b = .mk (.Bool bb) Tb ∧ ba ≠ bb) ∨
    (∃ la oa lb ob Ta Tb, a = .mk (.Op2 .Ptr la oa) Ta ∧ b = .mk (.Op2 .Ptr lb ob) Tb ∧
      (Bool.sure_neq la lb = true ∨ Bool.sure_neq oa ob = true)) := by
  unfold Bool.sure_neq at h
  simp only [getD_firstSome_orElse, Bool.or_eq_true, Bool.not_eq_true', ty_eq] at h
  rcases h with h | h
  · left; exact of_decide_eq_false h
  right
  rcases a with ⟨ka, Ta⟩; rcases b with ⟨kb, Tb⟩
  cases ka <;> cases kb <;> simp [firstSome, f_equal] at h ⊢
  all_goals first
    | assumption
    | (rename_i o1 a1 b1 o2 a2 b2
       cases o1 <;> cases o2 <;> first
         | (simp at h; done)
         | exact ⟨_, _, ⟨rfl, rfl, rfl⟩, _, _, ⟨rfl, rfl, rfl⟩, by simpa using h⟩)

theorem sure_neq_sound_aux {FS : FloatSem} (k : Nat) : ∀ {a b : Term} {ρ : Env} {u : Val},
    sizeOf a < k → Bool.sure_neq a b = true →
    a.ty = b.ty → eval FS ρ a = some u → eval FS ρ b = some u → False := by
  induction k with
  | zero => intros; omega
  | succ k ih =>
    intro a b ρ u hk h ht ea eb
    rcases sure_neq_cases h with h | ⟨za, zb, Ta, Tb, rfl, rfl, hz⟩ |
      ⟨za, zb, Ta, Tb, rfl, rfl, hz⟩ | ⟨fa, fb, Ta, Tb, rfl, rfl, hf⟩ | ⟨ba, bb, Ta, Tb, rfl, rfl, hb⟩ |
      ⟨la, oa, lb, ob, Ta, Tb, rfl, rfl, hp⟩
    · exact h ht
    · simp only [Term.ty_mk] at ht; subst ht
      have wa := eval_WT ea; have wb := eval_WT eb
      obtain ⟨n, hn, hT, h0, h1⟩ := WT_bitVec.1 wa
      obtain ⟨n', hn', hT', h0', h1'⟩ := WT_bitVec.1 wb
      have : n' = n := by
        simp only [hT', Ty.TBitVector.injEq] at hT; omega
      subst this
      rw [eval_bitVec' wa hT] at ea; rw [eval_bitVec' wb hT, ← ea] at eb
      simp only [Option.some.injEq, Val.bv.injEq, heq_eq_eq, true_and] at eb
      have := congrArg BitVec.toNat eb
      simp only [BitVec.toNat_ofInt] at this
      simp only [Int.toNat_natCast] at this; push_cast at this
      rw [Int.emod_eq_of_lt h0' h1', Int.emod_eq_of_lt h0 h1] at this
      exact hz (by omega)
    · simp only [Term.ty_mk] at ht; subst ht
      have wa := eval_WT ea; have wb := eval_WT eb
      obtain ⟨n, hn, hT, h0, h1⟩ := WT_locLit.1 wa
      obtain ⟨n', hn', hT', h0', h1'⟩ := WT_locLit.1 wb
      have : n' = n := by
        simp only [hT', Ty.TLoc.injEq] at hT; omega
      subst this
      rw [eval_locLit' wa hT] at ea; rw [eval_locLit' wb hT, ← ea] at eb
      simp only [Option.some.injEq, Val.bv.injEq, heq_eq_eq, true_and] at eb
      have := congrArg BitVec.toNat eb
      simp only [BitVec.toNat_ofInt] at this
      simp only [Int.toNat_natCast] at this; push_cast at this
      rw [Int.emod_eq_of_lt h0' h1', Int.emod_eq_of_lt h0 h1] at this
      exact hz (by omega)
    · have wa := eval_WT ea; have wb := eval_WT eb
      rw [eval_eq_ev wa, ev] at ea; rw [eval_eq_ev wb, ev, ← ea] at eb
      simp only [Term.WT] at wa wb
      rcases fa with ⟨p, x⟩; rcases fb with ⟨q, y⟩
      simp only [Float.sem, Float.val, Option.some.injEq, Val.float.injEq] at eb
      obtain ⟨rfl, eb⟩ := eb
      simp only [heq_eq_eq] at eb
      have := congrArg BitVec.toNat eb
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt wa.2, Nat.mod_eq_of_lt wb.2] at this
      exact hf (by simp at this ⊢; omega)
    · simp only [eval_bool (WT_bool.1 (eval_WT ea)), eval_bool (WT_bool.1 (eval_WT eb))] at ea eb
      rw [← ea] at eb; simp at eb; exact hb eb.symm
    · obtain ⟨n, x, y, hla, hoa, rfl⟩ := (eval_ptr_eq_some (eval_WT ea)).1 ea
      obtain ⟨n', x', y', hlb, hob, he⟩ := (eval_ptr_eq_some (eval_WT eb)).1 eb
      simp only [Val.ptr.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      obtain ⟨m, -, hTa, hla', hoa', -, -⟩ := WT_ptr.1 (eval_WT ea)
      obtain ⟨m', -, hTb, hlb', hob', -, -⟩ := WT_ptr.1 (eval_WT eb)
      simp only [Term.ty_mk] at ht; rw [hTa, hTb] at ht; simp only [Ty.TPointer.injEq] at ht
      subst ht
      rcases hp with hp | hp
      · exact ih (by simp at hk; omega) hp (hla'.trans hlb'.symm) hla hlb
      · exact ih (by simp at hk; omega) hp (hoa'.trans hob'.symm) hoa hob

theorem sure_neq_sound {FS : FloatSem} {a b : Term} {ρ : Env} {u : Val} (h : Bool.sure_neq a b = true)
    (ht : a.ty = b.ty) (ea : eval FS ρ a = some u) (eb : eval FS ρ b = some u) : False :=
  sure_neq_sound_aux (sizeOf a + 1) (Nat.lt_succ_self _) h ht ea eb

theorem evList_eq {FS : FloatSem} {ρ : Env} : ∀ l, evList FS ρ l = l.mapM (ev FS ρ)
  | [] => by simp [evList]
  | t :: ts => by
    rw [evList, List.mapM_cons, evList_eq ts]
    cases ev FS ρ t <;> cases ts.mapM (ev FS ρ) <;> rfl

/-! ## `exists` -/

theorem mem_freeVars_exists {bs : List (Int × Ty)} {body : Term} {T : Ty} {v : Int} :
    v ∈ (Term.mk (.Exists bs body) T).freeVars ↔ v ∈ body.freeVars ∧ ∀ b ∈ bs, b.1 ≠ v := by
  simp [Term.freeVars]

/-- Moving an extension of [ρa] to one of [ρb], where they agree on the free variables. -/
theorem extends_transfer {bs : List (Int × Ty)} {P : Int → Prop} {ρa ρb ρ' : Env}
    (hv : ∀ v, P v → (∀ b ∈ bs, b.1 ≠ v) → ρa.var v = ρb.var v)
    (h : ρ'.Extends ρa bs) :
    ∃ ρ'' : Env, ρ''.Extends ρb bs ∧ ∀ v, P v → ρ''.var v = ρ'.var v := by
  refine ⟨⟨fun v => if ∃ b ∈ bs, b.1 = v then ρ'.var v else ρb.var v⟩,
    ⟨fun v hn => ?_, fun b hb => ?_⟩, fun v hP => ?_⟩
  · have : ¬ ∃ b ∈ bs, b.1 = v := fun ⟨b, hb, e⟩ => hn b hb e
    simp only [this, ite_false]
  · simp only [show ∃ b' ∈ bs, b'.1 = b.1 from ⟨b, hb, rfl⟩, ite_true]; exact h.2 b hb
  · by_cases hc : ∃ b ∈ bs, b.1 = v
    · simp [hc]
    · have hn : ∀ b ∈ bs, b.1 ≠ v := fun b hb e => hc ⟨b, hb, e⟩
      simp only [hc, ite_false]; rw [h.1 v hn, hv v hP hn]

mutual

theorem ev_congr {FS : FloatSem} :
    ∀ (t : Term) (ρ1 ρ2 : Env), (∀ v ∈ t.freeVars, ρ1.var v = ρ2.var v) →
      ev FS ρ1 t = ev FS ρ2 t
  | .mk (.Var x) T, ρ1, ρ2, hv => by
      simp only [ev]; rw [hv x (by simp [Term.freeVars])]
  | .mk (.Bool b) T, ρ1, ρ2, _ => by simp only [ev]
  | .mk (.Float f) T, ρ1, ρ2, _ => by simp only [ev]
  | .mk (.BitVec z) T, ρ1, ρ2, _ => by simp only [ev]
  | .mk (.LocLit z) T, ρ1, ρ2, _ => by simp only [ev]
  | .mk (.Seq l) T, ρ1, ρ2, hv => by
      simp only [ev]
      rw [evList_congr l ρ1 ρ2 (fun v h => hv v (by simpa [Term.freeVars] using h))]
  | .mk (.Op1 op a) T, ρ1, ρ2, hv => by
      simp only [ev]
      rw [ev_congr a ρ1 ρ2 (fun v h => hv v (by simpa [Term.freeVars] using h))]
  | .mk (.Op2 op a b) T, ρ1, ρ2, hv => by
      simp only [ev]
      rw [ev_congr a ρ1 ρ2 (fun v h => hv v (by simp [Term.freeVars, h])),
        ev_congr b ρ1 ρ2 (fun v h => hv v (by simp [Term.freeVars, h]))]
  | .mk (.Op3 op g a b) T, ρ1, ρ2, hv => by
      have hg := ev_congr (FS := FS) g ρ1 ρ2 (fun v h => hv v (by simp [Term.freeVars, h]))
      have ha := ev_congr (FS := FS) a ρ1 ρ2 (fun v h => hv v (by simp [Term.freeVars, h]))
      have hb := ev_congr (FS := FS) b ρ1 ρ2 (fun v h => hv v (by simp [Term.freeVars, h]))
      simp only [ev]; rw [hg, ha, hb]
  | .mk (.OpN op l) T, ρ1, ρ2, hv => by
      cases op
      simp only [ev]
      rw [evList_congr l ρ1 ρ2 (fun v h => hv v (by simpa [Term.freeVars] using h))]
  | .mk (.Exists bs body) T, ρ1, ρ2, hv => by
      have key : ∀ ρa ρb : Env,
          (∀ v, v ∈ body.freeVars → (∀ b ∈ bs, b.1 ≠ v) → ρa.var v = ρb.var v) →
          ∀ ρ' : Env, ρ'.Extends ρa bs →
            ∃ ρ'' : Env, ρ''.Extends ρb bs ∧ ev FS ρ'' body = ev FS ρ' body := by
        intro ρa ρb hvab ρ' hext
        obtain ⟨ρ'', h1, h3⟩ := extends_transfer (P := (· ∈ body.freeVars)) hvab hext
        exact ⟨ρ'', h1, ev_congr body ρ'' ρ' h3⟩
      have hv' : ∀ v, v ∈ body.freeVars → (∀ b ∈ bs, b.1 ≠ v) → ρ1.var v = ρ2.var v :=
        fun v h1 h2 => hv v (mem_freeVars_exists.2 ⟨h1, h2⟩)
      have k12 := key ρ1 ρ2 hv'
      have k21 := key ρ2 ρ1 (fun v h1 h2 => (hv' v h1 h2).symm)
      have hC : (∀ ρ' : Env, ρ'.Extends ρ1 bs → ∃ b, ev FS ρ' body = some (.bool b)) ↔
          (∀ ρ' : Env, ρ'.Extends ρ2 bs → ∃ b, ev FS ρ' body = some (.bool b)) := by
        constructor
        · intro h ρ' hx; obtain ⟨ρ'', h1, h2⟩ := k21 ρ' hx; rw [← h2]; exact h ρ'' h1
        · intro h ρ' hx; obtain ⟨ρ'', h1, h2⟩ := k12 ρ' hx; rw [← h2]; exact h ρ'' h1
      have hE : (∃ ρ' : Env, ρ'.Extends ρ1 bs ∧ ev FS ρ' body = some (.bool true)) ↔
          (∃ ρ' : Env, ρ'.Extends ρ2 bs ∧ ev FS ρ' body = some (.bool true)) := by
        constructor
        · rintro ⟨ρ', hx, e⟩; obtain ⟨ρ'', h1, h2⟩ := k12 ρ' hx; exact ⟨ρ'', h1, h2.trans e⟩
        · rintro ⟨ρ', hx, e⟩; obtain ⟨ρ'', h1, h2⟩ := k21 ρ' hx; exact ⟨ρ'', h1, h2.trans e⟩
      simp only [ev]
      simp only [hC, hE]

theorem evList_congr {FS : FloatSem} :
    ∀ (l : List Term) (ρ1 ρ2 : Env),
      (∀ v ∈ Term.freeVarsList l, ρ1.var v = ρ2.var v) → evList FS ρ1 l = evList FS ρ2 l
  | [], _, _, _ => by simp only [evList]
  | t :: ts, ρ1, ρ2, hv => by
      simp only [evList]
      rw [ev_congr t ρ1 ρ2 (fun v h => hv v (by simp [Term.freeVarsList, h])),
        evList_congr ts ρ1 ρ2 (fun v h => hv v (by simp [Term.freeVarsList, h]))]
end

theorem Ty.WF.inhabited : ∀ {t : Ty}, t.WF → ∃ x : Val, x.hasTy t
  | .TBool, _ => ⟨.bool false, by simp [Val.hasTy, Val.hasSort]⟩
  | .TFloat p, _ => ⟨.float p 0, by simp [Val.hasTy, Val.hasSort]⟩
  | .TLoc n, h => ⟨.bv n.toNat 0, by simp [Val.hasTy, Val.hasSort, Ty.WF] at h ⊢; omega⟩
  | .TPointer n, h => ⟨.ptr n.toNat 0 0, by simp [Val.hasTy, Val.hasSort, Ty.WF] at h ⊢; omega⟩
  | .TSeq t, _ => ⟨.seq [], by simp [Val.hasTy, Val.hasSort, Val.hasSortList]⟩
  | .TBitVector n, h => ⟨.bv n.toNat 0, by simp [Val.hasTy, Val.hasSort, Ty.WF] at h ⊢; omega⟩

theorem binders_fst_inj : ∀ {bs : List (Int × Ty)}, (bs.map Prod.fst).Nodup →
    ∀ {b b' : Int × Ty}, b ∈ bs → b' ∈ bs → b.1 = b'.1 → b = b'
  | [], _, _, _, h, _, _ => by simp at h
  | a :: rest, hn, b, b', hb, hb', e => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    obtain ⟨ha, hn⟩ := hn
    rcases List.mem_cons.1 hb with rfl | hb1 <;> rcases List.mem_cons.1 hb' with rfl | hb2
    · rfl
    · exact absurd ⟨b', hb2, e.symm⟩ ha
    · exact absurd ⟨b, hb1, e⟩ ha
    · exact binders_fst_inj hn hb1 hb2 e

theorem binders_values : ∀ {bs : List (Int × Ty)}, (bs.map Prod.fst).Nodup → (∀ b ∈ bs, b.2.WF) →
    ∃ f : Int → Option Val, ∀ b ∈ bs, ∃ x, f b.1 = some x ∧ x.hasTy b.2
  | [], _, _ => ⟨fun _ => none, by simp⟩
  | a :: rest, hn, hw => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    obtain ⟨ha, hn⟩ := hn
    obtain ⟨f, hf⟩ := binders_values hn (fun b hb => hw b (List.mem_cons_of_mem _ hb))
    obtain ⟨x, hx⟩ := Ty.WF.inhabited (hw a (by simp))
    refine ⟨fun v => if v = a.1 then some x else f v, fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨x, by simp, hx⟩
    · have : b.1 ≠ a.1 := fun e => ha ⟨b, hb, e⟩
      simp only [this, ite_false]; exact hf b hb

theorem mem_used_binders {bs : List (Int × Ty)} {body : Term} {b : Int × Ty} :
    b ∈ used_binders bs body ↔ b ∈ bs ∧ b.1 ∈ body.freeVars := by
  simp [used_binders]

theorem ev_exists_used {FS : FloatSem} {ρ : Env} {bs : List (Int × Ty)} {body : Term} {T T' : Ty}
    (hn : (bs.map Prod.fst).Nodup) (hw : ∀ b ∈ bs, b.2.WF) :
    ev FS ρ (.mk (.Exists bs body) T) = ev FS ρ (.mk (.Exists (used_binders bs body) body) T') := by
  have kA : ∀ ρ' : Env, ρ'.Extends ρ bs →
      ∃ ρ'' : Env, ρ''.Extends ρ (used_binders bs body) ∧ ev FS ρ'' body = ev FS ρ' body := by
    intro ρ' h
    refine ⟨⟨fun v => if ∃ b ∈ used_binders bs body, b.1 = v then ρ'.var v else ρ.var v⟩,
      ⟨fun v hv => ?_, fun b hb => ?_⟩, ev_congr _ _ _ fun v hv => ?_⟩
    · have : ¬ ∃ b ∈ used_binders bs body, b.1 = v := fun ⟨b, hb, e⟩ => hv b hb e
      simp only [this, ite_false]
    · simp only [show ∃ b' ∈ used_binders bs body, b'.1 = b.1 from ⟨b, hb, rfl⟩, ite_true]
      exact h.2 b (mem_used_binders.1 hb).1
    · by_cases hc : ∃ b ∈ used_binders bs body, b.1 = v
      · simp [hc]
      · simp only [hc, ite_false]
        refine (h.1 v fun b hb e => hc ⟨b, mem_used_binders.2 ⟨hb, e ▸ hv⟩, e⟩).symm
  have kB : ∀ ρ'' : Env, ρ''.Extends ρ (used_binders bs body) →
      ∃ ρ' : Env, ρ'.Extends ρ bs ∧ ev FS ρ' body = ev FS ρ'' body := by
    intro ρ'' h
    obtain ⟨f, hf⟩ := binders_values hn hw
    refine ⟨⟨fun v => if ∃ b ∈ used_binders bs body, b.1 = v then ρ''.var v
        else if ∃ b ∈ bs, b.1 = v then f v else ρ.var v⟩,
      ⟨fun v hv => ?_, fun b hb => ?_⟩, ev_congr _ _ _ fun v hv => ?_⟩
    · have h1 : ¬ ∃ b ∈ used_binders bs body, b.1 = v :=
        fun ⟨b, hb, e⟩ => hv b (mem_used_binders.1 hb).1 e
      have h2 : ¬ ∃ b ∈ bs, b.1 = v := fun ⟨b, hb, e⟩ => hv b hb e
      simp only [h1, h2, ite_false]
    · by_cases hc : ∃ b' ∈ used_binders bs body, b'.1 = b.1
      · simp only [hc, ite_true]
        obtain ⟨b', hb', e⟩ := hc
        obtain rfl := binders_fst_inj hn (mem_used_binders.1 hb').1 hb e
        exact h.2 b' hb'
      · simp only [hc, show ∃ b' ∈ bs, b'.1 = b.1 from ⟨b, hb, rfl⟩, ite_false, ite_true]
        exact hf b hb
    · by_cases hc : ∃ b ∈ used_binders bs body, b.1 = v
      · simp [hc]
      · have h2 : ¬ ∃ b ∈ bs, b.1 = v :=
          fun ⟨b, hb, e⟩ => hc ⟨b, mem_used_binders.2 ⟨hb, e ▸ hv⟩, e⟩
        simp only [hc, h2, ite_false]
        exact (h.1 v fun b hb e => hc ⟨b, hb, e⟩).symm
  have hC : (∀ ρ' : Env, ρ'.Extends ρ bs → ∃ b, ev FS ρ' body = some (.bool b)) ↔
      (∀ ρ' : Env, ρ'.Extends ρ (used_binders bs body) → ∃ b, ev FS ρ' body = some (.bool b)) := by
    constructor
    · intro h ρ' hx; obtain ⟨ρ'', h1, h2⟩ := kB ρ' hx; rw [← h2]; exact h ρ'' h1
    · intro h ρ' hx; obtain ⟨ρ'', h1, h2⟩ := kA ρ' hx; rw [← h2]; exact h ρ'' h1
  have hE : (∃ ρ' : Env, ρ'.Extends ρ bs ∧ ev FS ρ' body = some (.bool true)) ↔
      (∃ ρ' : Env, ρ'.Extends ρ (used_binders bs body) ∧ ev FS ρ' body = some (.bool true)) := by
    constructor
    · rintro ⟨ρ', hx, e⟩; obtain ⟨ρ'', h1, h2⟩ := kA ρ' hx; exact ⟨ρ'', h1, h2.trans e⟩
    · rintro ⟨ρ', hx, e⟩; obtain ⟨ρ'', h1, h2⟩ := kB ρ' hx; exact ⟨ρ'', h1, h2.trans e⟩
  simp only [ev]
  simp only [hC, hE]

theorem extends_nil {ρ ρ' : Env} : ρ'.Extends ρ [] ↔ ρ' = ρ := by
  constructor
  · rintro ⟨hv, -⟩
    rcases ρ with ⟨v⟩; rcases ρ' with ⟨v'⟩
    simp only [Env.mk.injEq] at hv ⊢
    exact funext fun a => hv a (by simp)
  · rintro rfl; exact ⟨fun _ _ => rfl, by simp⟩

end Kanon.Lib
