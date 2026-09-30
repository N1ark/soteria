import Bvr.Lib.Float
import Bvr.Lib.Tactic

/-!
# Lemmas and tactics for the boolean rules
-/

namespace Bvr.Lib

open Classical

/-! ## Bounds -/

@[simp] theorem upper_bound_lt {s a z T T'} :
    upper_bound (.mk (.Binop (.Lt s) a (.mk (.BitVec z) T)) T') =
      to_z s (bv_of_lit (.mk (.BitVec z) T)) - 1 := by
  simp [upper_bound, firstSome]
@[simp] theorem upper_bound_leq {s a z T T'} :
    upper_bound (.mk (.Binop (.Leq s) a (.mk (.BitVec z) T)) T') =
      to_z s (bv_of_lit (.mk (.BitVec z) T)) := by
  simp [upper_bound, firstSome]
@[simp] theorem lower_bound_lt {s a z T T'} :
    lower_bound (.mk (.Binop (.Lt s) (.mk (.BitVec z) T) a) T') =
      to_z s (bv_of_lit (.mk (.BitVec z) T)) + 1 := by
  simp [lower_bound, firstSome]
@[simp] theorem lower_bound_leq {s a z T T'} :
    lower_bound (.mk (.Binop (.Leq s) (.mk (.BitVec z) T) a) T') =
      to_z s (bv_of_lit (.mk (.BitVec z) T)) := by
  simp [lower_bound, firstSome]

/-- Closes the comparisons of bit-vectors, as integers. -/
macro "bvr_int_cmp" : tactic => `(tactic| (
  (try bvr_split)
  (try simp only [BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle, decide_eq_true_eq,
    decide_eq_false_iff_not, Bool.not_eq_true, Bool.not_eq_false, Bool.or_eq_true,
    Bool.and_eq_true] at *)
  (try simp (disch := assumption) only [emod_two_pow_of_lt] at *)
  first
    | ((try simp only [← BitVec.toNat_inj] at *)
       (try simp (disch := assumption) only [toNat_ofInt_of_lt] at *)
       omega)
    | ((try simp only [← BitVec.toInt_inj, BitVec.toInt_ofInt] at *)
       omega)))

/-- `bvr_rule` for the rules on bounds: reads the bounds, and closes the
comparisons as integers. -/
macro "bvr_rule_bounds" : tactic => `(tactic| (
  bvr_rule_core
  all_goals (try simp only [upper_bound_lt, upper_bound_leq, lower_bound_lt, lower_bound_leq] at *)
  all_goals first | (bvr_wt; done) | bvr_sem_core
  all_goals bvr_int_cmp))

/-! ## Adjacent extractions -/

/-- The concatenation of two adjacent extractions of `x` is their union. -/

theorem concat_eq_extract {w p q n : Nat} {x : BitVec w} {a : BitVec p} {b : BitVec q}
    {i j : Nat} (hn : n = q + p) (hj : j = i + p) :
    (b ++ a).setWidth n = x.extractLsb' i n ↔ a = x.extractLsb' i p ∧ b = x.extractLsb' j q := by
  subst hn hj
  rw [BitVec.setWidth_eq]
  constructor
  · intro h
    constructor
    · apply BitVec.eq_of_getElem_eq; intro k hk
      have := congrArg (·[k]'(by omega)) h
      simp [BitVec.getElem_append, hk] at this
      simp [this]
    · apply BitVec.eq_of_getElem_eq; intro k hk
      have := congrArg (·[k + p]'(by omega)) h
      simp only [BitVec.getElem_append, show ¬ k + p < p by omega, dite_false,
        Nat.add_sub_cancel] at this
      simp [this, Nat.add_comm k p, Nat.add_assoc]
  · rintro ⟨rfl, rfl⟩
    apply BitVec.eq_of_getElem_eq; intro k hk
    simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
    split
    · rfl
    · simp only [BitVec.getLsbD_eq_getElem?_getD]
      rw [show i + p + (k - p) = i + k by omega]

theorem concat_eq_extract_of {w p q n : Nat} {x : BitVec w} {a : BitVec p} {b : BitVec q}
    {i j : Nat} (ha : a = x.extractLsb' i p) (hb : b = x.extractLsb' j q) (hn : n = q + p)
    (hj : j = i + p) : (b ++ a).setWidth n = x.extractLsb' i n :=
  (concat_eq_extract hn hj).2 ⟨ha, hb⟩

theorem concat_ne_extract {w p q n : Nat} {x : BitVec w} {a : BitVec p} {b : BitVec q}
    {i j : Nat} (h : a = x.extractLsb' i p → ¬ b = x.extractLsb' j q) (hn : n = q + p)
    (hj : j = i + p) : ¬ (b ++ a).setWidth n = x.extractLsb' i n :=
  fun e => h ((concat_eq_extract hn hj).1 e).1 ((concat_eq_extract hn hj).1 e).2

theorem concat_ne_extract' {w p q n : Nat} {x : BitVec w} {a : BitVec p} {b : BitVec q}
    {i j : Nat} (h : b = x.extractLsb' j q → ¬ a = x.extractLsb' i p) (hn : n = q + p)
    (hj : j = i + p) : ¬ (b ++ a).setWidth n = x.extractLsb' i n :=
  fun e => h ((concat_eq_extract hn hj).1 e).2 ((concat_eq_extract hn hj).1 e).1

/-! ## `sure_neq` -/

theorem getD_firstSome_orElse {α} {o : Option α} {l : List (Option α)} {d : α} :
    (firstSome (o :: l)).getD d = match o with | some x => x | none => (firstSome l).getD d := by
  cases o <;> simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

theorem sure_neq_cases {a b : Term} (h : sure_neq a b = true) :
    a.ty ≠ b.ty ∨
    (∃ za zb Ta Tb, a = .mk (.BitVec za) Ta ∧ b = .mk (.BitVec zb) Tb ∧ za ≠ zb) ∨
    (∃ fa fb Ta Tb, a = .mk (.Float fa) Ta ∧ b = .mk (.Float fb) Tb ∧ fa ≠ fb) ∨
    (∃ ba bb Ta Tb, a = .mk (.Bool ba) Ta ∧ b = .mk (.Bool bb) Tb ∧ ba ≠ bb) ∨
    (∃ la oa lb ob Ta Tb, a = .mk (.Ptr la oa) Ta ∧ b = .mk (.Ptr lb ob) Tb ∧
      (sure_neq la lb = true ∨ sure_neq oa ob = true)) := by
  unfold sure_neq at h
  simp only [getD_firstSome_orElse, Bool.or_eq_true, Bool.not_eq_true', ty_eq] at h
  rcases h with h | h
  · left; exact of_decide_eq_false h
  right
  rcases a with ⟨ka, Ta⟩; rcases b with ⟨kb, Tb⟩
  cases ka <;> cases kb <;> simp [firstSome, f_equal] at h ⊢ <;>
    first | assumption | exact ⟨_, _, ⟨rfl, rfl⟩, _, _, ⟨rfl, rfl⟩, h⟩

theorem sure_neq_sound_aux {FS : FloatSem} (k : Nat) : ∀ {a b : Term} {ρ : Env} {u : Val},
    sizeOf a < k → sure_neq a b = true →
    a.ty = b.ty → eval FS ρ a = some u → eval FS ρ b = some u → False := by
  induction k with
  | zero => intros; omega
  | succ k ih =>
    intro a b ρ u hk h ht ea eb
    rcases sure_neq_cases h with h | ⟨za, zb, Ta, Tb, rfl, rfl, hz⟩ |
      ⟨fa, fb, Ta, Tb, rfl, rfl, hf⟩ | ⟨ba, bb, Ta, Tb, rfl, rfl, hb⟩ |
      ⟨la, oa, lb, ob, Ta, Tb, rfl, rfl, hp⟩
    · exact h ht
    · simp only [Term.ty_mk] at ht; subst ht
      have wa := eval_WT ea; have wb := eval_WT eb
      obtain ⟨n, hn, hT, h0, h1⟩ := WT_bitVec.1 wa
      obtain ⟨n', hn', hT', h0', h1'⟩ := WT_bitVec.1 wb
      have : n' = n := by
        rcases hT with rfl | rfl <;> rcases hT' with h | h <;> simp at h <;> omega
      subst this
      rw [eval_bitVec' wa hT] at ea; rw [eval_bitVec' wb hT, ← ea] at eb
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
      obtain ⟨m, -, hTa, hla', hoa', -, -⟩ := eval_WT ea
      obtain ⟨m', -, hTb, hlb', hob', -, -⟩ := eval_WT eb
      simp only [Term.ty_mk] at ht; rw [hTa, hTb] at ht; simp only [Ty.TPointer.injEq] at ht
      subst ht
      simp only [Ty.sort_eq] at *
      rcases hp with hp | hp
      · exact ih (by simp at hk; omega) hp (hla'.trans hlb'.symm) hla hlb
      · exact ih (by simp at hk; omega) hp (hoa'.trans hob'.symm) hoa hob

theorem sure_neq_sound {FS : FloatSem} {a b : Term} {ρ : Env} {u : Val} (h : sure_neq a b = true)
    (ht : a.ty = b.ty) (ea : eval FS ρ a = some u) (eb : eval FS ρ b = some u) : False :=
  sure_neq_sound_aux (sizeOf a + 1) (Nat.lt_succ_self _) h ht ea eb

theorem Refines.and_eq_neq {FS p1 q1 p2 q2 x y a T1 T2 T}
    (o1 : (p1 = a ∧ q1 = x) ∨ (p1 = x ∧ q1 = a)) (o2 : (p2 = a ∧ q2 = y) ∨ (p2 = y ∧ q2 = a))
    (hn : sure_neq x y = true) :
    Refines FS (.mk (.Binop .And (.mk (.Binop .Eq p1 q1) T1) (.mk (.Binop .Eq p2 q2) T2)) T)
      v_false := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · have := (WT_binop.1 w).1; simp [Binop.WT] at this; simp [v_false, this, WT_bool]
  obtain ⟨-, w1, w2⟩ := WT_binop.1 w
  obtain ⟨h1, -, -⟩ := WT_binop.1 w1
  obtain ⟨h2, -, -⟩ := WT_binop.1 w2
  simp only [Binop.WT, Ty.sort_eq] at h1 h2
  rw [eval_binop w, eval_binop w1, eval_binop w2] at e
  rw [v_false, eval_bool rfl]
  have k := fun u => sure_neq_sound (FS := FS) (ρ := ρ) (u := u) hn
  rcases o1 with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases o2 with ⟨_, _⟩ | ⟨_, _⟩ <;> subst p1 q1 p2 q2 <;>
    cases eval FS ρ a <;> cases hx : eval FS ρ x <;> cases hy : eval FS ρ y <;>
    simp [evBinop, pand] at e <;> grind

/-- Proves `a == x && a == y` (with the equalities in either order) refines
`false`, for `x` and `y` surely different. -/
macro "bvr_and_eq_neq" : tactic => `(tactic| (
  intro FS O hO
  intros
  bvr_flags
  bvr_split
  subst_vars
  simp only [bvr_spec] at *
  first
    | exact Refines.and_eq_neq (.inl ⟨rfl, rfl⟩) (.inl ⟨rfl, rfl⟩) ‹_›
    | exact Refines.and_eq_neq (.inl ⟨rfl, rfl⟩) (.inr ⟨rfl, rfl⟩) ‹_›
    | exact Refines.and_eq_neq (.inr ⟨rfl, rfl⟩) (.inl ⟨rfl, rfl⟩) ‹_›
    | exact Refines.and_eq_neq (.inr ⟨rfl, rfl⟩) (.inr ⟨rfl, rfl⟩) ‹_›))

/-! ## `distinct` -/

theorem equal_iff {a b : Term} : equal a b = true ↔ a = b := by simp [equal]

theorem WTList_iff {e : Ty} : ∀ {l : List Term}, Term.WTList e l ↔ ∀ t ∈ l, t.ty = e ∧ t.WT
  | [] => by simp [Term.WTList]
  | t :: ts => by simp [Term.WTList, WTList_iff (l := ts), and_assoc]

/-- The value of a term that evaluates (a default otherwise). -/
noncomputable def evD (FS : FloatSem) (ρ : Env) (t : Term) : Val := (ev FS ρ t).getD (.bool false)

theorem evList_eq_some {FS : FloatSem} {ρ : Env} : ∀ {l : List Term} {vs : List Val},
    evList FS ρ l = some vs ↔ (∀ t ∈ l, ∃ v, ev FS ρ t = some v) ∧ vs = l.map (evD FS ρ)
  | [], vs => by simp [evList]
  | t :: ts, vs => by
    simp only [evList]
    constructor
    · intro h
      split at h
      · rename_i v vs' hv hvs
        cases h
        obtain ⟨h1, h2⟩ := evList_eq_some.1 hvs
        refine ⟨?_, ?_⟩
        · intro t' ht'
          rcases List.mem_cons.1 ht' with rfl | ht'
          · exact ⟨v, hv⟩
          · exact h1 t' ht'
        · simp [h2, evD, hv]
      · cases h
    · rintro ⟨h1, rfl⟩
      obtain ⟨v, hv⟩ := h1 t (by simp)
      have := evList_eq_some (l := ts) (vs := ts.map (evD FS ρ)) |>.2
        ⟨fun t' ht' => h1 t' (by simp [ht']), rfl⟩
      rw [hv, this]; simp [evD, hv]

theorem distinct_check_one_true {a : Term} : ∀ {rest : List Term},
    distinct_check_one a rest = some true → ∀ b ∈ rest, sure_neq a b = true
  | [], _ => by simp
  | b :: rest, h => by
    rw [distinct_check_one] at h
    simp only [firstSome, Option.getD_some, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at h
    split at h
    · simp at h
    · split at h
      · rename_i hs
        intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact hs
        · exact distinct_check_one_true h c hc
      · simp at h

theorem distinct_check_one_false {a : Term} : ∀ {rest : List Term},
    distinct_check_one a rest = some false → a ∈ rest
  | [], h => by rw [distinct_check_one] at h; simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at h
  | b :: rest, h => by
    rw [distinct_check_one] at h
    simp only [firstSome, Option.getD_some, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at h
    split at h
    · rename_i he; simp [equal_iff] at he; simp [he]
    · split at h
      · exact List.mem_cons_of_mem _ (distinct_check_one_false h)
      · simp at h

theorem distinct_check_true : ∀ {l : List Term},
    distinct_check l = some true → l.Pairwise (fun a b => sure_neq a b = true)
  | [], _ => by simp
  | a :: rest, h => by
    rw [distinct_check] at h
    simp only [firstSome, Option.getD_some, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at h
    cases h1 : distinct_check_one a rest with
    | none => simp [h1] at h
    | some b =>
      cases b
      · simp [h1] at h
      · simp only [h1] at h
        exact List.Pairwise.cons (distinct_check_one_true h1) (distinct_check_true h)

theorem distinct_check_false : ∀ {l : List Term}, distinct_check l = some false → ¬ l.Nodup
  | [], h => by rw [distinct_check] at h; simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at h
  | a :: rest, h => by
    rw [distinct_check] at h
    simp only [firstSome, Option.getD_some, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at h
    cases h1 : distinct_check_one a rest with
    | none => simp [h1] at h
    | some b =>
      cases b
      · have := distinct_check_one_false h1
        simp [this]
      · simp only [h1] at h
        have := distinct_check_false h
        simp [this]

theorem eval_distinct_eq_some {FS ρ l v} (e : eval FS ρ (b_distinct.spec l) = some v) :
    (∃ E, ∀ t ∈ l, t.ty = E ∧ t.WT) ∧ (∀ t ∈ l, ∃ v, ev FS ρ t = some v) ∧
      v = .bool (decide (l.map (evD FS ρ)).Nodup) := by
  have w := eval_WT e
  rw [eval_eq_ev w] at e
  simp only [b_distinct.spec, Term.WT] at w
  obtain ⟨-, E, wl⟩ := w
  simp only [b_distinct.spec, ev] at e
  cases hv : evList FS ρ l with
  | none => simp [hv] at e
  | some vs =>
    obtain ⟨hall, rfl⟩ := evList_eq_some.1 hv
    simp [hv] at e
    exact ⟨⟨E, WTList_iff.1 wl⟩, hall, e.symm⟩

/-! ## `exists` -/

theorem mem_freeVars_exists {bs : List (Int × Ty)} {body : Term} {T : Ty} {v : Int} :
    v ∈ (Term.mk (.Exists bs body) T).freeVars ↔ v ∈ body.freeVars ∧ ∀ b ∈ bs, b.1 ≠ v := by
  simp [Term.freeVars]

/-- Moving an extension of [ρa] to one of [ρb], where they agree on the free variables. -/
theorem extends_transfer {bs : List (Int × Ty)} {P : Int → Prop} {ρa ρb ρ' : Env}
    (he : ρa.ext = ρb.ext) (hv : ∀ v, P v → (∀ b ∈ bs, b.1 ≠ v) → ρa.var v = ρb.var v)
    (h : ρ'.Extends ρa bs) :
    ∃ ρ'' : Env, ρ''.Extends ρb bs ∧ ρ''.ext = ρ'.ext ∧ ∀ v, P v → ρ''.var v = ρ'.var v := by
  refine ⟨⟨fun v => if ∃ b ∈ bs, b.1 = v then ρ'.var v else ρb.var v, ρ'.ext⟩,
    ⟨by rw [h.1, he], fun v hn => ?_, fun b hb => ?_⟩, rfl, fun v hP => ?_⟩
  · have : ¬ ∃ b ∈ bs, b.1 = v := fun ⟨b, hb, e⟩ => hn b hb e
    simp only [this, ite_false]
  · simp only [show ∃ b' ∈ bs, b'.1 = b.1 from ⟨b, hb, rfl⟩, ite_true]; exact h.2.2 b hb
  · by_cases hc : ∃ b ∈ bs, b.1 = v
    · simp [hc]
    · have hn : ∀ b ∈ bs, b.1 ≠ v := fun b hb e => hc ⟨b, hb, e⟩
      simp only [hc, ite_false]; rw [h.2.1 v hn, hv v hP hn]

mutual

theorem ev_congr {FS : FloatSem} :
    ∀ (t : Term) (ρ1 ρ2 : Env), ρ1.ext = ρ2.ext → (∀ v ∈ t.freeVars, ρ1.var v = ρ2.var v) →
      ev FS ρ1 t = ev FS ρ2 t
  | .mk (.Var x) T, ρ1, ρ2, _, hv => by
      simp only [ev]; rw [hv x (by simp [Term.freeVars])]
  | .mk (.Bool b) T, ρ1, ρ2, _, _ => by simp only [ev]
  | .mk (.Float f) T, ρ1, ρ2, _, _ => by simp only [ev]
  | .mk (.BitVec z) T, ρ1, ρ2, _, _ => by simp only [ev]
  | .mk (.Ptr l o) T, ρ1, ρ2, he, hv => by
      simp only [ev]
      rw [ev_congr l ρ1 ρ2 he (fun v h => hv v (by simp [Term.freeVars, h])),
        ev_congr o ρ1 ρ2 he (fun v h => hv v (by simp [Term.freeVars, h]))]
  | .mk (.Seq l) T, ρ1, ρ2, he, hv => by
      simp only [ev]
      rw [evList_congr l ρ1 ρ2 he (fun v h => hv v (by simpa [Term.freeVars] using h))]
  | .mk (.Unop op a) T, ρ1, ρ2, he, hv => by
      simp only [ev]
      rw [ev_congr a ρ1 ρ2 he (fun v h => hv v (by simpa [Term.freeVars] using h))]
  | .mk (.Binop op a b) T, ρ1, ρ2, he, hv => by
      simp only [ev]
      rw [ev_congr a ρ1 ρ2 he (fun v h => hv v (by simp [Term.freeVars, h])),
        ev_congr b ρ1 ρ2 he (fun v h => hv v (by simp [Term.freeVars, h]))]
  | .mk (.Triop op g a b) T, ρ1, ρ2, he, hv => by
      have hg := ev_congr (FS := FS) g ρ1 ρ2 he (fun v h => hv v (by simp [Term.freeVars, h]))
      have ha := ev_congr (FS := FS) a ρ1 ρ2 he (fun v h => hv v (by simp [Term.freeVars, h]))
      have hb := ev_congr (FS := FS) b ρ1 ρ2 he (fun v h => hv v (by simp [Term.freeVars, h]))
      cases op <;> simp only [ev] <;> rw [hg, ha, hb]
  | .mk (.Nop op l) T, ρ1, ρ2, he, hv => by
      cases op
      simp only [ev]
      rw [evList_congr l ρ1 ρ2 he (fun v h => hv v (by simpa [Term.freeVars] using h))]
  | .mk (.Exists bs body) T, ρ1, ρ2, he, hv => by
      have key : ∀ ρa ρb : Env, ρa.ext = ρb.ext →
          (∀ v, v ∈ body.freeVars → (∀ b ∈ bs, b.1 ≠ v) → ρa.var v = ρb.var v) →
          ∀ ρ' : Env, ρ'.Extends ρa bs →
            ∃ ρ'' : Env, ρ''.Extends ρb bs ∧ ev FS ρ'' body = ev FS ρ' body := by
        intro ρa ρb hab hvab ρ' hext
        obtain ⟨ρ'', h1, h2, h3⟩ := extends_transfer (P := (· ∈ body.freeVars)) hab hvab hext
        exact ⟨ρ'', h1, ev_congr body ρ'' ρ' h2 h3⟩
      have hv' : ∀ v, v ∈ body.freeVars → (∀ b ∈ bs, b.1 ≠ v) → ρ1.var v = ρ2.var v :=
        fun v h1 h2 => hv v (mem_freeVars_exists.2 ⟨h1, h2⟩)
      have k12 := key ρ1 ρ2 he hv'
      have k21 := key ρ2 ρ1 he.symm (fun v h1 h2 => (hv' v h1 h2).symm)
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
  | .mk (.Extension x) T, ρ1, ρ2, he, _ => by simp only [ev]; rw [he]

theorem evList_congr {FS : FloatSem} :
    ∀ (l : List Term) (ρ1 ρ2 : Env), ρ1.ext = ρ2.ext →
      (∀ v ∈ Term.freeVarsList l, ρ1.var v = ρ2.var v) → evList FS ρ1 l = evList FS ρ2 l
  | [], _, _, _, _ => by simp only [evList]
  | t :: ts, ρ1, ρ2, he, hv => by
      simp only [evList]
      rw [ev_congr t ρ1 ρ2 he (fun v h => hv v (by simp [Term.freeVarsList, h])),
        evList_congr ts ρ1 ρ2 he (fun v h => hv v (by simp [Term.freeVarsList, h]))]
end

theorem Ty.WF.inhabited : ∀ {t : Ty}, t.WF → ∃ x : Val, x.hasTy t
  | .TBool, _ => ⟨.bool false, by simp [Val.hasTy, Val.hasSort]⟩
  | .TFloat p, _ => ⟨.float p 0, by simp [Val.hasTy, Val.hasSort]⟩
  | .TLoc n, h => ⟨.bv n.toNat 0, by simp [Val.hasTy, Val.hasSort, Ty.WF] at h ⊢; omega⟩
  | .TPointer n, h => ⟨.ptr n.toNat 0 0, by simp [Val.hasTy, Val.hasSort, Ty.WF] at h ⊢; omega⟩
  | .TSeq t, _ => ⟨.seq [], by simp [Val.hasTy, Val.hasSort, Val.hasSortList]⟩
  | .TBitVector n, h => ⟨.bv n.toNat 0, by simp [Val.hasTy, Val.hasSort, Ty.WF] at h ⊢; omega⟩
  | .TExtension e, _ => ⟨.ext 0, by simp [Val.hasTy, Val.hasSort]⟩

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
    refine ⟨⟨fun v => if ∃ b ∈ used_binders bs body, b.1 = v then ρ'.var v else ρ.var v, ρ'.ext⟩,
      ⟨h.1, fun v hv => ?_, fun b hb => ?_⟩, ev_congr _ _ _ rfl fun v hv => ?_⟩
    · have : ¬ ∃ b ∈ used_binders bs body, b.1 = v := fun ⟨b, hb, e⟩ => hv b hb e
      simp only [this, ite_false]
    · simp only [show ∃ b' ∈ used_binders bs body, b'.1 = b.1 from ⟨b, hb, rfl⟩, ite_true]
      exact h.2.2 b (mem_used_binders.1 hb).1
    · by_cases hc : ∃ b ∈ used_binders bs body, b.1 = v
      · simp [hc]
      · simp only [hc, ite_false]
        refine (h.2.1 v fun b hb e => hc ⟨b, mem_used_binders.2 ⟨hb, e ▸ hv⟩, e⟩).symm
  have kB : ∀ ρ'' : Env, ρ''.Extends ρ (used_binders bs body) →
      ∃ ρ' : Env, ρ'.Extends ρ bs ∧ ev FS ρ' body = ev FS ρ'' body := by
    intro ρ'' h
    obtain ⟨f, hf⟩ := binders_values hn hw
    refine ⟨⟨fun v => if ∃ b ∈ used_binders bs body, b.1 = v then ρ''.var v
        else if ∃ b ∈ bs, b.1 = v then f v else ρ.var v, ρ.ext⟩,
      ⟨rfl, fun v hv => ?_, fun b hb => ?_⟩, ev_congr _ _ _ h.1.symm fun v hv => ?_⟩
    · have h1 : ¬ ∃ b ∈ used_binders bs body, b.1 = v :=
        fun ⟨b, hb, e⟩ => hv b (mem_used_binders.1 hb).1 e
      have h2 : ¬ ∃ b ∈ bs, b.1 = v := fun ⟨b, hb, e⟩ => hv b hb e
      simp only [h1, h2, ite_false]
    · by_cases hc : ∃ b' ∈ used_binders bs body, b'.1 = b.1
      · simp only [hc, ite_true]
        obtain ⟨b', hb', e⟩ := hc
        obtain rfl := binders_fst_inj hn (mem_used_binders.1 hb').1 hb e
        exact h.2.2 b' hb'
      · simp only [hc, show ∃ b' ∈ bs, b'.1 = b.1 from ⟨b, hb, rfl⟩, ite_false, ite_true]
        exact hf b hb
    · by_cases hc : ∃ b ∈ used_binders bs body, b.1 = v
      · simp [hc]
      · have h2 : ¬ ∃ b ∈ bs, b.1 = v :=
          fun ⟨b, hb, e⟩ => hc ⟨b, mem_used_binders.2 ⟨hb, e ▸ hv⟩, e⟩
        simp only [hc, h2, ite_false]
        exact (h.2.1 v fun b hb e => hc ⟨b, hb, e⟩).symm
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
  · rintro ⟨he, hv, -⟩
    rcases ρ with ⟨v, x⟩; rcases ρ' with ⟨v', x'⟩
    simp only [Env.mk.injEq] at he hv ⊢
    exact ⟨funext fun a => hv a (by simp), he⟩
  · rintro rfl; exact ⟨rfl, fun _ _ => rfl, by simp⟩

theorem WT_exists {bs body T} : (Term.mk (.Exists bs body) T).WT ↔
    T = .TBool ∧ (bs.map Prod.fst).Nodup ∧ (∀ b ∈ bs, b.2.WF) ∧ body.ty = .TBool ∧ body.WT := by
  simp [Term.WT]

/-! ## Rules that hold at any type, by evaluation -/

theorem evUnop_not_eq_bool {FS a b} : evUnop FS .Not a = some (.bool b) ↔ a = some (.bool !b) := by
  rcases a with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> simp [evUnop] <;> grind
theorem pand_eq_true {a b} : pand a b = some (.bool true) ↔
    a = some (.bool true) ∧ b = some (.bool true) := by
  rcases a with _ | ⟨⟨_ | _⟩ | _ | _ | _ | _ | _⟩ <;>
    rcases b with _ | ⟨⟨_ | _⟩ | _ | _ | _ | _ | _⟩ <;> simp [pand]
theorem por_eq_false {a b} : por a b = some (.bool false) ↔
    a = some (.bool false) ∧ b = some (.bool false) := by
  rcases a with _ | ⟨⟨_ | _⟩ | _ | _ | _ | _ | _⟩ <;>
    rcases b with _ | ⟨⟨_ | _⟩ | _ | _ | _ | _ | _⟩ <;> simp [por]

/-- `bvr_rule` for the rules that hold at any type: the value half is proved
by evaluation (`ev`), splitting on the guards of the `ite`s. -/
macro "bvr_rule_ev" : tactic => `(tactic| (
  bvr_rule_lift
  all_goals refine Refines.intro ?_ (fun ρ v w w' e => ?_)
  case' refine_1 => simp only [Ty.sort_eq]; bvr_wt
  case' refine_2 =>
    rw [eval_eq_ev w] at e
    rw [eval_eq_ev w']
    simp only [ev] at e ⊢
    repeat' split at e
    all_goals simp_all [evBinop, evUnop_not_eq_bool, pand_eq_true, por_eq_false]))

/-- `bvr_rule`, for the rules whose spec is a boolean (resp. bit-vector) at a
type that its typing determines. -/
macro "bvr_rule_typed" : tactic => `(tactic| (
  bvr_rule_lift
  all_goals first
    | (refine Refines.denB ?_ ?_ ?_
       · intro w; bvr_facts; all_goals first | rfl | simp_all)
    | (refine Refines.den ?_ ?_ ?_
       · intro w; bvr_facts; all_goals first | exact ⟨_, rfl⟩ | simp_all)
  all_goals first
    | (bvr_wt; done)
    | (bvr_sem_core; all_goals bvr_bool_vars; all_goals simp_all; done)
    | bvr_sem
    | skip))

end Bvr.Lib
