import Kanon.Semantics
import ExistsMod.Prims

/-!
# The values of the sorts, and the free variables

Well-typed terms evaluate to values of their sort (`ev_ty`), by induction on
terms, in every environment (an `Exists` evaluates its body in others), and
from it the `Typed` instances of the modules.

The exists module needs the language to give the binders that occur free in a
term (`used_binders`), and to prove that an `Exists` does not depend on the
others (`ExistsMod.Laws`): the value of a term depends on its free variables
only (`ev_local`), as option B proved of its terms.
-/

noncomputable section

namespace Kanon

open Classical

theorem toNat_cast {n : Int} (h : 0 < n) : ((n.toNat : Nat) : Int) = n := Int.toNat_of_nonneg (by omega)

theorem bv_of {n : Int} (h : 0 < n) (x : BitVec n.toNat) :
    (Val.bv n.toNat x).Of (.bitvec (.TBitVector n)) := ⟨by omega, .inl (by rw [toNat_cast h])⟩

/-- A bit-vector of the sort of bit-vectors of width `n` is of width `n`. -/
theorem bv_width {m : Nat} {x : BitVec m} {n : Int} (h : (Val.bv m x).Of (.bitvec (.TBitVector n))) :
    (m : Int) = n := by
  obtain ⟨-, h | h⟩ := h <;> cases h; rfl

open BitvecMod in
theorem bitvec_ty (ρ : Env) (n : BitvecMod.Node Term) (t : Ty) (v : Val)
    (wt : BitvecMod.Node.wt Ty.bool Ty.core Ty.bitvec Term.ty n t)
    (ih : ∀ c ∈ n.children, ∀ v, ev ρ c = some v → v.Of c.ty)
    (h : BitvecMod.Node.eval (D := dom) ρ t (n.map (fun c ρ => ev ρ c)) = some v) : v.Of t := by
  cases n <;> simp only [BitvecMod.Node.wt, BitvecMod.Node.map, BitvecMod.Node.eval] at wt h
  all_goals first
    | (obtain ⟨⟨n, hn, ha⟩, -, ht⟩ := wt; rw [ha] at ht; subst ht
       simp only [ofBV, Option.map_eq_some_iff] at h; obtain ⟨x, -, rfl⟩ := h; exact bv_of hn x)
    | (obtain ⟨⟨n, hn, ha⟩, ht⟩ := wt; rw [ha] at ht; subst ht
       simp only [ofBV, Option.map_eq_some_iff] at h; obtain ⟨x, -, rfl⟩ := h; exact bv_of hn x)
    | (obtain ⟨-, -, rfl⟩ := wt
       rw [withW_eq_some] at h; simp only [ofB, Option.map_eq_some_iff] at h
       obtain ⟨_, _, -, _, -, rfl⟩ := h; rfl)
    | skip
  · obtain ⟨⟨n, hn, rfl⟩, -⟩ := wt
    simp only [ofBV, Option.map_eq_some_iff] at h; obtain ⟨x, -, rfl⟩ := h; exact bv_of hn _
  · obtain ⟨⟨n, hn, rfl⟩, -⟩ := wt
    simp only [ofBV, Option.map_eq_some_iff] at h; obtain ⟨x, -, rfl⟩ := h
    exact ⟨show 0 < n.toNat by omega, .inr (by
      show Ty.bitvec (.TLoc n) = Ty.bitvec (.TLoc ((n.toNat : Nat) : Int)); rw [toNat_cast hn])⟩
  · obtain ⟨hn, -, rfl⟩ := wt
    simp only [ofBV, Option.map_eq_some_iff] at h; obtain ⟨x, -, rfl⟩ := h; exact bv_of hn x
  · rename_i i j a
    obtain ⟨n, -, h0, h1, h2, rfl⟩ := wt
    rw [withW_eq_some] at h; simp only [ofBV, Option.map_eq_some_iff] at h
    obtain ⟨_, _, -, x, -, rfl⟩ := h; exact bv_of (by omega) x
  · rename_i s k a
    obtain ⟨n, hn, ha, hk, rfl⟩ := wt
    rw [withW_eq_some] at h; simp only [ofBV, Option.map_eq_some_iff] at h
    obtain ⟨m, y, hy, x, -, rfl⟩ := h
    have := bv_width (ha ▸ ih a (by simp [BitvecMod.Node.children]) _ hy)
    refine ⟨?_, .inl ?_⟩ <;> dsimp only at * <;>
      (try simp only [Ty.bitvec.injEq, BitvecMod.Srt.TBitVector.injEq]) <;> omega
  · rename_i a b
    obtain ⟨n, m, hn, hm, ha, hb, rfl⟩ := wt
    rw [withW_eq_some] at h; obtain ⟨n', y, hy, h⟩ := h
    rw [withW_eq_some] at h; obtain ⟨m', z, hz, h⟩ := h
    simp only [ofBV, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    have h1 := bv_width (ha ▸ ih a (by simp [BitvecMod.Node.children]) _ hy)
    have h2 := bv_width (hb ▸ ih b (by simp [BitvecMod.Node.children]) _ hz)
    refine ⟨?_, .inl ?_⟩ <;> dsimp only at * <;>
      (try simp only [Ty.bitvec.injEq, BitvecMod.Srt.TBitVector.injEq]) <;> omega

open FloatMod in
theorem float_ty (ρ : Env) (n : FloatMod.Node Term) (t : Ty) (v : Val)
    (wt : FloatMod.Node.wt Ty.bool Ty.core Ty.bitvec Ty.float Term.ty n t)
    (ih : ∀ c ∈ n.children, ∀ v, ev ρ c = some v → v.Of c.ty)
    (h : FloatMod.Node.eval (D := dom) ρ t (n.map (fun c ρ => ev ρ c)) = some v) : v.Of t := by
  cases n <;> simp only [FloatMod.Node.wt, FloatMod.Node.map, FloatMod.Node.eval, fUn, fArith,
    fCmp, fPred, fBin] at wt h
  all_goals first
    -- at the sort of the first operand
    | (rename_i a _ _; obtain ⟨-, -, -, ht⟩ := wt
       rw [withF_eq_some] at h; obtain ⟨q, x, hx, h⟩ := h
       simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
       obtain ⟨_, -, _, -, rfl⟩ := h
       show t = _; rw [ht]; exact ih a (by simp [FloatMod.Node.children]) _ hx)
    | (rename_i a _; obtain ⟨-, -, ht⟩ := wt
       rw [withF_eq_some] at h; obtain ⟨q, x, hx, h⟩ := h
       simp only [Option.bind_eq_some_iff] at h
       obtain ⟨_, -, h⟩ := h; cases h
       show t = _; rw [ht]; exact ih a (by simp [FloatMod.Node.children]) _ hx)
    | (rename_i a; obtain ⟨-, ht⟩ := wt
       rw [withF_eq_some] at h; obtain ⟨q, x, hx, h⟩ := h; cases h
       show t = _; rw [ht]; exact ih a (by simp [FloatMod.Node.children]) _ hx)
    | (rename_i a; obtain ⟨-, rfl⟩ := wt
       rw [withF_eq_some] at h; obtain ⟨_, _, -, h⟩ := h; cases h; rfl)
    | (obtain ⟨-, -, rfl⟩ := wt
       rw [withF_eq_some] at h; obtain ⟨_, _, -, h⟩ := h
       simp only [Option.bind_eq_some_iff] at h
       obtain ⟨_, -, h⟩ := h; cases h; rfl)
    | skip
  · obtain ⟨rfl, -⟩ := wt; cases h; rfl
  · rename_i _ _ n _
    obtain ⟨hn, -, rfl⟩ := wt
    rw [withF_eq_some] at h; obtain ⟨_, _, -, h⟩ := h; cases h
    exact ⟨show 0 < n.toNat by omega, .inl (by
      show Ty.bitvec (.TBitVector n) = Ty.bitvec (.TBitVector ((n.toNat : Nat) : Int))
      rw [toNat_cast hn])⟩
  · obtain ⟨-, rfl⟩ := wt
    rw [BitvecMod.withW_eq_some] at h; obtain ⟨_, _, -, h⟩ := h
    simp only [Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; rfl
  · obtain ⟨-, rfl⟩ := wt
    simp only [Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; rfl

open PtrMod in
theorem ptr_ty (ρ : Env) (n : PtrMod.Node Term) (t : Ty) (v : Val)
    (wt : PtrMod.Node.wt Ty.bool Ty.core Ty.bitvec Ty.ptr Term.ty n t)
    (ih : ∀ c ∈ n.children, ∀ v, ev ρ c = some v → v.Of c.ty)
    (h : PtrMod.Node.eval (D := dom) ρ t (n.map (fun c ρ => ev ρ c)) = some v) : v.Of t := by
  cases n <;> simp only [PtrMod.Node.wt, PtrMod.Node.map, PtrMod.Node.eval] at wt h
  · rename_i l o
    obtain ⟨n, hn, hl, -, rfl⟩ := wt
    rw [BitvecMod.withW_eq_some] at h; obtain ⟨m, x, hx, h⟩ := h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, -, _, -, rfl⟩ := h
    obtain ⟨hm, h' | h'⟩ := hl ▸ ih l (by simp [PtrMod.Node.children]) _ hx <;> cases h'
    exact ⟨hm, rfl⟩
  all_goals
    rename_i p
    obtain ⟨n, hn, hp, rfl⟩ := wt
    rw [withP_eq_some] at h; obtain ⟨m, l, o, hx, h⟩ := h; cases h
    obtain ⟨hm, h'⟩ := hp ▸ ih p (by simp [PtrMod.Node.children]) _ hx
    cases h'
    first | exact ⟨hm, .inr rfl⟩ | exact ⟨hm, .inl rfl⟩

/-- The values of a list of terms that are not poison are some of their
values. -/
theorem mem_mapM {l : List Term} {f : Term → Option Val} {vs : List Val}
    (h : (l.map f).mapM id = some vs) : ∀ w ∈ vs, ∃ c ∈ l, f c = some w := by
  induction l generalizing vs with
  | nil => simp at h; subst h; simp
  | cons c l ih =>
    simp only [List.map_cons, List.mapM_cons, id, Option.bind_eq_bind, Option.pure_def,
      Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨w, hw, ws, hws, rfl⟩ := h
    intro u hu
    simp only [List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact ⟨c, by simp, hw⟩
    · obtain ⟨c', hc', h'⟩ := ih hws u hu; exact ⟨c', by simp [hc'], h'⟩

theorem child_lt_bool {n : KanonBool.Node Term} {t : Ty} {c : Term} (hc : c ∈ n.children) :
    sizeOf c < sizeOf (Term.bool n t) :=
  (KanonBool.Node.all_iff _ n).1 (instBoolLang.size_proj (.bool n t) n rfl) c hc
theorem child_lt_core {n : CoreMod.Node Term} {t : Ty} {c : Term} (hc : c ∈ n.children) :
    sizeOf c < sizeOf (Term.core n t) :=
  (CoreMod.Node.all_iff _ n).1 (instCoreLang.size_proj (.core n t) n rfl) c hc
theorem child_lt_bitvec {n : BitvecMod.Node Term} {t : Ty} {c : Term} (hc : c ∈ n.children) :
    sizeOf c < sizeOf (Term.bitvec n t) :=
  (BitvecMod.Node.all_iff _ n).1 (instBitvecLang.size_proj (.bitvec n t) n rfl) c hc
theorem child_lt_float {n : FloatMod.Node Term} {t : Ty} {c : Term} (hc : c ∈ n.children) :
    sizeOf c < sizeOf (Term.float n t) :=
  (FloatMod.Node.all_iff _ n).1 (instFloatLang.size_proj (.float n t) n rfl) c hc
theorem child_lt_ptr {n : PtrMod.Node Term} {t : Ty} {c : Term} (hc : c ∈ n.children) :
    sizeOf c < sizeOf (Term.ptr n t) :=
  (PtrMod.Node.all_iff _ n).1 (instPtrLang.size_proj (.ptr n t) n rfl) c hc

theorem ite_some {c : Prop} [Decidable c] {x v : Val} (h : (if c then some x else none) = some v) :
    v = x := by
  by_cases hc : c
  · rw [if_pos hc] at h; cases h; rfl
  · rw [if_neg hc] at h; cases h

/-- Well-typed terms evaluate to values of their sort. -/
theorem ev_ty (e : Term) : ∀ (ρ : Env) (v : Val), e.WT → ev ρ e = some v → v.Of e.ty := by
  intro ρ v w h
  match e with
  | .bool n t =>
    rw [WT_bool, KanonBool.Node.all_iff] at w; rw [ev_bool] at h
    have ih : ∀ c ∈ n.children, ∀ v, ev ρ c = some v → v.Of c.ty :=
      fun c hc v hv => ev_ty c ρ v (w.2 c hc) hv
    obtain ⟨wt, -⟩ := w
    show v.Of t
    cases n with
    | Ite g a b =>
      simp only [KanonBool.Node.wt] at wt
      simp only [KanonBool.Node.map, KanonBool.Node.eval, KanonBool.pite_eq_some] at h
      rcases h with ⟨-, h⟩ | ⟨-, -, h⟩
      · rw [wt.2.2]; exact ih a (by simp [KanonBool.Node.children]) v h
      · rw [wt.2.2, ← wt.2.1]; exact ih b (by simp [KanonBool.Node.children]) v h
    | _ =>
      simp only [KanonBool.Node.wt] at wt
      simp only [KanonBool.Node.map, KanonBool.Node.eval, KanonBool.pnot_eq_some, KanonBool.pand_eq_some,
        KanonBool.por_eq_some, KanonBool.peq_eq_some, KanonBool.pdistinct_eq_some,
        Option.some.injEq] at h
      have ht : t = .bool .TBool := by
        first | exact wt | exact wt.2 | exact wt.2.2 | (obtain ⟨_, h, -⟩ := wt; exact h)
      subst ht
      simp only [show (KanonBool.Values.vbool (D := dom)).inj = Val.bool from rfl] at h
      obtain ⟨b, rfl⟩ : ∃ b, v = .bool b := by grind
      rfl
  | .core n t =>
    rw [WT_core, CoreMod.Node.all_iff] at w; rw [ev_core] at h
    have ih : ∀ c ∈ n.children, ∀ v, ev ρ c = some v → v.Of c.ty :=
      fun c hc v hv => ev_ty c ρ v (w.2 c hc) hv
    obtain ⟨wt, -⟩ := w
    show v.Of t
    cases n with
    | Var x =>
      simp only [CoreMod.Node.map, CoreMod.Node.eval, Option.bind_eq_some_iff] at h
      obtain ⟨u, -, h⟩ := h
      split at h
      · cases h; assumption
      · cases h
    | Seq l =>
      simp only [CoreMod.Node.wt, CoreMod.seq_wt] at wt
      obtain ⟨e, rfl, he⟩ := wt
      simp only [CoreMod.Node.map, CoreMod.Node.eval, CoreMod.seqV, List.map_map,
        Function.comp_def, Option.map_eq_some_iff] at h
      obtain ⟨vs, hvs, rfl⟩ := h
      refine ⟨e, rfl, (Val.ofAll_iff _ _).2 fun u hu => ?_⟩
      obtain ⟨c, hc, hcu⟩ := mem_mapM hvs u hu
      rw [← he c hc]; exact ih c (by simpa [CoreMod.Node.children] using hc) u hcu
  | .exists n t =>
    rw [WT_exists] at w; rw [ev_exists] at h
    cases n with
    | Exists bs body =>
      obtain ⟨⟨rfl, -⟩, -⟩ := w
      simp only [ExistsMod.Node.map, ExistsMod.Node.eval, ExistsMod.existsV] at h
      obtain rfl := ite_some h; rfl
  | .bitvec n t =>
    rw [WT_bitvec, BitvecMod.Node.all_iff] at w; rw [ev_bitvec] at h
    exact bitvec_ty ρ n t v w.1 (fun c hc v hv => ev_ty c ρ v (w.2 c hc) hv) h
  | .float n t =>
    rw [WT_float, FloatMod.Node.all_iff] at w; rw [ev_float] at h
    exact float_ty ρ n t v w.1 (fun c hc v hv => ev_ty c ρ v (w.2 c hc) hv) h
  | .ptr n t =>
    rw [WT_ptr, PtrMod.Node.all_iff] at w; rw [ev_ptr] at h
    exact ptr_ty ρ n t v w.1 (fun c hc v hv => ev_ty c ρ v (w.2 c hc) hv) h
termination_by sizeOf e
decreasing_by
  all_goals first
    | exact child_lt_bool ‹_›
    | exact child_lt_core ‹_›
    | exact child_lt_bitvec ‹_›
    | exact child_lt_float ‹_›
    | exact child_lt_ptr ‹_›

instance : KanonBool.Typed sem where
  ev_sort ρ e v s w h he := by
    have := ev_ty e ρ v w he
    rw [show e.ty = _ from h] at this
    cases s
    cases v <;> simp [Val.Of] at this
    rename_i b; cases b
    · exact .inr rfl
    · exact .inl rfl

instance : CoreMod.Typed sem where
  ev_sort ρ e v s w h he := by
    have := ev_ty e ρ v w he
    rw [show e.ty = _ from h] at this
    cases s
    cases v <;> simp [Val.Of] at this
    obtain ⟨e', h', hall⟩ := this
    cases h'
    exact ⟨_, rfl, (Val.ofAll_iff _ _).1 hall⟩

instance : BitvecMod.Typed sem where
  ev_sort ρ e v s w h he := by
    have := ev_ty e ρ v w he
    rw [show e.ty = _ from h] at this
    cases s <;> cases v <;>
      simp [Val.Of, show ∀ s, BitvecMod.sort (S := sem) s = Ty.bitvec s from fun _ => rfl] at this
    all_goals
      obtain ⟨hn, h'⟩ := this
      subst h'
      exact ⟨by omega, by rw [Int.toNat_natCast]; exact ⟨_, rfl⟩⟩

instance : FloatMod.Typed sem where
  ev_sort ρ e v s w h he := by
    have := ev_ty e ρ v w he
    rw [show e.ty = _ from h] at this
    cases s
    cases v <;>
      simp [Val.Of, show ∀ s, FloatMod.sort (S := sem) s = Ty.float s from fun _ => rfl] at this
    subst this; exact ⟨_, rfl⟩

instance : PtrMod.Typed sem where
  ev_sort ρ e v s w h he := by
    have := ev_ty e ρ v w he
    rw [show e.ty = _ from h] at this
    cases s
    cases v <;>
      simp [Val.Of, show ∀ s, PtrMod.sort (S := sem) s = Ty.ptr s from fun _ => rfl] at this
    obtain ⟨hn, h'⟩ := this; subst h'
    exact ⟨by omega, by rw [Int.toNat_natCast]; exact ⟨_, _, rfl⟩⟩

/-! ## Free variables -/

/-- The children of a term, but the body of an `Exists`. -/
def Term.kids : Term → List Term
  | .bool n _ => n.children
  | .core n _ => n.children
  | .bitvec n _ => n.children
  | .float n _ => n.children
  | .ptr n _ => n.children
  | .exists _ _ => []

theorem kids_size : ∀ (e : Term), ∀ c ∈ e.kids, sizeOf c < sizeOf e
  | .bool _ _, _, h => child_lt_bool h
  | .core _ _, _, h => child_lt_core h
  | .bitvec _ _, _, h => child_lt_bitvec h
  | .float _ _, _, h => child_lt_float h
  | .ptr _ _, _, h => child_lt_ptr h
  | .exists _ _, _, h => by simp [Term.kids] at h

/-- The variables that occur free in a term. -/
def Term.free : Term → List Int
  | .core (.Var x) _ => [x]
  | .exists (.Exists bs body) _ => body.free.filter (fun x => x ∉ bs.map Prod.fst)
  | e@(.core (.Seq _) _) | e@(.bool _ _) | e@(.bitvec _ _) | e@(.float _ _) | e@(.ptr _ _) =>
    e.kids.attach.flatMap fun ⟨c, _⟩ => c.free
termination_by e => sizeOf e
decreasing_by
  all_goals first
    | (simp; omega)
    | (simp only [namedPattern] at *; subst_vars; exact kids_size _ _ ‹_›)

theorem free_kid {e c : Term} {x : Int} (hc : c ∈ e.kids) (hx : x ∈ c.free) : x ∈ e.free := by
  match e with
  | .core (.Var _) _ | .exists _ _ => simp [Term.kids, CoreMod.Node.children] at hc
  | .core (.Seq _) _ | .bool _ _ | .bitvec _ _ | .float _ _ | .ptr _ _ =>
    rw [Term.free]; simp only [List.mem_flatMap, List.mem_attach, true_and, Subtype.exists]
    exact ⟨c, hc, hx⟩

theorem free_body {bs : List (Int × Ty)} {body : Term} {t : Ty} {x : Int}
    (hx : x ∈ body.free) (hb : x ∉ bs.map Prod.fst) :
    x ∈ (Term.exists (.Exists bs body) t).free := by
  rw [Term.free]; simp only [List.mem_filter, decide_eq_true_eq]
  exact ⟨hx, hb⟩

/-- The environment `ρ1` on the names `bs`, and `ρ` on the others. -/
def over (ρ1 ρ : Env) (bs : List (Int × Ty)) : Env :=
  fun x => if x ∈ bs.map Prod.fst then ρ1 x else ρ x

theorem extends_over {ρ1 ρ ρ' : Env} {bs bs' : List (Int × Ty)} (h : Extends ρ1 ρ bs)
    (sub : ∀ b ∈ bs', b ∈ bs) : Extends (over ρ1 ρ' bs') ρ' bs' := by
  refine ⟨fun x hx => ?_, fun b hb => ?_⟩
  · have : x ∉ bs'.map Prod.fst := by
      intro h; obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h; exact hx b hb rfl
    simp [over, this]
  · obtain ⟨v, hv, hof⟩ := h.2 b (sub b hb)
    exact ⟨v, by unfold over; rw [if_pos (List.mem_map_of_mem hb)]; exact hv, hof⟩

/-- The value of a term depends on its free variables only. -/
theorem ev_local (e : Term) : ∀ ρ ρ' : Env, (∀ x ∈ e.free, ρ x = ρ' x) → ev ρ e = ev ρ' e := by
  intro ρ ρ' h
  have hk : ∀ c ∈ e.kids, ev ρ c = ev ρ' c := fun c hc =>
    ev_local c ρ ρ' (fun x hx => h x (free_kid hc hx))
  match e with
  | .core (.Var x) t =>
    have : ρ x = ρ' x := h x (by rw [Term.free]; simp)
    rw [ev_core, ev_core]; simp only [CoreMod.Node.map, CoreMod.Node.eval]
    show (ρ x).bind _ = (ρ' x).bind _
    rw [this]
  | .core (.Seq l) t =>
    rw [ev_core, ev_core]
    simp only [Term.kids, CoreMod.Node.children] at hk
    simp only [CoreMod.Node.map, CoreMod.Node.eval, CoreMod.seqV, List.map_map, Function.comp_def]
    rw [List.map_congr_left hk]
  | .bool n t =>
    rw [ev_bool, ev_bool]
    cases n <;> simp only [Term.kids, KanonBool.Node.children, List.mem_cons, List.mem_append,
      List.mem_singleton, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq_or_imp,
      forall_eq] at hk <;>
      simp only [KanonBool.Node.map, KanonBool.Node.eval, hk, List.map_map, Function.comp_def]
    all_goals (try (rename_i l; rw [List.map_congr_left hk]))
  | .bitvec n t =>
    rw [ev_bitvec, ev_bitvec]
    cases n <;> simp only [Term.kids, BitvecMod.Node.children, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false, or_imp, forall_and, forall_eq_or_imp, forall_eq] at hk <;>
      simp only [BitvecMod.Node.map, BitvecMod.Node.eval, hk]
  | .float n t =>
    rw [ev_float, ev_float]
    cases n <;> simp only [Term.kids, FloatMod.Node.children, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false, or_imp, forall_and, forall_eq_or_imp, forall_eq] at hk <;>
      simp only [FloatMod.Node.map, FloatMod.Node.eval, hk]
  | .ptr n t =>
    rw [ev_ptr, ev_ptr]
    cases n <;> simp only [Term.kids, PtrMod.Node.children, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false, or_imp, forall_and, forall_eq_or_imp, forall_eq] at hk <;>
      simp only [PtrMod.Node.map, PtrMod.Node.eval, hk]
  | .exists (.Exists bs body) t =>
    have hb : ∀ ρ1 ρ1' : Env, Extends ρ1 ρ bs → (∀ x ∈ bs.map Prod.fst, ρ1 x = ρ1' x) →
        (∀ x, x ∉ bs.map Prod.fst → ρ1' x = ρ' x) → ev ρ1 body = ev ρ1' body := by
      intro ρ1 ρ1' e1 hin hout
      refine ev_local body ρ1 ρ1' (fun x hx => ?_)
      by_cases hm : x ∈ bs.map Prod.fst
      · exact hin x hm
      · rw [hout x hm, e1.1 x (fun b hb' he => hm (he ▸ List.mem_map_of_mem hb'))]
        exact h x (free_body hx hm)
    rw [ev_exists, ev_exists]
    simp only [ExistsMod.Node.map, ExistsMod.Node.eval]
    apply ExistsMod.existsV_congr Iff.rfl
    · intro ρ1 e1
      exact ⟨over ρ1 ρ' bs, extends_over e1 (fun _ h => h),
        hb ρ1 _ e1 (fun x hx => by simp [over, hx]) (fun x hx => by simp [over, hx])⟩
    · intro ρ2 e2
      have e1 : Extends (over ρ2 ρ bs) ρ bs := extends_over e2 (fun _ h => h)
      refine ⟨over ρ2 ρ bs, e1, hb _ ρ2 e1 (fun x hx => by simp [over, hx]) (fun x hx => ?_)⟩
      exact e2.1 x (fun b hb' he => hx (he ▸ List.mem_map_of_mem hb'))
termination_by sizeOf e
decreasing_by
  all_goals first
    | exact kids_size _ c ‹_›
    | (simp; omega)

/-- Distinct names name distinct binders. -/
theorem eq_of_nodup : ∀ {bs : List (Int × Ty)}, (bs.map Prod.fst).Nodup →
    ∀ {a b}, a ∈ bs → b ∈ bs → a.1 = b.1 → a = b
  | [], _, _, _, ha, _, _ => by cases ha
  | c :: bs, hn, a, b, ha, hb, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hn
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd h.symm (hn.1 b hb)
    · exact absurd h (hn.1 a ha)
    · exact eq_of_nodup hn.2 ha hb h

/-- The binders of `bs` that occur free in `body`. -/
def usedBinders (bs : List (Int × Ty)) (body : Term) : List (Int × Ty) :=
  bs.filter (fun b => b.1 ∈ body.free)

theorem mem_used {bs : List (Int × Ty)} {body : Term} {x : Int} (hx : x ∈ body.free)
    (hb : x ∈ bs.map Prod.fst) : x ∈ (usedBinders bs body).map Prod.fst := by
  obtain ⟨b, hb', rfl⟩ := List.mem_map.1 hb
  exact List.mem_map_of_mem (List.mem_filter.2 ⟨hb', by simpa using hx⟩)

/-- Dropping the binders that the body does not use does not change an `Exists`
that is not poison (whose binders' sorts have values). -/
theorem ev_used (ρ : Env) (bs : List (Int × Ty)) (body : Term) (t : Ty) (v : Val)
    (hn : (bs.map Prod.fst).Nodup) (h : ev ρ (.exists (.Exists bs body) t) = some v) :
    ev ρ (.exists (.Exists (usedBinders bs body) body) t) = some v := by
  have sub : ∀ b ∈ usedBinders bs body, b ∈ bs := fun b hb => (List.mem_filter.1 hb).1
  rw [ev_exists] at h ⊢
  simp only [ExistsMod.Node.map, ExistsMod.Node.eval] at h ⊢
  have hs : ∀ b ∈ bs, ∃ v, CoreMod.Values.Of (D := dom) v b.2 := by
    unfold ExistsMod.existsV at h; split at h
    · rename_i hc; exact hc.1
    · cases h
  rw [← h]; symm
  apply ExistsMod.existsV_congr ⟨fun h b hb => h b (sub b hb), fun _ => hs⟩
  · intro ρ1 e1
    refine ⟨over ρ1 ρ (usedBinders bs body), extends_over e1 sub, ?_⟩
    refine ev_local body _ _ (fun x hx => ?_)
    unfold over
    split
    · rfl
    · rename_i hu
      refine e1.1 x (fun b hb he => hu ?_)
      subst he; exact mem_used hx (List.mem_map_of_mem hb)
  · intro ρ2 e2
    let wit : Int × Ty → Option Val := fun b =>
      if hb : b ∈ bs then some (Classical.choose (hs b hb)) else none
    let ρ1 : Env := fun x =>
      if x ∈ (usedBinders bs body).map Prod.fst then ρ2 x
      else match bs.find? (fun b => b.1 = x) with
        | some b => wit b
        | none => ρ x
    refine ⟨ρ1, ⟨fun x hx => ?_, fun b hb => ?_⟩, ?_⟩
    · have hu : x ∉ (usedBinders bs body).map Prod.fst := by
        intro h; obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h; exact hx b (sub b hb) rfl
      have hf : bs.find? (fun b => b.1 = x) = none :=
        List.find?_eq_none.2 (fun b hb h => hx b hb (by simpa using h))
      simp only [ρ1, if_neg hu, hf]
    · by_cases hu : b.1 ∈ (usedBinders bs body).map Prod.fst
      · obtain ⟨b', hb', he⟩ := List.mem_map.1 hu
        obtain ⟨v, hv, hof⟩ := e2.2 b' hb'
        have : b' = b := eq_of_nodup hn (sub b' hb') hb he
        subst this
        exact ⟨v, by simp only [ρ1, if_pos hu]; exact hv, hof⟩
      · cases hf : bs.find? (fun b' => b'.1 = b.1) with
        | none => exact absurd (List.find?_eq_none.1 hf b hb) (by simp)
        | some b' =>
          have hb' := List.mem_of_find?_eq_some hf
          have he : b'.1 = b.1 := by simpa using List.find?_some hf
          have : b' = b := eq_of_nodup hn hb' hb he
          subst this
          refine ⟨Classical.choose (hs b' hb'), ?_, Classical.choose_spec (hs b' hb')⟩
          simp only [ρ1, if_neg hu, hf, wit, dif_pos hb']
    · refine ev_local body _ _ (fun x hx => ?_)
      simp only [ρ1]
      split
      · rfl
      · rename_i hu
        have hx' : x ∉ bs.map Prod.fst := fun h => hu (mem_used hx h)
        have hf : bs.find? (fun b => b.1 = x) = none :=
          List.find?_eq_none.2 (fun b hb h => hx' (by
            simp only [decide_eq_true_eq] at h; exact h ▸ List.mem_map_of_mem hb))
        rw [hf]
        exact (e2.1 x (fun b hb he => hu (he ▸ List.mem_map_of_mem hb))).symm

instance : ExistsMod.Laws sem where
  used_binders := usedBinders
  used_sublist _ _ := List.filter_sublist
  ev_used ρ bs body t v w e := by
    obtain ⟨-, hn, -, -⟩ := ExistsMod.WT_exists w
    exact ev_used ρ bs body t v hn e

end Kanon
