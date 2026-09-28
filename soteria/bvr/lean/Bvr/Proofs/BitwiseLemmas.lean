import Bvr.Lemmas

/-! Lemmas for the proofs of the bitwise rules. -/

namespace Bvr
namespace BitwiseL

open Classical

/-! ## Values of bit-vector and pointer sorts -/

/-- A value of the bit-vector or pointer sort [s], if [s] is one. -/
def BvOK (s : Ty) (v : Val) : Prop :=
  (∀ n : Int, s = .bitVector n ∨ s = .loc n → ∃ x, v = .bv n.toNat x) ∧
    (∀ n : Int, s = .pointer n → ∃ l o, v = .ptr n.toNat l o)

theorem BvOK.of_hasSort {s : Ty} {v : Val} (h : v.hasSort s) : BvOK s v := by
  refine ⟨fun n hs => ?_, fun n hs => ?_⟩
  · rcases hs with rfl | rfl <;> cases v <;> simp [Val.hasSort] at h <;>
    · rename_i m x; obtain ⟨rfl, _⟩ := h; exact ⟨x, by simp⟩
  · subst hs; cases v <;> simp [Val.hasSort] at h
    rename_i m l o; obtain ⟨rfl, _⟩ := h; exact ⟨l, o, by simp⟩

theorem BvOK.bool {s : Ty} {v : Val} (h : s = .bool) : BvOK s v := by
  subst h; exact ⟨fun _ h => (by rcases h with h | h <;> cases h), fun _ h => (by cases h)⟩

theorem BvOK.float {s : Ty} {v : Val} {p} (h : s = .float p) : BvOK s v := by
  subst h; exact ⟨fun _ h => (by rcases h with h | h <;> cases h), fun _ h => (by cases h)⟩

theorem BvOK.bv {s : Ty} {m : Int} {k : Nat} {x : BitVec k} (h : s = .bitVector m ∨ s = .loc m)
    (hk : k = m.toNat) : BvOK s (.bv k x) := by
  subst hk
  refine ⟨fun _ h' => ?_, fun _ h' => ?_⟩ <;> rcases h with rfl | rfl <;>
    simp at h' <;> subst h' <;> exact ⟨x, rfl⟩

theorem bvBin_eq_some {f : ∀ {n : Nat}, BitVec n → BitVec n → Option Val} {a b : Option Val}
    {v : Val} :
    bvBin f a b = some v ↔ ∃ n x y, a = some (.bv n x) ∧ b = some (.bv n y) ∧ f x y = some v := by
  constructor
  · intro h
    rcases a with _ | ⟨_ | ⟨n, x⟩ | _ | _ | _ | _⟩ <;>
      rcases b with _ | ⟨_ | ⟨m, y⟩ | _ | _ | _ | _⟩ <;> simp [bvBin] at h
    obtain ⟨rfl, h⟩ := h
    exact ⟨_, _, _, rfl, rfl, h⟩
  · rintro ⟨n, x, y, rfl, rfl, h⟩
    simp [bvBin, h]

theorem ev_ok (FS : FloatSem) (ρ : Env) :
    ∀ (t : Term), t.WT → ∀ v, ev FS ρ t = some v → BvOK t.ty.sort v
  | .mk (.var x) T, _, v, h => by
      simp only [ev] at h
      split at h
      · split at h
        · simp at h; subst h; exact BvOK.of_hasSort ‹_›
        · simp at h
      · simp at h
  | .mk (.extension e) T, _, v, h => by
      simp only [ev] at h
      split at h
      · split at h
        · simp at h; subst h; exact BvOK.of_hasSort ‹_›
        · simp at h
      · simp at h
  | .mk (.bool b) T, w, v, h => by
      simp [Term.WT] at w; subst w; exact BvOK.bool rfl
  | .mk (.float f) T, w, v, h => by
      simp [Term.WT] at w; rw [w.1]; exact BvOK.float rfl
  | .mk (.bitVec z) T, w, v, h => by
      obtain ⟨n, _, hT, _⟩ := WT_bitVec.1 w
      simp only [ev] at h; cases h
      exact BvOK.bv hT (by rw [Ty.width_of_sort hT]; simp)

  | .mk (.ptr l o) T, w, v, h => by
      simp only [Term.WT] at w
      obtain ⟨n, hn, hT, hl, ho, wl, wo⟩ := w
      have il := ev_ok FS ρ l wl
      have io := ev_ok FS ρ o wo
      simp only [ev] at h
      split at h
      · rename_i m x k y el eo
        split at h
        · rename_i hm; subst hm; cases h
          obtain ⟨x', hx'⟩ := (il _ el).1 n (Or.inr hl)
          simp at hx'; obtain ⟨rfl, _⟩ := hx'
          subst hT
          exact ⟨fun _ h => (by rcases h with h | h <;> cases h), fun _ h => (by cases h; exact ⟨_, _, rfl⟩)⟩
        · simp at h
      · simp at h
  | .mk (.seq l) T, w, v, h => by
      simp only [Term.WT] at w
      obtain ⟨e, rfl, _⟩ := w
      exact ⟨fun _ h => (by rcases h with h | h <;> cases h), fun _ h => (by cases h)⟩
  | .mk (.unop op a) T, w, v, h => by
      obtain ⟨w1, wa⟩ := WT_unop.1 w
      have ia := ev_ok FS ρ a wa
      simp only [ev, Term.ty_mk] at h ⊢
      cases op <;> simp only [Unop.WT] at w1
      case not_ => exact BvOK.bool w1.2
      case getPtrLoc | getPtrOfs =>
        obtain ⟨n, hn, ha, hT⟩ := w1
        rcases ea : ev FS ρ a with _ | x
        · rw [ea] at h; simp [evUnop] at h
        obtain ⟨l, o, rfl⟩ := (ia x ea).2 n ha
        rw [ea] at h; simp [evUnop] at h; subst h
        first | exact BvOK.bv (Or.inl hT) rfl | exact BvOK.bv (Or.inr hT) rfl
      case bvOfBool n =>
        obtain ⟨hn, ha, hT⟩ := w1
        rcases ea : ev FS ρ a with _ | x
        · rw [ea] at h; simp [evUnop] at h
        rw [ea] at h; cases x <;> simp [evUnop] at h; subst h
        exact BvOK.bv (Or.inl hT) rfl
      case bvOfFloat rm s n =>
        obtain ⟨hn, ha, hT⟩ := w1
        rcases ea : ev FS ρ a with _ | x
        · rw [ea] at h; simp [evUnop] at h
        rw [ea] at h; cases x <;> simp [evUnop] at h; subst h
        exact BvOK.bv (Or.inl hT) rfl
      case floatOfBv => exact BvOK.float w1.2
      case floatOfBvRaw => exact BvOK.float w1.2
      case floatOfFloat => exact BvOK.float w1.2
      case bvExtract i j =>
        obtain ⟨n, ha, hi, hij, hj, hT⟩ := w1
        rcases ea : ev FS ρ a with _ | x
        · rw [ea] at h; simp [evUnop] at h
        rw [ea] at h; cases x <;> simp [evUnop] at h; subst h
        exact BvOK.bv (Or.inl hT) rfl
      case bvExtend s k =>
        obtain ⟨n, hn, ha, hk, hT⟩ := w1
        rcases ea : ev FS ρ a with _ | x
        · rw [ea] at h; simp [evUnop] at h
        obtain ⟨x, rfl⟩ := (ia x ea).1 n (Or.inl ha)
        rw [ea] at h; simp [evUnop] at h; subst h
        exact BvOK.bv (Or.inl hT) (by omega)
      case bvNot | neg =>
        obtain ⟨n, hn, ha, hT⟩ := w1
        rcases ea : ev FS ρ a with _ | x
        · rw [ea] at h; simp [evUnop] at h
        obtain ⟨x, rfl⟩ := (ia x ea).1 n (Or.inl ha)
        rw [ea] at h; simp only [evUnop] at h
        try split at h
        all_goals (try simp at h)
        all_goals (obtain rfl := h; exact BvOK.bv (Or.inl (hT.trans ha)) rfl)
      all_goals first
        | exact BvOK.float (w1.2.trans (Classical.choose_spec w1.1))
        | exact BvOK.bool w1.2
  | .mk (.binop op a b) T, w, v, h => by
      obtain ⟨w1, wa, wb⟩ := WT_binop.1 w
      have ia := ev_ok FS ρ a wa
      have ib := ev_ok FS ρ b wb
      simp only [ev, Term.ty_mk] at h ⊢
      have hbv : ∀ {f : ∀ {n : Nat}, BitVec n → BitVec n → Option Val},
          (∀ {k} (x y : BitVec k) u, f x y = some u → ∃ z : BitVec k, u = .bv k z) →
          (∃ n : Int, 0 < n ∧ a.ty.sort = .bitVector n) → T.sort = a.ty.sort →
          bvBin f (ev FS ρ a) (ev FS ρ b) = some v → BvOK T.sort v := by
        intro f hf ⟨n, _, ha⟩ hT e
        obtain ⟨k, x, y, ea, eb, e⟩ := bvBin_eq_some.1 e
        obtain ⟨z, rfl⟩ := hf x y v e
        obtain ⟨x', hx'⟩ := (ia _ ea).1 n (Or.inl ha)
        simp at hx'; obtain ⟨rfl, _⟩ := hx'
        exact BvOK.bv (Or.inl (hT.trans ha)) rfl
      cases op <;> simp only [Binop.WT] at w1
      case bvConcat =>
        obtain ⟨n, m, hn, hm, ha, hb, hT⟩ := w1
        rcases ea : ev FS ρ a with _ | x
        · rw [ea] at h; simp [evBinop] at h
        obtain ⟨x, rfl⟩ := (ia _ ea).1 n (Or.inl ha)
        rcases eb : ev FS ρ b with _ | y
        · rw [ea, eb] at h; simp [evBinop] at h
        obtain ⟨y, rfl⟩ := (ib _ eb).1 m (Or.inl hb)
        rw [ea, eb] at h; simp [evBinop] at h; subst h
        exact BvOK.bv (Or.inl hT) (by omega)
      all_goals first
        | exact BvOK.bool w1.2
        | exact BvOK.bool w1.2.2
        | exact BvOK.float (w1.2.2.trans (Classical.choose_spec w1.1))
        | (simp only [evBinop, checkedOp] at h
           refine hbv ?_ w1.1 w1.2.2 h
           intro k x y u e
           (try split at e) <;> simp at e <;> exact ⟨_, e.symm⟩)
  | .mk (.triop op a b c) T, w, v, h => by
      obtain ⟨w1, wa, wb, wc⟩ := WT_triop.1 w
      have ib := ev_ok FS ρ b wb
      have ic := ev_ok FS ρ c wc
      cases op <;> simp only [Triop.WT] at w1
      · obtain ⟨⟨p, hp⟩, _, _, hT⟩ := w1
        exact BvOK.float (hT.trans hp)
      · obtain ⟨_, hcb, hT⟩ := w1
        simp only [ev] at h
        rw [Term.ty_mk, hT]
        split at h
        · exact ib v h
        · rw [← hcb]; exact ic v h
        · simp at h
  | .mk (.nop op l) T, w, v, h => by
      simp only [Term.WT] at w
      rw [Term.ty_mk, w.1]; exact BvOK.bool rfl
  | .mk (.exists_ bs body) T, w, v, h => by
      simp only [Term.WT] at w
      rw [Term.ty_mk, w.1]; exact BvOK.bool rfl
termination_by t => sizeOf t
decreasing_by all_goals (simp_wf; omega)

theorem eval_bv {FS ρ t v} {n : Int} (h : eval FS ρ t = some v) (hs : t.ty = .bitVector n) :
    ∃ x, v = .bv n.toNat x := by
  have w := eval_WT h
  rw [eval_eq_ev w] at h
  exact (ev_ok FS ρ t w v h).1 n (Or.inl hs)

/-! ## Types -/

/-! ## Literals -/

theorem one_lt_two_pow {n : Int} (hn : 0 < n) : (1 : Int) < 2 ^ n.toNat := by
  have h : (2 : Nat) ^ 1 ≤ 2 ^ n.toNat := Nat.pow_le_pow_right (by omega) (by omega)
  have : (1 : Int) < ((2 ^ n.toNat : Nat) : Int) := by omega
  simpa using this

@[simp] theorem bv_zero_ty {n} : (bv_zero n).ty = .bitVector n := rfl
@[simp] theorem bv_one_ty {n} : (bv_one n).ty = .bitVector n := rfl

@[simp] theorem of_bool_WT {b} : (of_bool b).WT := by cases b <;> simp [of_bool]
@[simp] theorem of_bool_ty {b} : (of_bool b).ty = .bool := by cases b <;> simp [of_bool]
@[simp] theorem eval_of_bool {FS ρ b} : eval FS ρ (of_bool b) = some (.bool b) := by
  cases b <;> simp [of_bool]

/-! ## Masks -/

theorem popcountNat_eq_zero : ∀ {m : Nat}, popcountNat m = 0 → m = 0
  | 0, _ => rfl
  | k + 1, h => by
      rw [popcountNat] at h
      have : (k + 1) / 2 < k + 1 := by omega
      have := popcountNat_eq_zero (m := (k + 1) / 2) (by omega)
      omega

theorem popcountNat_eq_one : ∀ {m : Nat}, popcountNat m = 1 → ∃ j, m = 2 ^ j
  | 0, h => by simp [popcountNat] at h
  | k + 1, h => by
      rw [popcountNat] at h
      have : (k + 1) / 2 < k + 1 := by omega
      by_cases hm : (k + 1) % 2 = 1
      · have := popcountNat_eq_zero (m := (k + 1) / 2) (by omega)
        exact ⟨0, by omega⟩
      · obtain ⟨j, hj⟩ := popcountNat_eq_one (m := (k + 1) / 2) (by omega)
        exact ⟨j + 1, by rw [Nat.pow_succ]; omega⟩

structure BitOp (FS : FloatSem) (op : Binop) (f : ∀ {n : Nat}, BitVec n → BitVec n → BitVec n) :
    Prop where
  wt : ∀ a b t, Binop.WT op a b t ↔ (∃ n : Int, 0 < n ∧ a = .bitVector n) ∧ b = a ∧ t = a
  ev : ∀ a b, evBinop FS op a b = bvBin (fun x y => some (.bv _ (f x y))) a b

theorem BitOp.and {FS} : BitOp FS .bitAnd (· &&& ·) := ⟨fun _ _ _ => Iff.rfl, fun _ _ => rfl⟩
theorem BitOp.or {FS} : BitOp FS .bitOr (· ||| ·) := ⟨fun _ _ _ => Iff.rfl, fun _ _ => rfl⟩
theorem BitOp.shl {FS} : BitOp FS .shl (· <<< ·) := ⟨fun _ _ _ => Iff.rfl, fun _ _ => rfl⟩
theorem BitOp.add {FS} : BitOp FS (.add unchecked) (· + ·) :=
  ⟨fun _ _ _ => Iff.rfl, fun _ _ => by simp [evBinop, checkedOp, unchecked]⟩
theorem BitOp.mul {FS} : BitOp FS (.mul unchecked) (· * ·) :=
  ⟨fun _ _ _ => Iff.rfl, fun _ _ => by simp [evBinop, checkedOp, unchecked]⟩

theorem BitOp.WT {FS op f} (H : BitOp FS op f) {a b t} :
    (Term.mk (.binop op a b) t).WT ↔
      ∃ n : Int, 0 < n ∧ a.ty = .bitVector n ∧ b.ty = .bitVector n ∧ t = .bitVector n ∧
        a.WT ∧ b.WT := by
  rw [WT_binop, H.wt]
  constructor
  · rintro ⟨⟨⟨n, hn, ha⟩, hb, ht⟩, wa, wb⟩
    exact ⟨n, hn, ha, hb.trans ha, ht.trans ha, wa, wb⟩
  · rintro ⟨n, hn, ha, hb, ht, wa, wb⟩
    exact ⟨⟨⟨n, hn, ha⟩, hb.trans ha.symm, ht.trans ha.symm⟩, wa, wb⟩

theorem BitOp.eval_eq_some {FS op f} (H : BitOp FS op f) {ρ a b t v}
    (e : eval FS ρ (.mk (.binop op a b) t) = some v) :
    ∃ n x y, eval FS ρ a = some (.bv n x) ∧ eval FS ρ b = some (.bv n y) ∧ v = .bv n (f x y) := by
  have w := eval_WT e
  rw [eval_binop w, H.ev] at e
  obtain ⟨n, x, y, ea, eb, e⟩ := bvBin_eq_some.1 e
  exact ⟨n, x, y, ea, eb, by simp at e; exact e.symm⟩

/-! ## If-then-else -/

theorem WT_ite {g a b t} : (Term.mk (.triop .ite g a b) t).WT ↔
    g.ty = .bool ∧ b.ty = a.ty ∧ t = a.ty ∧ g.WT ∧ a.WT ∧ b.WT := by
  simp [WT_triop, Triop.WT, and_assoc]

theorem int_two_pow_cast (k : Nat) : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by push_cast; rfl

/-! ### Shifts of literals -/

theorem getLsbD_ofInt_lowmask (n : Nat) (s : Int) (i : Nat) :
    (BitVec.ofInt n (zshiftl 1 s - 1)).getLsbD i = (decide (i < n) && decide (i < s.toNat)) := by
  have e : zshiftl 1 s - 1 = ((2 ^ s.toNat - 1 : Nat) : Int) := by
    have := Nat.one_le_two_pow (n := s.toNat)
    rw [zshiftl, Int.one_mul, ← int_two_pow_cast]; omega
  rw [e, BitVec.ofInt_natCast, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]

theorem ite_pos' {c : Prop} [Decidable c] {α} {a b : α} (h : c) : (if c then a else b) = a :=
  by simp [h]
theorem ite_neg' {c : Prop} [Decidable c] {α} {a b : α} (h : ¬c) : (if c then a else b) = b :=
  by simp [h]
@[simp] theorem getLsbD_zero' {w i : Nat} : (0 : BitVec w).getLsbD i = false := by simp
theorem getLsbD_one' {w i : Nat} : (1 : BitVec w).getLsbD i = (decide (0 < w) && decide (i = 0)) :=
  by simp

/-- Simplifies the bits of bit-vector expressions, deciding index conditions with omega. -/
macro "bitw_simp" : tactic => `(tactic| simp (disch := omega) only [BitVec.getLsbD_extractLsb',
  BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
  BitVec.getLsbD_setWidth, BitVec.getLsbD_zero, BitVec.getLsbD_and, BitVec.getLsbD_or,
  BitVec.getLsbD_xor, decide_eq_true, decide_eq_false, ite_pos', ite_neg', getLsbD_zero',
  Bool.true_and,
  Bool.and_true, Bool.false_and, Bool.and_false, Bool.not_true, Bool.not_false, Nat.zero_add,
  Nat.add_zero, Int.toNat_zero, BitVec.getLsbD_of_ge, BitVec.getLsbD_signExtend,
  BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last, Bool.not_and, Bool.not_not, Bool.false_eq_true,
  Bool.true_eq_false, ↓reduceIte, BitVec.getLsbD_not, getLsbD_ofInt_lowmask,
  BitVec.ofInt_zlognot, getLsbD_one'])

end BitwiseL
end Bvr
