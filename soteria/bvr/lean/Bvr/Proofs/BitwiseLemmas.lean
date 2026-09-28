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

/-- A well-typed term of bit-vector type is poison or a bit-vector of its width. -/
theorem ev_bv {FS ρ t} {n : Int} (w : t.WT) (ht : t.ty = .bitVector n) :
    ev FS ρ t = none ∨ ∃ x, ev FS ρ t = some (.bv n.toNat x) := by
  rcases e : ev FS ρ t with _ | v
  · exact Or.inl rfl
  · obtain ⟨x, rfl⟩ := (ev_ok FS ρ t w v e).1 n (Or.inl ht)
    exact Or.inr ⟨x, rfl⟩

/-! ## Types -/

theorem ty_of_refines {FS a b} (h : Refines FS a b) (w : a.WT) : b.ty = a.ty := (h.syn w).2

theorem size_of_refines {FS a b} (h : Refines FS a b) (w : a.WT) : size b = size a := by
  simp [ty_of_refines h w]

/-! ## Literals -/

theorem lit_WT {z n : Int} (hn : 0 < n) (h0 : 0 ≤ z) (h1 : z < 2 ^ n.toNat) :
    (Term.mk (.bitVec z) (.bitVector n)).WT :=
  WT_bitVec.2 ⟨n.toNat, by omega, Or.inl (by simp; omega), h0, h1⟩

theorem eval_lit {FS ρ} {z n : Int} (w : (Term.mk (.bitVec z) (.bitVector n)).WT) :
    eval FS ρ (.mk (.bitVec z) (.bitVector n)) = some (.bv n.toNat (BitVec.ofInt _ z)) :=
  eval_bitVec' w (Or.inl rfl)

theorem one_lt_two_pow {n : Int} (hn : 0 < n) : (1 : Int) < 2 ^ n.toNat := by
  have h : (2 : Nat) ^ 1 ≤ 2 ^ n.toNat := Nat.pow_le_pow_right (by omega) (by omega)
  have : (1 : Int) < ((2 ^ n.toNat : Nat) : Int) := by omega
  simpa using this

@[simp] theorem bv_zero_ty {n} : (bv_zero n).ty = .bitVector n := rfl
@[simp] theorem bv_one_ty {n} : (bv_one n).ty = .bitVector n := rfl

theorem bv_zero_WT {n : Int} (hn : 0 < n) : (bv_zero n).WT :=
  lit_WT hn (by omega) (two_pow_pos' _)

theorem bv_one_WT {n : Int} (hn : 0 < n) : (bv_one n).WT :=
  lit_WT hn (by omega) (one_lt_two_pow hn)

theorem eval_bv_zero {FS ρ} {n : Int} (hn : 0 < n) :
    eval FS ρ (bv_zero n) = some (.bv n.toNat 0) := by
  rw [bv_zero, eval_lit (bv_zero_WT hn)]; simp

theorem bv_zero_pos {n : Int} (w : (bv_zero n).WT) : 0 < n := by
  obtain ⟨k, hk, h, _⟩ := WT_bitVec.1 w
  simp [bv_zero] at h; omega

theorem eval_bv_one {FS ρ} {n : Int} (hn : 0 < n) :
    eval FS ρ (bv_one n) = some (.bv n.toNat 1) := by
  rw [bv_one, eval_lit (bv_one_WT hn)]; simp

theorem toNat_ofInt_of_range {k : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ k) :
    (BitVec.ofInt k z).toNat = z.toNat := by
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt h0 (by exact_mod_cast h1)]

theorem ofInt_eq_zero_iff {k : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ k) :
    BitVec.ofInt k z = 0 ↔ z = 0 := by
  constructor
  · intro h; have := congrArg BitVec.toNat h
    rw [toNat_ofInt_of_range h0 h1] at this; simp at this; omega
  · rintro rfl; simp

@[simp] theorem of_bool_WT {b} : (of_bool b).WT := by cases b <;> simp [of_bool]
@[simp] theorem of_bool_ty {b} : (of_bool b).ty = .bool := by cases b <;> simp [of_bool]
@[simp] theorem eval_of_bool {FS ρ b} : eval FS ρ (of_bool b) = some (.bool b) := by
  cases b <;> simp [of_bool]

theorem lit_inv {z T} (w : (Term.mk (.bitVec z) T).WT) (n : Int) (hT : T = .bitVector n) :
    0 < n ∧ 0 ≤ z ∧ z < 2 ^ n.toNat := by
  obtain ⟨k, hk, h, h0, h1⟩ := WT_bitVec.1 w
  subst hT; rcases h with h | h <;> simp at h; subst h; simp; omega

theorem eval_lit' {FS ρ z T} (w : (Term.mk (.bitVec z) T).WT) {n : Int} (hT : T = .bitVector n) :
    eval FS ρ (.mk (.bitVec z) T) = some (.bv n.toNat (BitVec.ofInt _ z)) :=
  eval_bitVec' w (Or.inl hT)

theorem lit_val₀ {FS ρ z T k x} (e : eval FS ρ (.mk (.bitVec z) T) = some (.bv k x)) :
    x = BitVec.ofInt k z ∧ 0 ≤ z ∧ z < 2 ^ k := by
  have w := eval_WT e
  obtain ⟨n, hn, hT, h0, h1⟩ := WT_bitVec.1 w
  rw [eval_bitVec' w hT] at e
  simp at e; obtain ⟨rfl, h⟩ := e; exact ⟨(eq_of_heq h).symm, h0, by simpa using h1⟩

/-- Bit-vector values are equal when their widths and their bits are. -/
theorem Val.bv_ext {n m : Nat} {x : BitVec n} {y : BitVec m} (h : n = m)
    (hx : ∀ i < n, x.getLsbD i = y.getLsbD i) : Val.bv n x = Val.bv m y := by
  subst h; congr 1; ext i hi; exact hx i hi

theorem zland_ofNat (a b : Nat) : zland a b = ((a &&& b : Nat) : Int) := rfl
theorem zlor_ofNat (a b : Nat) : zlor a b = ((a ||| b : Nat) : Int) := rfl
theorem zland_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ zland a b := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  simp [zland_ofNat]

theorem zlor_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ zlor a b := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  simp [zlor_ofNat]

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
theorem BitOp.xor {FS} : BitOp FS .bitXor (· ^^^ ·) := ⟨fun _ _ _ => Iff.rfl, fun _ _ => rfl⟩
theorem BitOp.shl {FS} : BitOp FS .shl (· <<< ·) := ⟨fun _ _ _ => Iff.rfl, fun _ _ => rfl⟩
theorem BitOp.lshr {FS} : BitOp FS .lShr (· >>> ·) := ⟨fun _ _ _ => Iff.rfl, fun _ _ => rfl⟩
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

theorem BitOp.eval_of {FS op f} (H : BitOp FS op f) {ρ a b t n x y}
    (w : (Term.mk (.binop op a b) t).WT) (ea : eval FS ρ a = some (.bv n x))
    (eb : eval FS ρ b = some (.bv n y)) :
    eval FS ρ (.mk (.binop op a b) t) = some (.bv n (f x y)) := by
  rw [eval_binop w, H.ev, ea, eb]; simp [bvBin]

/-- A binary operation on literals is folded. -/
theorem Refines.retype {FS k t t'} (h : (Term.mk k t).WT → t' = t) :
    Refines FS (.mk k t) (.mk k t') := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain rfl := h w; exact ⟨w, rfl⟩
  · obtain rfl := h w; exact e

/-! ## If-then-else -/

theorem WT_ite {g a b t} : (Term.mk (.triop .ite g a b) t).WT ↔
    g.ty = .bool ∧ b.ty = a.ty ∧ t = a.ty ∧ g.WT ∧ a.WT ∧ b.WT := by
  simp [WT_triop, Triop.WT, and_assoc]

/-- An ite whose branches are refined by rule functions is refined by [b_ite]. -/
theorem Refines.ite_O {FS} {O : Ops} (hO : O.Sound FS) {g A B A' B' t} (hA : Refines FS A A')
    (hB : Refines FS B B') :
    Refines FS (.mk (.triop .ite g A B) t) (O.b_ite g A' B') := by
  refine Refines.trans (Refines.ite Refines.refl hA hB (fun w => ?_)) (hO.b_ite g A' B')
  obtain ⟨_, _, ht, _, wa, _⟩ := WT_ite.1 w
  simp [ty_of_refines hA wa, ht]

/-- An operation with an ite as its right operand is pushed into the branches. -/
theorem WT_bvOfBool {m g T} : (Term.mk (.unop (.bvOfBool m) g) T).WT ↔
    0 < m ∧ g.ty = .bool ∧ T = .bitVector m ∧ g.WT := by
  simp [WT_unop, Unop.WT, and_assoc]

theorem eval_bvOfBool {FS ρ m g T v} (e : eval FS ρ (.mk (.unop (.bvOfBool m) g) T) = some v) :
    ∃ b, eval FS ρ g = some (.bool b) ∧ v = .bv m.toNat (if b then 1 else 0) := by
  rw [eval_unop (eval_WT e)] at e
  rcases eg : eval FS ρ g with _ | ⟨b | _ | _ | _ | _ | _⟩ <;> rw [eg] at e <;>
    simp [evUnop] at e
  exact ⟨b, rfl, e.symm⟩

theorem eval_bvOfBool' {FS ρ m g T b} (w : (Term.mk (.unop (.bvOfBool m) g) T).WT)
    (e : eval FS ρ g = some (.bool b)) :
    eval FS ρ (.mk (.unop (.bvOfBool m) g) T) = some (.bv m.toNat (if b then 1 else 0)) := by
  rw [eval_unop w, e]; rfl

theorem WT_extract {i j a T} : (Term.mk (.unop (.bvExtract i j) a) T).WT ↔
    ∃ n : Int, a.ty = .bitVector n ∧ 0 ≤ i ∧ i ≤ j ∧ j < n ∧ T = .bitVector (j - i + 1) ∧
      a.WT := by
  simp only [WT_unop, Unop.WT, Ty.sort_eq]
  constructor
  · rintro ⟨⟨n, h1, h2, h3, h4, h5⟩, h6⟩; exact ⟨n, h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨n, h1, h2, h3, h4, h5, h6⟩; exact ⟨⟨n, h1, h2, h3, h4, h5⟩, h6⟩

theorem eval_extract {FS ρ i j a T v}
    (e : eval FS ρ (.mk (.unop (.bvExtract i j) a) T) = some v) :
    ∃ n x, a.ty = .bitVector n ∧ 0 ≤ i ∧ i ≤ j ∧ j < n ∧ T = .bitVector (j - i + 1) ∧
      eval FS ρ a = some (.bv n.toNat x) ∧
      v = .bv (j - i + 1).toNat (x.extractLsb' i.toNat _) := by
  have w := eval_WT e
  obtain ⟨n, ha, h0, h1, h2, hT, _⟩ := WT_extract.1 w
  rw [eval_unop w] at e
  rcases ea : eval FS ρ a with _ | x
  · rw [ea] at e; simp at e
  obtain ⟨x, rfl⟩ := eval_bv ea ha
  rw [ea] at e; simp [evUnop] at e
  exact ⟨n, x, ha, h0, h1, h2, hT, rfl, e.symm⟩

theorem eval_extract_of {FS ρ i j a T k x} (w : (Term.mk (.unop (.bvExtract i j) a) T).WT)
    (ea : eval FS ρ a = some (.bv k x)) :
    eval FS ρ (.mk (.unop (.bvExtract i j) a) T) =
      some (.bv (j - i + 1).toNat (x.extractLsb' i.toNat _)) := by
  rw [eval_unop w, ea]; rfl

theorem WT_extend {s k a T} : (Term.mk (.unop (.bvExtend s k) a) T).WT ↔
    ∃ n : Int, 0 < n ∧ a.ty = .bitVector n ∧ 0 ≤ k ∧ T = .bitVector (n + k) ∧ a.WT := by
  simp only [WT_unop, Unop.WT, Ty.sort_eq]
  constructor
  · rintro ⟨⟨n, h1, h2, h3, h4⟩, h6⟩; exact ⟨n, h1, h2, h3, h4, h6⟩
  · rintro ⟨n, h1, h2, h3, h4, h6⟩; exact ⟨⟨n, h1, h2, h3, h4⟩, h6⟩

theorem eval_extend {FS ρ s k a T v}
    (e : eval FS ρ (.mk (.unop (.bvExtend s k) a) T) = some v) :
    ∃ n x, 0 < n ∧ a.ty = .bitVector n ∧ 0 ≤ k ∧ T = .bitVector (n + k) ∧
      eval FS ρ a = some (.bv n.toNat x) ∧
      v = .bv (n.toNat + k.toNat) (if s then x.signExtend _ else x.setWidth _) := by
  have w := eval_WT e
  obtain ⟨n, hn, ha, h0, hT, _⟩ := WT_extend.1 w
  rw [eval_unop w] at e
  rcases ea : eval FS ρ a with _ | x
  · rw [ea] at e; simp at e
  obtain ⟨x, rfl⟩ := eval_bv ea ha
  rw [ea] at e; simp only [evUnop] at e
  exact ⟨n, x, hn, ha, h0, hT, rfl, (Option.some.inj e).symm⟩

theorem eval_extend_of {FS ρ s k a T n x} (w : (Term.mk (.unop (.bvExtend s k) a) T).WT)
    (ea : eval FS ρ a = some (.bv n x)) :
    eval FS ρ (.mk (.unop (.bvExtend s k) a) T) =
      some (.bv (n + k.toNat) (if s then x.signExtend _ else x.setWidth _)) := by
  rw [eval_unop w, ea]; rfl

theorem WT_concat {a b T} : (Term.mk (.binop .bvConcat a b) T).WT ↔
    ∃ n m : Int, 0 < n ∧ 0 < m ∧ a.ty = .bitVector n ∧ b.ty = .bitVector m ∧
      T = .bitVector (n + m) ∧ a.WT ∧ b.WT := by
  simp [WT_binop, Binop.WT]
  constructor
  · rintro ⟨⟨n, m, h1, h2, h3, h4, h5⟩, h6, h7⟩; exact ⟨n, m, h1, h2, h3, h4, h5, h6, h7⟩
  · rintro ⟨n, m, h1, h2, h3, h4, h5, h6, h7⟩; exact ⟨⟨n, m, h1, h2, h3, h4, h5⟩, h6, h7⟩

theorem eval_concat {FS ρ a b T v}
    (e : eval FS ρ (.mk (.binop .bvConcat a b) T) = some v) :
    ∃ n m x y, 0 < n ∧ 0 < m ∧ a.ty = .bitVector n ∧ b.ty = .bitVector m ∧
      T = .bitVector (n + m) ∧
      eval FS ρ a = some (.bv n.toNat x) ∧ eval FS ρ b = some (.bv m.toNat y) ∧
      v = .bv (n.toNat + m.toNat) (x ++ y) := by
  have w := eval_WT e
  obtain ⟨n, m, hn, hm, ha, hb, hT, _⟩ := WT_concat.1 w
  rw [eval_binop w] at e
  rcases ea : eval FS ρ a with _ | x
  · rw [ea] at e; simp [evBinop] at e
  obtain ⟨x, rfl⟩ := eval_bv ea ha
  rcases eb : eval FS ρ b with _ | y
  · rw [ea, eb] at e; simp [evBinop] at e
  obtain ⟨y, rfl⟩ := eval_bv eb hb
  rw [ea, eb] at e; simp only [evBinop] at e
  exact ⟨n, m, x, y, hn, hm, ha, hb, hT, rfl, rfl, (Option.some.inj e).symm⟩

theorem eval_concat_of {FS ρ a b T n m x y} (w : (Term.mk (.binop .bvConcat a b) T).WT)
    (ea : eval FS ρ a = some (.bv n x)) (eb : eval FS ρ b = some (.bv m y)) :
    eval FS ρ (.mk (.binop .bvConcat a b) T) = some (.bv (n + m) (x ++ y)) := by
  rw [eval_binop w, ea, eb]; rfl

theorem Val.bv_inj {n m : Nat} {x : BitVec n} {y : BitVec m} (h : Val.bv n x = Val.bv m y) :
    ∃ h : n = m, h ▸ x = y := by
  cases h; exact ⟨rfl, rfl⟩

/-- Refining the operands of a binary node whose type is computed from its left operand. -/
theorem Refines.binop_ty {FS op a a' b b'} (F : Term → Ty) (hF : ∀ x y : Term, x.ty = y.ty → F x = F y)
    (ha : Refines FS a a') (hb : Refines FS b b') :
    Refines FS (.mk (.binop op a b) (F a)) (.mk (.binop op a' b') (F a')) :=
  Refines.binop ha hb (fun w => hF _ _ (ty_of_refines ha (WT_binop.1 w).2.1))

/-- Refining the operand of a unary node whose type is computed from it. -/
theorem Refines.binop_ty2 {FS op a a' b b'} (F : Term → Term → Ty)
    (hF : ∀ x x' y y' : Term, x.ty = x'.ty → y.ty = y'.ty → F x y = F x' y')
    (ha : Refines FS a a') (hb : Refines FS b b') :
    Refines FS (.mk (.binop op a b) (F a b)) (.mk (.binop op a' b') (F a' b')) :=
  Refines.binop ha hb (fun w => hF _ _ _ _ (ty_of_refines ha (WT_binop.1 w).2.1)
    (ty_of_refines hb (WT_binop.1 w).2.2))

/-- The value of an operation whose right operand is a literal. -/
theorem BitOp.eval_lit_r {FS op f} (H : BitOp FS op f) {ρ a s T2 t v}
    (e : eval FS ρ (.mk (.binop op a (.mk (.bitVec s) T2)) t) = some v) :
    ∃ n x, eval FS ρ a = some (.bv n x) ∧ v = .bv n (f x (BitVec.ofInt n s)) ∧ 0 ≤ s ∧
      s < 2 ^ n := by
  obtain ⟨n, x, y, ea, eb, rfl⟩ := H.eval_eq_some e
  obtain ⟨rfl, h0, h1⟩ := lit_val₀ eb
  exact ⟨n, x, ea, rfl, h0, h1⟩

/-- The value of an operation whose left operand is a literal. -/
theorem toNat_ofInt_lit {k : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ k) :
    (BitVec.ofInt k z).toNat = z.toNat := toNat_ofInt_of_range h0 h1

theorem Val.bv_getLsbD {n m : Nat} {x : BitVec n} {y : BitVec m} (h : Val.bv n x = Val.bv m y)
    (t : Nat) : x.getLsbD t = y.getLsbD t := by
  cases h; rfl

/-- Checked arithmetic: well-typed like the unchecked one, and its value is the unchecked one
when it is not poison. -/
theorem eval_checked {c sovf uovf} {f : ∀ {n : Nat}, BitVec n → BitVec n → BitVec n}
    {a b : Option Val} {v : Val} (e : checkedOp c sovf uovf f a b = some v) :
    ∃ n x y, a = some (.bv n x) ∧ b = some (.bv n y) ∧ v = .bv n (f x y) := by
  obtain ⟨n, x, y, ea, eb, h⟩ := bvBin_eq_some.1 e
  refine ⟨n, x, y, ea, eb, ?_⟩
  split at h <;> simp at h; exact h.symm

theorem eval_add_eq_some {FS ρ c a b t v}
    (e : eval FS ρ (.mk (.binop (.add c) a b) t) = some v) :
    ∃ n x y, eval FS ρ a = some (.bv n x) ∧ eval FS ρ b = some (.bv n y) ∧ v = .bv n (x + y) := by
  rw [eval_binop (eval_WT e)] at e; exact eval_checked e

theorem eval_mul_eq_some {FS ρ c a b t v}
    (e : eval FS ρ (.mk (.binop (.mul c) a b) t) = some v) :
    ∃ n x y, eval FS ρ a = some (.bv n x) ∧ eval FS ρ b = some (.bv n y) ∧ v = .bv n (x * y) := by
  rw [eval_binop (eval_WT e)] at e; exact eval_checked e

theorem int_two_pow_cast (k : Nat) : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by push_cast; rfl

theorem ofInt_div_two_pow (L : Nat) {z : Int} (h : 0 ≤ z) (i : Nat) :
    BitVec.ofInt L (z / 2 ^ i) = BitVec.ofNat L (z.toNat >>> i) := by
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le h
  rw [← int_two_pow_cast, ← Int.natCast_ediv, BitVec.ofInt_natCast, Int.toNat_natCast,
    Nat.shiftRight_eq_div_pow]

/-! ### Shifts of literals -/

theorem signed_extract_eq_toInt {k : Nat} {l : Int} (hk : 0 < k) (h0 : 0 ≤ l) (h1 : l < 2 ^ k) :
    signed_extract l 0 k = (BitVec.ofInt k l).toInt := by
  rw [BitVec.toInt_eq_toNat_cond, toNat_ofInt_lit h0 h1]
  simp only [signed_extract, zasr, Int.toNat_zero, Int.pow_zero, Int.ediv_one, Int.toNat_natCast]
  rw [Int.emod_eq_of_lt h0 h1]
  have e1 := int_two_pow_cast k
  have e2 := int_two_pow_cast (k - 1)
  have e3 : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  split <;> split <;> omega

theorem two_pow_mono {z : Int} {a b : Nat} (h : z < 2 ^ a) (hab : a ≤ b) : z < 2 ^ b := by
  rw [← int_two_pow_cast] at h ⊢
  have := Nat.pow_le_pow_right (n := 2) (by omega) hab
  omega

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
