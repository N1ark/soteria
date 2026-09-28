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

theorem lit_val {FS ρ z T k x} (e : eval FS ρ (.mk (.bitVec z) T) = some (.bv k x)) {n : Int}
    (hT : T = .bitVector n) : k = n.toNat ∧ x = BitVec.ofInt k z := by
  rw [eval_lit' (eval_WT e) hT] at e
  simp at e; obtain ⟨rfl, h⟩ := e; exact ⟨rfl, (eq_of_heq h).symm⟩

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

theorem orElse_eq_some4 {α} {a b c d : Option α} {r : α} (h : (a <|> b <|> c <|> d) = some r) :
    a = some r ∨ b = some r ∨ c = some r ∨ d = some r := by
  rcases orElse_eq_some h with h | h; · exact Or.inl h
  rcases orElse_eq_some h with h | h; · exact Or.inr (Or.inl h)
  rcases orElse_eq_some h with h | h; · exact Or.inr (Or.inr (Or.inl h))
  exact Or.inr (Or.inr (Or.inr h))

theorem orElse_eq_some8 {α} {a b c d e f g i : Option α} {r : α}
    (h : (a <|> b <|> c <|> d <|> e <|> f <|> g <|> i) = some r) :
    a = some r ∨ b = some r ∨ c = some r ∨ d = some r ∨ e = some r ∨ f = some r ∨
      g = some r ∨ i = some r := by
  rcases orElse_eq_some4 h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  rcases orElse_eq_some4 h with h | h | h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  rcases orElse_eq_some h with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

/-! ## Zarith's bit operations on non-negative integers -/

theorem zland_ofNat (a b : Nat) : zland a b = ((a &&& b : Nat) : Int) := rfl
theorem zlor_ofNat (a b : Nat) : zlor a b = ((a ||| b : Nat) : Int) := rfl
theorem zlxor_ofNat (a b : Nat) : zlxor a b = ((a ^^^ b : Nat) : Int) := rfl

theorem ofInt_zland {w : Nat} {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    BitVec.ofInt w (zland a b) = BitVec.ofInt w a &&& BitVec.ofInt w b := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  simp [zland_ofNat, BitVec.ofNat_and]

theorem ofInt_zlor {w : Nat} {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    BitVec.ofInt w (zlor a b) = BitVec.ofInt w a ||| BitVec.ofInt w b := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  simp [zlor_ofNat, BitVec.ofNat_or]

theorem ofInt_zlxor {w : Nat} {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    BitVec.ofInt w (zlxor a b) = BitVec.ofInt w a ^^^ BitVec.ofInt w b := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  simp [zlxor_ofNat, BitVec.ofNat_xor]

theorem zland_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ zland a b := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  simp [zland_ofNat]

theorem zlor_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ zlor a b := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  simp [zlor_ofNat]

/-! ## Masks -/

theorem BitVec.or_and_absorb {k} {a b : BitVec k} (h : a &&& b = b) (z : BitVec k) :
    a ||| (z &&& b) = a ∧ a ||| (b &&& z) = a := by
  constructor <;>
  · ext i hi
    have h' := congrArg (fun v => v.getLsbD i) h
    simp at h' ⊢
    grind

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

theorem is_right_mask_eq {z : Int} (h : is_right_mask z = true) :
    z = 2 ^ (right_mask_size z).toNat - 1 := by
  unfold is_right_mask at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h0, h1⟩ := h
  simp only [popcount] at h1
  have h1' : popcountNat (z + 1).toNat = 1 := by exact_mod_cast h1
  obtain ⟨j, hj⟩ := popcountNat_eq_one h1'
  have e1 : ((2 ^ j : Nat) : Int) = (2 : Int) ^ j := by push_cast; rfl
  have : z + 1 = ((2 ^ j : Nat) : Int) := by omega
  simp only [right_mask_size, log2, hj, Nat.log2_two_pow, Int.toNat_natCast]
  omega

theorem covers_bitwidth_eq {n z : Int} (h : covers_bitwidth n z = true) :
    z = 2 ^ n.toNat - 1 := by
  simp only [covers_bitwidth, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [is_right_mask_eq h.1, h.2]

theorem ofInt_two_pow_sub_one (k : Nat) : BitVec.ofInt k (2 ^ k - 1) = BitVec.allOnes k := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_ofInt_of_range (by have := two_pow_pos' k; omega) (by omega), BitVec.toNat_allOnes]
  have : (1 : Nat) ≤ 2 ^ k := Nat.one_le_two_pow
  have e1 : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by push_cast; rfl
  omega

/-! ## Binary operations on bit-vectors of the same width -/

/-- [op] is a total operation [f] on bit-vectors of the same width. -/
structure BitOp (FS : FloatSem) (op : Binop) (f : ∀ {n : Nat}, BitVec n → BitVec n → BitVec n) :
    Prop where
  wt : ∀ a b t, Binop.WT op a b t ↔ (∃ n : Int, 0 < n ∧ a = .bitVector n) ∧ b = a ∧ t = a
  ev : ∀ a b, evBinop FS op a b = bvBin (fun x y => some (.bv _ (f x y))) a b

theorem BitOp.and {FS} : BitOp FS .bitAnd (· &&& ·) := ⟨fun _ _ _ => Iff.rfl, fun _ _ => rfl⟩
theorem BitOp.or {FS} : BitOp FS .bitOr (· ||| ·) := ⟨fun _ _ _ => Iff.rfl, fun _ _ => rfl⟩
theorem BitOp.xor {FS} : BitOp FS .bitXor (· ^^^ ·) := ⟨fun _ _ _ => Iff.rfl, fun _ _ => rfl⟩
theorem BitOp.shl {FS} : BitOp FS .shl (· <<< ·) := ⟨fun _ _ _ => Iff.rfl, fun _ _ => rfl⟩
theorem BitOp.lshr {FS} : BitOp FS .lShr (· >>> ·) := ⟨fun _ _ _ => Iff.rfl, fun _ _ => rfl⟩
theorem BitOp.ashr {FS} : BitOp FS .aShr (fun x y => x.sshiftRight' y) :=
  ⟨fun _ _ _ => Iff.rfl, fun _ _ => rfl⟩
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
theorem BitOp.lits {FS op f} (H : BitOp FS op f) {l r z : Int} {T1 T2 t}
    (hz : ∀ k : Nat, 0 < k → 0 ≤ l → l < 2 ^ k → 0 ≤ r → r < 2 ^ k →
      BitVec.ofInt k z = f (BitVec.ofInt k l) (BitVec.ofInt k r)) :
    Refines FS (.mk (.binop op (.mk (.bitVec l) T1) (.mk (.bitVec r) T2)) t)
      (mk_masked (size_of_ty T1) z) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨n, hn, h1, _, ht, _⟩ := H.WT.1 w
    simp only [Term.ty_mk] at h1; subst h1 ht
    exact ⟨mk_masked_WT hn, rfl⟩
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := H.WT.1 w
    simp only [Term.ty_mk] at h1 h2; subst h1 h2 ht
    obtain ⟨_, l0, l1⟩ := lit_inv w1 n rfl
    obtain ⟨_, r0, r1⟩ := lit_inv w2 n rfl
    rw [H.eval_of w (eval_lit' w1 rfl) (eval_lit' w2 rfl)] at e
    cases e
    rw [size_of_ty_bitVector, eval_mk_masked hn, hz _ (by omega) l0 l1 r0 r1]

/-- A literal left operand that is neutral. -/
theorem BitOp.lit_l {FS op f} (H : BitOp FS op f) {c : Int} {T1 b t}
    (hid : ∀ (n : Int) (y : BitVec n.toNat), 0 < n → T1 = .bitVector n → b.ty = .bitVector n →
      f (BitVec.ofInt n.toNat c) y = y) :
    Refines FS (.mk (.binop op (.mk (.bitVec c) T1) b) t) b := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨n, hn, h1, h2, ht, _, w2⟩ := H.WT.1 w
    exact ⟨w2, h2.trans ht.symm⟩
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := H.WT.1 w
    simp only [Term.ty_mk] at h1
    obtain ⟨k, x, y, ea, eb, rfl⟩ := H.eval_eq_some e
    rw [eval_lit' w1 h1] at ea; cases ea
    rw [eb, hid n y hn h1 h2]

/-- A literal right operand that is neutral. -/
theorem BitOp.lit_r {FS op f} (H : BitOp FS op f) {c : Int} {T2 a t}
    (hid : ∀ (n : Int) (x : BitVec n.toNat), 0 < n → a.ty = .bitVector n → T2 = .bitVector n →
      f x (BitVec.ofInt n.toNat c) = x) :
    Refines FS (.mk (.binop op a (.mk (.bitVec c) T2)) t) a := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨n, hn, h1, h2, ht, w1, _⟩ := H.WT.1 w
    exact ⟨w1, h1.trans ht.symm⟩
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := H.WT.1 w
    simp only [Term.ty_mk] at h2
    obtain ⟨k, x, y, ea, eb, rfl⟩ := H.eval_eq_some e
    rw [eval_lit' w2 h2] at eb; cases eb
    rw [ea, hid n x hn h1 h2]

/-- A literal left operand that is absorbing. -/
theorem BitOp.lit_l_abs {FS op f} (H : BitOp FS op f) {c : Int} {T1 b t}
    (hid : ∀ (n : Int) (y : BitVec n.toNat), 0 < n → T1 = .bitVector n → b.ty = .bitVector n →
      f (BitVec.ofInt n.toNat c) y = BitVec.ofInt n.toNat c) :
    Refines FS (.mk (.binop op (.mk (.bitVec c) T1) b) t) (.mk (.bitVec c) T1) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨n, hn, h1, h2, ht, w1, _⟩ := H.WT.1 w
    exact ⟨w1, h1.trans ht.symm⟩
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := H.WT.1 w
    simp only [Term.ty_mk] at h1
    obtain ⟨k, x, y, ea, eb, rfl⟩ := H.eval_eq_some e
    rw [eval_lit' w1 h1] at ea ⊢; cases ea
    rw [hid n y hn h1 h2]

/-- A literal right operand that is absorbing. -/
theorem BitOp.lit_r_abs {FS op f} (H : BitOp FS op f) {c : Int} {T2 a t}
    (hid : ∀ (n : Int) (x : BitVec n.toNat), 0 < n → a.ty = .bitVector n → T2 = .bitVector n →
      f x (BitVec.ofInt n.toNat c) = BitVec.ofInt n.toNat c) :
    Refines FS (.mk (.binop op a (.mk (.bitVec c) T2)) t) (.mk (.bitVec c) T2) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨n, hn, h1, h2, ht, _, w2⟩ := H.WT.1 w
    exact ⟨w2, h2.trans ht.symm⟩
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := H.WT.1 w
    simp only [Term.ty_mk] at h2
    obtain ⟨k, x, y, ea, eb, rfl⟩ := H.eval_eq_some e
    rw [eval_lit' w2 h2] at eb ⊢; cases eb
    rw [hid n x hn h1 h2]

/-- A literal left operand that absorbs the values that the right operand may take. -/
theorem BitOp.lit_l_abs_of {FS op f} (H : BitOp FS op f) {c N : Int} {T1 b t}
    (hN : ∀ n : Int, T1 = .bitVector n → b.ty = .bitVector n → t = .bitVector n → N = n)
    (hid : ∀ ρ (n : Int) (y : BitVec n.toNat), 0 < n → 0 ≤ c → T1 = .bitVector n →
      b.ty = .bitVector n → eval FS ρ b = some (.bv n.toNat y) →
      f (BitVec.ofInt n.toNat c) y = BitVec.ofInt n.toNat c) :
    Refines FS (.mk (.binop op (.mk (.bitVec c) T1) b) t) (mk_masked N c) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨n, hn, h1, h2, ht, _, _⟩ := H.WT.1 w
    obtain rfl := hN n h1 h2 ht
    exact ⟨mk_masked_WT hn, ht.symm⟩
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := H.WT.1 w
    obtain rfl := hN n h1 h2 ht
    obtain ⟨k, x, y, ea, eb, rfl⟩ := H.eval_eq_some e
    obtain ⟨rfl, rfl⟩ := lit_val ea h1
    rw [eval_mk_masked hn, hid ρ N y hn (lit_inv w1 N h1).2.1 h1 h2 eb]

/-- Refining the operands of an operation, keeping its type. -/
theorem BitOp.congr {FS op f} (_H : BitOp FS op f) {a a' b b' t} (ha : Refines FS a a')
    (hb : Refines FS b b') : Refines FS (.mk (.binop op a b) t) (.mk (.binop op a' b') t) :=
  Refines.binop ha hb (fun _ => rfl)

/-- Two literals of an associative and commutative operation are folded together. -/
theorem BitOp.lit_assoc {FS op f} (H : BitOp FS op f)
    (hA : ∀ {n} (x y z : BitVec n), f (f x y) z = f x (f y z))
    (hC : ∀ {n} (x y : BitVec n), f x y = f y x)
    {c1 c2 z N : Int} {T1 T2 T3 t t' x}
    (hN : ∀ n : Int, t = .bitVector n → N = n)
    (ht' : ∀ n : Int, x.ty = .bitVector n → t' = .bitVector n)
    (hz : ∀ k : Nat, 0 ≤ c1 → 0 ≤ c2 →
      BitVec.ofInt k z = f (BitVec.ofInt k c1) (BitVec.ofInt k c2)) :
    Refines FS (.mk (.binop op (.mk (.bitVec c1) T1) (.mk (.binop op x (.mk (.bitVec c2) T3)) T2)) t)
      (.mk (.binop op x (mk_masked N z)) t') := by
  have wt : ∀ {n : Int}, 0 < n → t = .bitVector n → x.ty = .bitVector n → x.WT →
      (Term.mk (.binop op x (mk_masked N z)) t').WT ∧ t' = t := by
    intro n hn ht hx wx
    obtain rfl := hN n ht
    exact ⟨H.WT.2 ⟨N, hn, hx, rfl, ht' N hx, wx, mk_masked_WT hn⟩, (ht' N hx).trans ht.symm⟩
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := H.WT.1 w
    obtain ⟨n', hn', hx, h3, h4, wx, w3⟩ := H.WT.1 w2
    simp only [Term.ty_mk] at h2 h4; subst h2; simp only [Ty.bitVector.injEq] at h4; subst h4
    exact wt hn ht hx wx
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := H.WT.1 w
    obtain ⟨n', hn', hx, h3, h4, wx, w3⟩ := H.WT.1 w2
    simp only [Term.ty_mk] at h1 h2 h4; subst h2; simp only [Ty.bitVector.injEq] at h4; subst h4
    obtain rfl := hN _ ht
    obtain ⟨k, x1, y, ea, eb, rfl⟩ := H.eval_eq_some e
    obtain ⟨k', u, x2, eu, ex2, hy⟩ := H.eval_eq_some eb
    simp at hy; obtain ⟨rfl, hy⟩ := hy; subst hy
    obtain ⟨rfl, _, _⟩ := lit_val₀ ea
    obtain ⟨_, c10, _⟩ := lit_val₀ ea
    obtain ⟨rfl, c20, _⟩ := lit_val₀ ex2
    obtain ⟨hk, -⟩ := lit_val ea h1
    subst hk
    rw [H.eval_of w' eu (eval_mk_masked hn), hz _ c10 c20, ← hA, hC u, hA]

/-- An idempotent operation. -/
theorem BitOp.same {FS op f} (H : BitOp FS op f) (hc : ∀ {n} (x : BitVec n), f x x = x)
    {a t} : Refines FS (.mk (.binop op a a) t) a := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := H.WT.1 w
    exact ⟨w1, h1.trans ht.symm⟩
  · obtain ⟨k, x, y, ea, eb, rfl⟩ := H.eval_eq_some e
    rw [ea] at eb; simp at eb; subst eb; rw [ea, hc]

/-- A commutative operation. -/
theorem BitOp.comm {FS op f} (H : BitOp FS op f) (hc : ∀ {n} (x y : BitVec n), f x y = f y x)
    {a b t} : Refines FS (.mk (.binop op a b) t) (.mk (.binop op b a) t) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := H.WT.1 w
    exact ⟨H.WT.2 ⟨n, hn, h2, h1, ht, w2, w1⟩, rfl⟩
  · obtain ⟨k, x, y, ea, eb, rfl⟩ := H.eval_eq_some e
    rw [H.eval_of w' eb ea, hc]

theorem BitOp.commut {FS op f} (H : BitOp FS op f) (hc : ∀ {n} (x y : BitVec n), f x y = f y x)
    {O : Ops} {a b t} : Refines FS (.mk (.binop op a b) t) (.mk (mk_commut_binop O op a b) t) := by
  unfold mk_commut_binop; split
  · exact Refines.refl
  · exact H.comm hc


/-- A node can be given another name of its type. -/
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
theorem BitOp.ite_r {FS op f} (H : BitOp FS op f) {c g l r T2 t} :
    Refines FS (.mk (.binop op c (.mk (.triop .ite g l r) T2)) t)
      (.mk (.triop .ite g (.mk (.binop op c l) t) (.mk (.binop op c r) t)) t) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := H.WT.1 w
    obtain ⟨hg, hr, hl, wg, wl, wr⟩ := WT_ite.1 w2
    simp only [Term.ty_mk] at h2 hl; subst h2
    refine ⟨WT_ite.2 ⟨hg, rfl, rfl, wg, H.WT.2 ⟨n, hn, h1, hl.symm, ht, w1, wl⟩,
      H.WT.2 ⟨n, hn, h1, hr.trans hl.symm, ht, w1, wr⟩⟩, rfl⟩
  · obtain ⟨k, x, y, ea, eb, rfl⟩ := H.eval_eq_some e
    obtain ⟨_, _, _, _, wa, wb⟩ := WT_ite.1 w'
    rw [eval_ite (WT_binop.1 w).2.2] at eb
    rw [eval_ite w']
    split at eb
    · exact H.eval_of wa ea eb
    · exact H.eval_of wb ea eb
    · simp at eb

/-- An operation with an ite as its left operand is pushed into the branches. -/
theorem BitOp.ite_l {FS op f} (H : BitOp FS op f) {c g l r T1 t} :
    Refines FS (.mk (.binop op (.mk (.triop .ite g l r) T1) c) t)
      (.mk (.triop .ite g (.mk (.binop op l c) t) (.mk (.binop op r c) t)) t) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := H.WT.1 w
    obtain ⟨hg, hr, hl, wg, wl, wr⟩ := WT_ite.1 w1
    simp only [Term.ty_mk] at h1 hl; subst h1
    refine ⟨WT_ite.2 ⟨hg, rfl, rfl, wg, H.WT.2 ⟨n, hn, hl.symm, h2, ht, wl, w2⟩,
      H.WT.2 ⟨n, hn, hr.trans hl.symm, h2, ht, wr, w2⟩⟩, rfl⟩
  · obtain ⟨k, x, y, ea, eb, rfl⟩ := H.eval_eq_some e
    obtain ⟨_, _, _, _, wa, wb⟩ := WT_ite.1 w'
    rw [eval_ite (WT_binop.1 w).2.1] at ea
    rw [eval_ite w']
    split at ea
    · exact H.eval_of wa ea eb
    · exact H.eval_of wb ea eb
    · simp at ea


/-! ## Booleans as bit-vectors -/

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

theorem eval_bvOfBool_val {FS ρ m g T k y}
    (e : eval FS ρ (.mk (.unop (.bvOfBool m) g) T) = some (.bv k y)) : y = 0 ∨ y = 1 := by
  obtain ⟨b, _, hv⟩ := eval_bvOfBool e
  simp at hv; obtain ⟨rfl, hv⟩ := hv; cases eq_of_heq hv; cases b <;> simp

/-- A literal left operand that is neutral on the values the right operand may take. -/
theorem BitOp.lit_l_of {FS op f} (H : BitOp FS op f) {c : Int} {T1 b t}
    (hid : ∀ ρ (n : Int) (y : BitVec n.toNat), 0 < n → T1 = .bitVector n →
      b.ty = .bitVector n → eval FS ρ b = some (.bv n.toNat y) →
      f (BitVec.ofInt n.toNat c) y = y) :
    Refines FS (.mk (.binop op (.mk (.bitVec c) T1) b) t) b := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨n, hn, h1, h2, ht, _, w2⟩ := H.WT.1 w
    exact ⟨w2, h2.trans ht.symm⟩
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := H.WT.1 w
    simp only [Term.ty_mk] at h1
    obtain ⟨k, x, y, ea, eb, rfl⟩ := H.eval_eq_some e
    obtain ⟨rfl, rfl⟩ := lit_val ea h1
    rw [eb, hid ρ n y hn h1 h2 eb]

/-- A literal right operand that is neutral on the values the left operand may take. -/
theorem BitOp.lit_r_of {FS op f} (H : BitOp FS op f) {c : Int} {T2 a t}
    (hid : ∀ ρ (n : Int) (x : BitVec n.toNat), 0 < n → a.ty = .bitVector n →
      T2 = .bitVector n → eval FS ρ a = some (.bv n.toNat x) →
      f x (BitVec.ofInt n.toNat c) = x) :
    Refines FS (.mk (.binop op a (.mk (.bitVec c) T2)) t) a := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨n, hn, h1, h2, ht, w1, _⟩ := H.WT.1 w
    exact ⟨w1, h1.trans ht.symm⟩
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := H.WT.1 w
    simp only [Term.ty_mk] at h2
    obtain ⟨k, x, y, ea, eb, rfl⟩ := H.eval_eq_some e
    obtain ⟨rfl, rfl⟩ := lit_val eb h2
    rw [ea, hid ρ n x hn h1 h2 ea]

/-- The operation on two booleans cast to bit-vectors. -/
theorem BitOp.of_bools {FS op f} (H : BitOp FS op f) {m1 m2 T1 T2 t b1 b2 N} {B : Term}
    (g : Bool → Bool → Bool)
    (hN : ∀ n : Int, T1 = .bitVector n → m1 = n → N = n)
    (hB : b1.WT → b2.WT → b1.ty = .bool → b2.ty = .bool → B.WT ∧ B.ty = .bool)
    (hBe : ∀ ρ x1 x2, b1.ty = .bool → b2.ty = .bool → eval FS ρ b1 = some (.bool x1) →
      eval FS ρ b2 = some (.bool x2) → eval FS ρ B = some (.bool (g x1 x2)))
    (hf : ∀ (k : Nat) x1 x2, 0 < k →
      f (if x1 then (1 : BitVec k) else 0) (if x2 then 1 else 0) = if g x1 x2 then 1 else 0) :
    Refines FS (.mk (.binop op (.mk (.unop (.bvOfBool m1) b1) T1) (.mk (.unop (.bvOfBool m2) b2) T2)) t)
      (.mk (.unop (.bvOfBool N) B) (.bitVector N)) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := H.WT.1 w
    obtain ⟨_, g1, e1, w1⟩ := WT_bvOfBool.1 w1
    obtain ⟨_, g2, e2, w2⟩ := WT_bvOfBool.1 w2
    simp only [Term.ty_mk] at h1
    obtain rfl := hN n h1 (by rw [h1] at e1; simp at e1; exact e1.symm)
    obtain ⟨wB, tB⟩ := hB w1 w2 g1 g2
    exact ⟨WT_bvOfBool.2 ⟨hn, tB, rfl, wB⟩, ht.symm⟩
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := H.WT.1 w
    simp only [Term.ty_mk] at h1 h2
    obtain ⟨_, g1, e1, _⟩ := WT_bvOfBool.1 w1
    obtain rfl := hN n h1 (by rw [h1] at e1; simp at e1; exact e1.symm)
    obtain ⟨_, g2, e2, _⟩ := WT_bvOfBool.1 w2
    subst e1 e2; simp only [Ty.bitVector.injEq] at h1 h2; subst h1 h2
    obtain ⟨k, x, y, ea, eb, rfl⟩ := H.eval_eq_some e
    obtain ⟨x1, ex1, hx⟩ := eval_bvOfBool ea
    obtain ⟨x2, ex2, hy⟩ := eval_bvOfBool eb
    simp at hx hy; obtain ⟨rfl, hx⟩ := hx; obtain ⟨-, hy⟩ := hy
    subst hx hy
    rw [eval_bvOfBool' w' (hBe ρ x1 x2 g1 g2 ex1 ex2)]
    congr 2; refine (hf _ x1 x2 ?_).symm; omega

/-! ## Extraction, extension and concatenation -/

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
theorem Refines.unop_ty {FS op a a'} (F : Term → Ty) (hF : ∀ x y : Term, x.ty = y.ty → F x = F y)
    (ha : Refines FS a a') :
    Refines FS (.mk (.unop op a) (F a)) (.mk (.unop op a') (F a')) :=
  Refines.unop ha (fun w => hF _ _ (ty_of_refines ha (WT_unop.1 w).2))

/-- Refining the operands of a binary node whose type is computed from its operands. -/
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
theorem BitOp.eval_lit_l {FS op f} (H : BitOp FS op f) {ρ b s T1 t v}
    (e : eval FS ρ (.mk (.binop op (.mk (.bitVec s) T1) b) t) = some v) :
    ∃ n y, eval FS ρ b = some (.bv n y) ∧ v = .bv n (f (BitVec.ofInt n s) y) ∧ 0 ≤ s ∧
      s < 2 ^ n := by
  obtain ⟨n, x, y, ea, eb, rfl⟩ := H.eval_eq_some e
  obtain ⟨rfl, h0, h1⟩ := lit_val₀ ea
  exact ⟨n, y, eb, rfl, h0, h1⟩

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

theorem ofInt_zshiftl {k : Nat} {l r : Int} (h0 : 0 ≤ l) (r0 : 0 ≤ r) (r1 : r < 2 ^ k) :
    BitVec.ofInt k (zshiftl l r) = BitVec.ofInt k l <<< BitVec.ofInt k r := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  rw [BitVec.shiftLeft_eq', toNat_ofInt_lit r0 r1, zshiftl, ← int_two_pow_cast]
  apply BitVec.eq_of_toNat_eq
  rw [← Int.natCast_mul, BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod]

theorem ofInt_zasr {k : Nat} {l r : Int} (h0 : 0 ≤ l) (h1 : l < 2 ^ k) (r0 : 0 ≤ r)
    (r1 : r < 2 ^ k) :
    BitVec.ofInt k (zasr l r) = BitVec.ofInt k l >>> BitVec.ofInt k r := by
  rw [BitVec.ushiftRight_eq', toNat_ofInt_lit r0 r1, zasr, ofInt_div_two_pow _ h0]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofInt_lit h0 h1, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have : l.toNat < 2 ^ k := by
    have := int_two_pow_cast k; omega
  exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) this

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

theorem ofInt_zasr_signed {k : Nat} {l r : Int} (hk : 0 < k) (h0 : 0 ≤ l) (h1 : l < 2 ^ k)
    (r0 : 0 ≤ r) (r1 : r < 2 ^ k) :
    BitVec.ofInt k (zasr (signed_extract l 0 k) r) =
      (BitVec.ofInt k l).sshiftRight' (BitVec.ofInt k r) := by
  rw [signed_extract_eq_toInt hk h0 h1, zasr, BitVec.sshiftRight_eq', toNat_ofInt_lit r0 r1,
    ← int_two_pow_cast, ← Int.shiftRight_eq_div_pow, ← BitVec.toInt_sshiftRight,
    BitVec.ofInt_toInt]

/-- A binary operation on literals is folded (at the width of the operation). -/
theorem BitOp.lits' {FS op f} (H : BitOp FS op f) {l r z : Int} {T1 T2 t} {N : Int}
    (hN : ∀ n : Int, T1 = .bitVector n → N = n)
    (hz : ∀ n : Int, T1 = .bitVector n → 0 < n → 0 ≤ l → l < 2 ^ n.toNat → 0 ≤ r →
      r < 2 ^ n.toNat →
      BitVec.ofInt n.toNat z = f (BitVec.ofInt n.toNat l) (BitVec.ofInt n.toNat r)) :
    Refines FS (.mk (.binop op (.mk (.bitVec l) T1) (.mk (.bitVec r) T2)) t) (mk_masked N z) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨n, hn, h1, _, ht, _⟩ := H.WT.1 w
    simp only [Term.ty_mk] at h1; obtain rfl := hN n h1; subst h1 ht
    exact ⟨mk_masked_WT hn, rfl⟩
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := H.WT.1 w
    simp only [Term.ty_mk] at h1 h2; obtain rfl := hN n h1; subst h1 h2 ht
    obtain ⟨_, l0, l1⟩ := lit_inv w1 N rfl
    obtain ⟨_, r0, r1⟩ := lit_inv w2 N rfl
    rw [H.eval_of w (eval_lit' w1 rfl) (eval_lit' w2 rfl)] at e
    cases e
    rw [eval_mk_masked hn, hz _ rfl hn l0 l1 r0 r1]

/-- A shift by a literal of a bitwise operation with a literal mask is the operation on the
shifted operand and the shifted mask. -/
theorem shift_distrib {FS op f sop g} (H : BitOp FS op f) (S : BitOp FS sop g)
    (hd : ∀ {k} (X M Z : BitVec k), g (f X M) Z = f (g X Z) (g M Z))
    {I x : Term} {m s z N : Int} {T3 T4 T5 T6 : Ty}
    (hwt : I.WT → I.ty = x.ty ∧ x.WT)
    (hev : ∀ ρ k u, eval FS ρ I = some (.bv k u) →
      ∃ X, eval FS ρ x = some (.bv k X) ∧ u = f X (BitVec.ofInt k m) ∧ 0 ≤ m ∧ m < 2 ^ k)
    (hz : ∀ k : Nat, 0 ≤ m → m < 2 ^ k → 0 ≤ s → s < 2 ^ k →
      BitVec.ofInt k z = g (BitVec.ofInt k m) (BitVec.ofInt k s))
    (hN : ∀ n, I.ty = .bitVector n → N = n)
    (hT5 : ∀ n, x.ty = .bitVector n → T5 = .bitVector n)
    (hT6 : ∀ n, x.ty = .bitVector n → T6 = .bitVector n) :
    Refines FS (.mk (.binop sop I (.mk (.bitVec s) T3)) T4)
      (.mk (.binop op (.mk (.binop sop x (.mk (.bitVec s) T3)) T5) (mk_masked N z)) T6) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := S.WT.1 w
    obtain ⟨hx, wx⟩ := hwt w1
    rw [hx] at h1
    obtain rfl := hN n (hx.trans h1)
    refine ⟨H.WT.2 ⟨N, hn, hT5 N h1, rfl, hT6 N h1, S.WT.2 ⟨N, hn, h1, h2, hT5 N h1, wx, w2⟩,
      mk_masked_WT hn⟩, ?_⟩
    simp [hT6 N h1, ht]
  · obtain ⟨_, w1, w2⟩ := WT_binop.1 w'
    obtain ⟨n, hn, hI, h2, ht, wI, wl⟩ := S.WT.1 w
    obtain rfl := hN n hI
    obtain ⟨k, u, y, eI, el, rfl⟩ := S.eval_eq_some e
    obtain ⟨u', hu'⟩ := eval_bv eI hI
    obtain ⟨rfl, rfl⟩ := Val.bv_inj hu'
    obtain ⟨rfl, s0, s1⟩ := lit_val₀ el
    obtain ⟨X, ex, rfl, m0, m1⟩ := hev ρ _ _ eI
    rw [H.eval_of w' (S.eval_of w1 ex el) (eval_mk_masked hn), hz _ m0 m1 s0 s1, hd]

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

theorem lshr_mask_bits {k : Nat} {n s mask : Int} (s0 : 0 ≤ s) (m0 : 0 ≤ mask) (hk : n = k)
    (hm : zland mask (zshiftl 1 (n - s) - 1) = zshiftl 1 (n - s) - 1)
    (X : BitVec k) : X >>> s.toNat &&& BitVec.ofInt k mask = X >>> s.toNat := by
  have l0 : 0 ≤ zshiftl 1 (n - s) - 1 := by
    simp only [zshiftl, Int.one_mul]; have := two_pow_pos' (n - s).toNat; omega
  have hb := congrArg (fun v => v.getLsbD) (ofInt_zland (w := k) m0 l0)
  simp only [hm] at hb
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_ushiftRight]
  by_cases h : i < (n - s).toNat
  · have := congrFun hb i
    simp only [BitVec.getLsbD_and, getLsbD_ofInt_lowmask, decide_eq_true hi, decide_eq_true h,
      Bool.and_true] at this
    rw [BitVec.getElem_eq_testBit_toNat, ← BitVec.getLsbD, ← this]; simp
  · rw [BitVec.getElem_eq_testBit_toNat, ← BitVec.getLsbD, BitVec.getLsbD_of_ge _ _ (by omega)]
    simp

theorem and_distrib_self {w : Nat} (m l r : BitVec w) :
    m &&& (l &&& r) = (m &&& l) &&& (m &&& r) := by
  ext i hi; simp only [BitVec.getElem_and]; cases m[i] <;> simp

/-- `M & (L & R)`, with `M` a literal on either side, is `(M & L) & (M & R)`. -/
theorem and_mask_and {FS : FloatSem} {c : Int} {l r A B : Term} {T1 T2 T : Ty} {N : Int}
    (hshape : (A = .mk (.bitVec c) T1 ∧ B = .mk (.binop .bitAnd l r) T2) ∨
      (B = .mk (.bitVec c) T1 ∧ A = .mk (.binop .bitAnd l r) T2))
    (hN : ∀ n, T1 = .bitVector n → T2 = .bitVector n → N = n) :
    Refines FS (.mk (.binop .bitAnd A B) T)
      (bv_and.spec (bv_and.spec (mk_bv N c) l) (bv_and.spec (mk_bv N c) r)) := by
  have key : (Term.mk (.binop .bitAnd A B) T).WT → ∃ n : Int, 0 < n ∧ T1 = .bitVector n ∧
      T2 = .bitVector n ∧ T = .bitVector n ∧ l.ty = .bitVector n ∧ r.ty = .bitVector n ∧ l.WT ∧
      r.WT ∧ 0 ≤ c ∧ c < 2 ^ n.toNat := by
    intro w
    obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := (BitOp.and (FS := FS)).WT.1 w
    rcases hshape with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨n', hn', hl, hr, ht', wl, wr⟩ := (BitOp.and (FS := FS)).WT.1 w2
      simp only [Term.ty_mk] at h1 h2; subst h1 h2
      simp only [Ty.bitVector.injEq] at ht'; subst ht'
      exact ⟨n, hn, rfl, rfl, ht, hl, hr, wl, wr, (lit_inv w1 n rfl).2⟩
    · obtain ⟨n', hn', hl, hr, ht', wl, wr⟩ := (BitOp.and (FS := FS)).WT.1 w1
      simp only [Term.ty_mk] at h1 h2; subst h1 h2
      simp only [Ty.bitVector.injEq] at ht'; subst ht'
      exact ⟨n, hn, rfl, rfl, ht, hl, hr, wl, wr, (lit_inv w2 n rfl).2⟩
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨n, hn, rfl, rfl, rfl, hl, hr, wl, wr, c0, c1⟩ := key w
    obtain rfl := hN n rfl rfl
    have wm : (mk_bv N c).WT := mk_masked_WT hn
    refine ⟨(BitOp.and (FS := FS)).WT.2 ⟨N, hn, by simp [bv_and.spec, mk_bv],
      by simp [bv_and.spec, mk_bv], by simp [bv_and.spec, mk_bv],
      (BitOp.and (FS := FS)).WT.2 ⟨N, hn, rfl, hl, by simp [mk_bv], wm, wl⟩,
      (BitOp.and (FS := FS)).WT.2 ⟨N, hn, rfl, hr, by simp [mk_bv], wm, wr⟩⟩, ?_⟩
    simp [bv_and.spec, mk_bv]
  · obtain ⟨n, hn, rfl, rfl, rfl, hl, hr, wl, wr, c0, c1⟩ := key w
    obtain rfl := hN n rfl rfl
    obtain ⟨_, w1, w2⟩ := WT_binop.1 w'
    have em : eval FS ρ (mk_bv N c) = some (.bv N.toNat (BitVec.ofInt _ c)) := eval_mk_masked hn
    obtain ⟨k, x, y, ea, eb, rfl⟩ := BitOp.and.eval_eq_some e
    rcases hshape with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨k', L, R, el, er, hy⟩ := BitOp.and.eval_eq_some eb
      obtain ⟨rfl, rfl⟩ := Val.bv_inj hy
      obtain ⟨rfl, rfl⟩ := lit_val ea rfl
      simp only [bv_and.spec] at w1 w2 w' ⊢
      rw [BitOp.and.eval_of w' (BitOp.and.eval_of w1 em el) (BitOp.and.eval_of w2 em er)]
      rw [and_distrib_self (BitVec.ofInt _ c) L R]
    · obtain ⟨k', L, R, el, er, hy⟩ := BitOp.and.eval_eq_some ea
      obtain ⟨rfl, rfl⟩ := Val.bv_inj hy
      obtain ⟨rfl, rfl⟩ := lit_val eb rfl
      simp only [bv_and.spec] at w1 w2 w' ⊢
      rw [BitOp.and.eval_of w' (BitOp.and.eval_of w1 em el) (BitOp.and.eval_of w2 em er)]
      rw [BitVec.and_comm (L &&& R), and_distrib_self (BitVec.ofInt _ c) L R]

theorem eval_ite_eq_some {FS ρ g a b t v} (e : eval FS ρ (.mk (.triop .ite g a b) t) = some v) :
    ∃ c, eval FS ρ g = some (.bool c) ∧ eval FS ρ (if c then a else b) = some v := by
  rw [eval_ite (eval_WT e)] at e
  rcases eg : eval FS ρ g with _ | ⟨c | _ | _ | _ | _ | _⟩ <;> rw [eg] at e <;> (try simp at e)
  exact ⟨c, rfl, by cases c <;> simpa using e⟩

/-! ## Shifts of shifts -/
theorem BitOp.shift_shift {FS op f} (H : BitOp FS op f) {v : Term} {s1 s2 : Int}
    {T1 T2 T3 : Ty} {g : Int → Int}
    (hg : ∀ k : Nat, 0 < k → ∀ x : BitVec k, 0 ≤ s1 → s1 < 2 ^ k → 0 ≤ s2 → s2 < 2 ^ k →
      f (f x (BitVec.ofInt k s1)) (BitVec.ofInt k s2) = f x (BitVec.ofInt k (g k))) :
    Refines FS (.mk (.binop op (.mk (.binop op v (.mk (.bitVec s1) T1)) T2) (.mk (.bitVec s2) T3)) T2)
      (.mk (.binop op v (mk_masked (size_of_ty T2) (g (size_of_ty T2)))) v.ty) := by
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := H.WT.1 w
    obtain ⟨n', hn', hv, h3, h4, wv, w3⟩ := H.WT.1 w1
    simp only [Term.ty_mk] at h1 h4; subst h1; simp only [Ty.bitVector.injEq] at h4; subst h4
    exact ⟨H.WT.2 ⟨n, hn, hv, by simp [size_of_ty], hv, wv, mk_masked_WT (by simpa [size_of_ty] using hn)⟩,
      by simp [hv]⟩
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := H.WT.1 w
    obtain ⟨n', hn', hv, h3, h4, wv, w3⟩ := H.WT.1 w1
    simp only [Term.ty_mk] at h1 h4; subst h1; simp only [Ty.bitVector.injEq] at h4; subst h4
    obtain ⟨k, x', ex, rfl, s20, s21⟩ := H.eval_lit_r e
    obtain ⟨k', y, ey, hb, s10, s11⟩ := H.eval_lit_r ex
    obtain ⟨rfl, rfl⟩ := Val.bv_inj hb
    obtain ⟨y', hy⟩ := eval_bv ey hv
    obtain ⟨rfl, -⟩ := Val.bv_inj hy
    have hk : ((n.toNat : Nat) : Int) = n := by omega
    simp only [size_of_ty] at w' ⊢
    rw [H.eval_of w' ey (eval_mk_masked hn), hg _ (by omega) y s10 s11 s20 s21, hk]

theorem lt_two_pow_int (k : Nat) : (k : Int) < 2 ^ k := by
  have := Nat.lt_two_pow_self (n := k); have := int_two_pow_cast k; omega

theorem zmin_eq_min (a b : Int) : zmin a b = min a b := by
  unfold zmin; split <;> simp_all <;> omega

theorem shl_shl_nat {k : Nat} (x : BitVec k) (a b : Nat) :
    x <<< a <<< b = x <<< min (a + b) k := by
  rw [← BitVec.shiftLeft_add]
  by_cases h : a + b ≤ k
  · rw [Nat.min_eq_left h]
  · rw [BitVec.shiftLeft_eq_zero (by omega), BitVec.shiftLeft_eq_zero (by omega)]

theorem lshr_lshr_nat {k : Nat} (x : BitVec k) (a b : Nat) :
    x >>> a >>> b = x >>> min (a + b) k := by
  ext i hi
  simp only [BitVec.getElem_ushiftRight, BitVec.getLsbD_ushiftRight]
  by_cases h : a + b ≤ k
  · rw [Nat.min_eq_left h, Nat.add_assoc]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega)]

theorem ashr_big_nat {k : Nat} (x : BitVec k) {m : Nat} (h : k - 1 ≤ m) :
    x.sshiftRight m = x.sshiftRight (k - 1) := by
  ext i hi
  simp only [BitVec.getElem_sshiftRight]
  by_cases h1 : m + i < k
  · have : m = k - 1 := by omega
    subst this; rfl
  · simp only [h1, ↓reduceDIte]
    by_cases h2 : k - 1 + i < k
    · simp only [h2, ↓reduceDIte, BitVec.msb_eq_getLsbD_last]
      have : i = 0 := by omega
      subst this; rw [BitVec.getLsbD_eq_getElem (by omega)]; rfl
    · simp only [h2, ↓reduceDIte]

theorem ashr_ashr_nat {k : Nat} (x : BitVec k) (a b : Nat) :
    (x.sshiftRight a).sshiftRight b = x.sshiftRight (min (a + b) (k - 1)) := by
  rw [← BitVec.sshiftRight_add]
  by_cases h : a + b ≤ k - 1
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), ashr_big_nat x (by omega)]

theorem shl_shl_lits {k : Nat} (x : BitVec k) {s1 s2 : Int} (s10 : 0 ≤ s1) (s11 : s1 < 2 ^ k)
    (s20 : 0 ≤ s2) (s21 : s2 < 2 ^ k) :
    x <<< BitVec.ofInt k s1 <<< BitVec.ofInt k s2 = x <<< BitVec.ofInt k (zmin (s1 + s2) k) := by
  have hk := lt_two_pow_int k
  have m0 : 0 ≤ zmin (s1 + s2) k := by rw [zmin_eq_min]; omega
  have m1 : zmin (s1 + s2) k < 2 ^ k := by rw [zmin_eq_min]; omega
  simp only [BitVec.shiftLeft_eq', toNat_ofInt_lit s10 s11, toNat_ofInt_lit s20 s21,
    toNat_ofInt_lit m0 m1, shl_shl_nat]
  congr 1; rw [zmin_eq_min]; omega

theorem lshr_lshr_lits {k : Nat} (x : BitVec k) {s1 s2 : Int} (s10 : 0 ≤ s1) (s11 : s1 < 2 ^ k)
    (s20 : 0 ≤ s2) (s21 : s2 < 2 ^ k) :
    x >>> BitVec.ofInt k s1 >>> BitVec.ofInt k s2 = x >>> BitVec.ofInt k (zmin (s1 + s2) k) := by
  have hk := lt_two_pow_int k
  have m0 : 0 ≤ zmin (s1 + s2) k := by rw [zmin_eq_min]; omega
  have m1 : zmin (s1 + s2) k < 2 ^ k := by rw [zmin_eq_min]; omega
  simp only [BitVec.ushiftRight_eq', toNat_ofInt_lit s10 s11, toNat_ofInt_lit s20 s21,
    toNat_ofInt_lit m0 m1, lshr_lshr_nat]
  congr 1; rw [zmin_eq_min]; omega

theorem ashr_ashr_lits {k : Nat} (hk0 : 0 < k) (x : BitVec k) {s1 s2 : Int} (s10 : 0 ≤ s1)
    (s11 : s1 < 2 ^ k) (s20 : 0 ≤ s2) (s21 : s2 < 2 ^ k) :
    (x.sshiftRight' (BitVec.ofInt k s1)).sshiftRight' (BitVec.ofInt k s2) =
      x.sshiftRight' (BitVec.ofInt k (zmin (s1 + s2) (k - 1))) := by
  have hk := lt_two_pow_int k
  have m0 : 0 ≤ zmin (s1 + s2) (k - 1) := by rw [zmin_eq_min]; omega
  have m1 : zmin (s1 + s2) (k - 1) < 2 ^ k := by rw [zmin_eq_min]; omega
  simp only [BitVec.sshiftRight_eq', toNat_ofInt_lit s10 s11, toNat_ofInt_lit s20 s21,
    toNat_ofInt_lit m0 m1, ashr_ashr_nat]
  congr 1; rw [zmin_eq_min]; omega

/-! ## Or of an extension and a shifted extension -/

theorem extend_shl_WT {nx k base tail s T1 T4 T5 T2 T}
    (w : (Term.mk (.binop .bitOr (.mk (.unop (.bvExtend false nx) base) T1)
      (.mk (.binop .shl (.mk (.unop (.bvExtend false k) tail) T4) (.mk (.bitVec s) T5)) T2)) T).WT) :
    ∃ nb nt : Int, 0 < nb ∧ 0 < nt ∧ base.ty = .bitVector nb ∧ tail.ty = .bitVector nt ∧
      0 ≤ nx ∧ 0 ≤ k ∧ nb + nx = nt + k ∧ T1 = .bitVector (nb + nx) ∧ T = T1 ∧
      base.WT ∧ tail.WT := by
  obtain ⟨⟨⟨n, hn, h1⟩, h2, h3⟩, w1, w2⟩ := WT_binop.1 w
  obtain ⟨nb, hnb, hb, hnx, hT1, wb⟩ := WT_extend.1 w1
  obtain ⟨⟨⟨n', hn', h4⟩, h5, h6⟩, w3, w4⟩ := WT_binop.1 w2
  obtain ⟨nt, hnt, ht, hk, hT4, wt⟩ := WT_extend.1 w3
  simp only [Term.ty_mk, Ty.sort] at h1 h2 h3 h4 h5 h6
  subst h1 h4 h2
  simp only [Ty.bitVector.injEq] at hT1 hT4 h6
  subst h6
  exact ⟨nb, nt, hnb, hnt, hb, ht, hnx, hk, by omega, by rw [hT1], h3, wb, wt⟩

theorem extend_shl_eval {FS ρ nx k base tail s T1 T4 T5 T2 T v}
    (hs : s = size base)
    (e : eval FS ρ (.mk (.binop .bitOr (.mk (.unop (.bvExtend false nx) base) T1)
      (.mk (.binop .shl (.mk (.unop (.bvExtend false k) tail) T4) (.mk (.bitVec s) T5)) T2)) T) =
        some v) :
    ∃ nb nt : Int, ∃ xb : BitVec nb.toNat, ∃ xt : BitVec nt.toNat, ∃ N, ∃ Y : BitVec N,
      N = nb.toNat + nx.toNat ∧ 0 < nb ∧ 0 < nt ∧ base.ty = .bitVector nb ∧
      tail.ty = .bitVector nt ∧ 0 ≤ nx ∧ 0 ≤ k ∧ nb + nx = nt + k ∧ T1 = .bitVector (nb + nx) ∧
      eval FS ρ base = some (.bv nb.toNat xb) ∧ eval FS ρ tail = some (.bv nt.toNat xt) ∧
      v = .bv N Y ∧ ∀ i, Y.getLsbD i = (decide (i < N) &&
        if i < nb.toNat then xb.getLsbD i else xt.getLsbD (i - nb.toNat)) := by
  obtain ⟨nb, nt, hnb, hnt, hb, ht, hnx, hk, hsum, hT1, hT, wb, wt⟩ := extend_shl_WT (eval_WT e)
  obtain ⟨n, x, y, e1, e2, rfl⟩ := BitOp.or.eval_eq_some e
  obtain ⟨nb', xb, -, hb', -, -, eb, hx⟩ := eval_extend e1
  obtain ⟨n', x2, e3, hy, s0, s1⟩ := BitOp.shl.eval_lit_r e2
  obtain ⟨nt', xt, -, ht', -, -, et, hx2⟩ := eval_extend e3
  rw [hb] at hb'; rw [ht] at ht'
  simp only [Ty.bitVector.injEq] at hb' ht'; subst hb' ht'
  obtain ⟨hn, -⟩ := Val.bv_inj hx
  obtain ⟨hn', -⟩ := Val.bv_inj hy
  obtain ⟨hn'', -⟩ := Val.bv_inj hx2
  subst hs
  simp only [size, ty, hb, size_of_ty] at s0 s1
  refine ⟨nb, nt, xb, xt, n, x ||| y, by omega, hnb, hnt, hb, ht, hnx, hk, hsum, hT1, eb, et, rfl,
    fun i => ?_⟩
  rw [BitVec.getLsbD_or, Val.bv_getLsbD hx, Val.bv_getLsbD hy]
  have hsz : size base = nb := by simp [size, ty, hb, size_of_ty]
  rw [hsz, BitVec.shiftLeft_eq', toNat_ofInt_lit s0 s1, BitVec.getLsbD_shiftLeft,
    Val.bv_getLsbD hx2]
  simp only [Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_setWidth]
  subst hn hn''
  by_cases h1 : i < nb.toNat + nx.toNat
  · by_cases h2 : i < nb.toNat
    · simp [h1, h2]
    · have h3 : i - nb.toNat < nt.toNat + k.toNat := by omega
      have h4 : i < nt.toNat + k.toNat := by omega
      simp [h1, h2, h3, h4, BitVec.getLsbD_of_ge xb i (by omega)]
  · have h1' : ¬ i < nt.toNat + k.toNat := by omega
    simp only [h1, h1', decide_false, Bool.false_and, Bool.and_false, Bool.or_false]

/-! ## A mask of an or with a literal -/

theorem and_lit_or_lit_abs {FS} {m o N : Int} {x T1 T2 T3 t}
    (hN : ∀ n : Int, t = .bitVector n → N = n) (hmo : zland m o = m) :
    Refines FS (.mk (.binop .bitAnd (.mk (.bitVec m) T1)
      (.mk (.binop .bitOr x (.mk (.bitVec o) T3)) T2)) t) (mk_masked N m) := by
  refine BitOp.and.lit_l_abs_of (fun n _ _ ht => hN n ht) (fun ρ n y hn m0 h1 h2 eb => ?_)
  obtain ⟨k, x', ex, hv, o0, o1⟩ := BitOp.or.eval_lit_r eb
  obtain ⟨rfl, rfl⟩ := Val.bv_inj hv
  have h := congrArg (BitVec.ofInt n.toNat) hmo
  rw [ofInt_zland m0 o0] at h
  ext i hi
  have h' := congrArg (fun v => v.getLsbD i) h
  simp at h' ⊢
  grind

theorem and_lit_or_lit_zero {FS} {m o N : Int} {x T1 T2 T3 t}
    (hN : ∀ n : Int, t = .bitVector n → N = n) (hmo : zland m o = 0) :
    Refines FS (.mk (.binop .bitAnd (.mk (.bitVec m) T1)
      (.mk (.binop .bitOr x (.mk (.bitVec o) T3)) T2)) t)
      (.mk (.binop .bitAnd x (mk_masked N m)) (.bitVector (size x))) := by
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := (BitOp.and (FS := FS)).WT.1 w
    obtain ⟨n', hn', hx, h3, h4, wx, w3⟩ := (BitOp.or (FS := FS)).WT.1 w2
    simp only [Term.ty_mk] at h2 h4; subst h2; simp only [Ty.bitVector.injEq] at h4; subst h4
    obtain rfl := hN _ ht
    exact ⟨(BitOp.and (FS := FS)).WT.2 ⟨N, hn, hx, rfl, by simp [size, ty, hx, size_of_ty], wx,
      mk_masked_WT hn⟩, by simp [size, ty, hx, size_of_ty, ht]⟩
  · obtain ⟨n, hn, h1, h2, ht, w1, w2⟩ := (BitOp.and (FS := FS)).WT.1 w
    obtain ⟨n', hn', hx, h3, h4, wx, w3⟩ := (BitOp.or (FS := FS)).WT.1 w2
    simp only [Term.ty_mk] at h2 h4; subst h2; simp only [Ty.bitVector.injEq] at h4; subst h4
    obtain rfl := hN _ ht
    obtain ⟨k, y, ey, rfl, m0, m1⟩ := BitOp.and.eval_lit_l e
    obtain ⟨k', x', ex, hv, o0, o1⟩ := BitOp.or.eval_lit_r ey
    obtain ⟨rfl, rfl⟩ := Val.bv_inj hv
    obtain ⟨z, hz⟩ := eval_bv ex hx
    obtain ⟨hk, -⟩ := Val.bv_inj hz
    subst hk
    rw [BitOp.and.eval_of w' ex (eval_mk_masked hn)]
    have h := congrArg (BitVec.ofInt N.toNat) hmo
    rw [ofInt_zland m0 o0] at h
    congr 2
    ext i hi
    have h' := congrArg (fun v => v.getLsbD i) h
    simp at h' ⊢
    grind

/-! ## A mask of an or of a literal and a masked value -/

theorem and_mask_or_mask {FS} {m c p : Int} {x T1 T2 T3 T4 T5 T' t}
    (hT' : ∀ k : Int, T1 = .bitVector k → T2 = .bitVector k → T' = .bitVector k) :
    Refines FS (.mk (.binop .bitAnd (.mk (.bitVec m) T1) (.mk (.binop .bitOr (.mk (.bitVec c) T4)
      (.mk (.binop .bitAnd (.mk (.bitVec p) T5) x) T3)) T2)) t)
      (bv_or.spec (bv_and.spec (.mk (.bitVec m) T') (.mk (.bitVec c) T4))
        (bv_and.spec x (bv_and.spec (.mk (.bitVec m) T') (.mk (.bitVec p) T5)))) := by
  have key : ∀ {k : Int}, 0 < k → T1 = .bitVector k → T2 = .bitVector k →
      (Term.mk (.bitVec m) T1).WT → (Term.mk (Kind.bitVec m) T').WT ∧ T' = .bitVector k := by
    intro k hk h1 h2 w1
    obtain rfl := hT' k h1 h2
    subst h1
    obtain ⟨_, m0, m1⟩ := lit_inv w1 k rfl
    exact ⟨lit_WT hk m0 m1, rfl⟩
  refine Refines.intro (fun w => ?_) (fun ρ u w w' e => ?_)
  · obtain ⟨k, hk, h1, h2, ht, w1, w2⟩ := (BitOp.and (FS := FS)).WT.1 w
    obtain ⟨k2, hk2, h4, h3, h5, w4, w3⟩ := (BitOp.or (FS := FS)).WT.1 w2
    obtain ⟨k3, hk3, h5', hx, h6, w5, wx⟩ := (BitOp.and (FS := FS)).WT.1 w3
    simp only [Term.ty_mk] at h1 h2 h3 h4 h5 h5' h6
    subst h1 h2 ht
    simp only [Ty.bitVector.injEq] at h5; subst h5
    subst h4 h3
    simp only [Ty.bitVector.injEq] at h6; subst h6
    subst h5'
    obtain ⟨wm, hm⟩ := key hk rfl rfl w1
    subst hm
    refine ⟨(BitOp.or (FS := FS)).WT.2 ⟨k, hk, by simp [bv_and.spec, size, ty, size_of_ty],
      by simp [bv_and.spec, size, ty, size_of_ty, hx], by simp [bv_and.spec, size, ty, size_of_ty],
      (BitOp.and (FS := FS)).WT.2 ⟨k, hk, rfl, rfl, by simp [size, ty, size_of_ty], wm, w4⟩,
      (BitOp.and (FS := FS)).WT.2 ⟨k, hk, hx, by simp [bv_and.spec, size, ty, size_of_ty],
        by simp [size, ty, size_of_ty, hx],
        wx, (BitOp.and (FS := FS)).WT.2 ⟨k, hk, rfl, rfl, by simp [size, ty, size_of_ty], wm, w5⟩⟩⟩,
      by simp [bv_or.spec, bv_and.spec, ty, size, size_of_ty]⟩
  · obtain ⟨k, hk, h1, h2, ht, w1, w2⟩ := (BitOp.and (FS := FS)).WT.1 w
    simp only [Term.ty_mk] at h1 h2
    obtain ⟨wm, hm⟩ := key hk h1 h2 w1
    obtain ⟨K, a1, y, ea1, ey, rfl⟩ := BitOp.and.eval_eq_some e
    obtain ⟨K', a2, z, ea2, ez, hy⟩ := BitOp.or.eval_eq_some ey
    obtain ⟨rfl, rfl⟩ := Val.bv_inj hy
    obtain ⟨K'', a3, x', ea3, ex, hz⟩ := BitOp.and.eval_eq_some ez
    obtain ⟨rfl, rfl⟩ := Val.bv_inj hz
    obtain ⟨hK, -⟩ := lit_val ea1 h1
    obtain ⟨rfl, -, -⟩ := lit_val₀ ea1
    have em : eval FS ρ (Term.mk (.bitVec m) T') = some (.bv K (BitVec.ofInt K m)) := by
      rw [eval_lit' wm hm, hK]
    obtain ⟨-, wa, wb⟩ := WT_binop.1 w'
    obtain ⟨-, wa1, wa2⟩ := WT_binop.1 wa
    obtain ⟨-, wb1, wb2⟩ := WT_binop.1 wb
    obtain ⟨-, wb21, wb22⟩ := WT_binop.1 wb2
    rw [bv_or.spec, BitOp.or.eval_of w' (BitOp.and.eval_of wa em ea2)
      (BitOp.and.eval_of wb ex (BitOp.and.eval_of wb2 em ea3))]
    congr 2
    ext i hi
    simp
    grind

end BitwiseL
end Bvr
