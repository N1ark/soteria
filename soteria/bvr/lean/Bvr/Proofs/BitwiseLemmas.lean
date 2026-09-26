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

theorem eval_bv_zero' {FS ρ} {n : Int} (w : (bv_zero n).WT) :
    eval FS ρ (bv_zero n) = some (.bv n.toNat 0) := eval_bv_zero (bv_zero_pos w)

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

theorem ofInt_eq_zero_iff' {k : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ k) :
    BitVec.ofInt k z = 0#k ↔ z = 0 := ofInt_eq_zero_iff h0 h1

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

theorem Val.bv_ext_toNat {n m : Nat} {x : BitVec n} {y : BitVec m} (h : n = m)
    (hx : x.toNat = y.toNat) : Val.bv n x = Val.bv m y := by
  subst h; congr 1; exact BitVec.eq_of_toNat_eq hx

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

/-- An extraction of a bitwise operation is the operation on the extractions. -/
theorem BitOp.extract {FS op f} (H : BitOp FS op f)
    (hf : ∀ {n} (x y : BitVec n) s l,
      (f x y).extractLsb' s l = f (x.extractLsb' s l) (y.extractLsb' s l))
    {i j v1 v2 T T'} (hT' : T' = .bitVector (j - i + 1)) :
    Refines FS (bv_extract.spec i j (.mk (.binop op v1 v2) T))
      (.mk (.binop op (bv_extract.spec i j v1) (bv_extract.spec i j v2)) T') := by
  subst hT'
  refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨n, hb, h0, h1, h2, -, wb⟩ := WT_extract.1 w
    obtain ⟨n', hn', ha1, ha2, ht, w1, w2⟩ := H.WT.1 wb
    simp only [Term.ty_mk] at hb; subst hb
    simp only [Ty.bitVector.injEq] at ht; subst ht
    refine ⟨H.WT.2 ⟨j - i + 1, by omega, rfl, rfl, rfl, ?_, ?_⟩, rfl⟩ <;>
      exact WT_extract.2 ⟨_, by assumption, h0, h1, h2, rfl, by assumption⟩
  · obtain ⟨n, x, hb, h0, h1, h2, -, eb, rfl⟩ := eval_extract e
    obtain ⟨k, x1, y1, e1, e2, hx⟩ := H.eval_eq_some eb
    obtain ⟨rfl, rfl⟩ := Val.bv_inj hx
    obtain ⟨_, w1, w2⟩ := WT_binop.1 w'
    rw [H.eval_of w' (eval_extract_of w1 e1) (eval_extract_of w2 e2), hf]

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

theorem ite_pos' {c : Prop} [Decidable c] {α} {a b : α} (h : c) : (if c then a else b) = a :=
  by simp [h]
theorem ite_neg' {c : Prop} [Decidable c] {α} {a b : α} (h : ¬c) : (if c then a else b) = b :=
  by simp [h]
@[simp] theorem getLsbD_zero' {w i : Nat} : (0 : BitVec w).getLsbD i = false := by simp

/-- Simplifies the bits of bit-vector expressions, deciding index conditions with omega. -/
macro "bitw_simp" : tactic => `(tactic| simp (disch := omega) only [BitVec.getLsbD_extractLsb',
  BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
  BitVec.getLsbD_setWidth, BitVec.getLsbD_zero, BitVec.getLsbD_and, BitVec.getLsbD_or,
  BitVec.getLsbD_xor, decide_eq_true, decide_eq_false, ite_pos', ite_neg', getLsbD_zero',
  Bool.true_and,
  Bool.and_true, Bool.false_and, Bool.and_false, Bool.not_true, Bool.not_false, Nat.zero_add,
  Nat.add_zero, Int.toNat_zero, BitVec.getLsbD_of_ge, BitVec.getLsbD_signExtend,
  BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last, Bool.not_and, Bool.not_not])

end BitwiseL
end Bvr
