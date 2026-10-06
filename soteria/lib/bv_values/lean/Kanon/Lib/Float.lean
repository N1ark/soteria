import Kanon.Lib.Lit
import Kanon.Model.Bool.of_bool

/-! Pointers and if-then-else, by evaluation. -/

namespace Kanon.Lib

open CoreMod

open Classical

theorem WT_ptr {l o t} : (Term.mk (.Op2 .Ptr l o) t).WT ↔ ∃ n : Int, 0 < n ∧ t = .TPointer n ∧
    l.ty = .TLoc n ∧ o.ty = .TBitVector n ∧ l.WT ∧ o.WT := by
  simp only [Term.WT, Op2.WT]
  constructor
  · rintro ⟨⟨n, hn, h1, h2, h3⟩, wl, wo⟩
    exact ⟨n, hn, h3, h1, h2, wl, wo⟩
  · rintro ⟨n, hn, h3, h1, h2, wl, wo⟩
    exact ⟨⟨n, hn, h1, h2, h3⟩, wl, wo⟩

theorem eval_ptr_eq_some {FS ρ l o t v} (h : (Term.mk (.Op2 .Ptr l o) t).WT) :
    eval FS ρ (.mk (.Op2 .Ptr l o) t) = some v ↔
      ∃ n x y, eval FS ρ l = some (.bv n x) ∧ eval FS ρ o = some (.bv n y) ∧ v = .ptr n x y := by
  obtain ⟨_, _, _, _, _, wl, wo⟩ := WT_ptr.1 h
  rw [eval_eq_ev h]
  simp only [ev]
  rw [← eval_eq_ev wl, ← eval_eq_ev wo]
  simp only [evOp2, evPtr]
  split
  · rename_i n x m y hl ho
    rw [hl, ho]
    constructor
    · intro e; split at e <;> simp at e
      subst_vars; exact ⟨_, _, _, rfl, rfl, rfl⟩
    · rintro ⟨n', x', y', h1, h2, rfl⟩
      simp at h1 h2; obtain ⟨rfl, h1⟩ := h1; obtain ⟨rfl, h2⟩ := h2
      subst h1 h2; simp
  · rename_i hne
    simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro n x y h1 h2 _
    exact hne n x n y h1 h2

theorem WT_ite {g a b t} : (Term.mk (.Op3 .Ite g a b) t).WT ↔
    g.ty = .TBool ∧ b.ty = a.ty ∧ t = a.ty ∧ g.WT ∧ a.WT ∧ b.WT := by
  simp [Term.WT, Op3.WT, and_assoc]

end Kanon.Lib
