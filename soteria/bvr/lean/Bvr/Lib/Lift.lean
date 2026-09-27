import Bvr.Lib.BV

/-!
# Lifting the calls to rule functions to their specs

The body of a rule calls rule functions through `O`, which only refine their
specs. `bvr_lift` proves `Refines FS S body`, where `S` is `body` with every
call `O.f args` replaced by `f.spec args` (it is found by unification), so
that the rest of a proof is about raw terms only.
-/

namespace Bvr.Lib

open Classical

variable {FS : FloatSem} {O : Ops}

theorem ty_refines {a a' : Term} (ha : Refines FS a a') (w : a.WT) : a'.ty = a.ty := by
  simpa using (ha.syn w).2

theorem lift_bv_add (hO : O.Sound FS) {c a a' b b'} (ha : Refines FS a a')
    (hb : Refines FS b b') : Refines FS (bv_add.spec c a b) (O.bv_add c a' b') :=
  Refines.trans
    (Refines.binop ha hb (fun w => by simp [ty_refines ha (WT_binop.1 w).2.1]))
    (hO.bv_add c a' b')

theorem lift_bv_sub (hO : O.Sound FS) {c a a' b b'} (ha : Refines FS a a')
    (hb : Refines FS b b') : Refines FS (bv_sub.spec c a b) (O.bv_sub c a' b') :=
  Refines.trans
    (Refines.binop ha hb (fun w => by simp [ty_refines ha (WT_binop.1 w).2.1]))
    (hO.bv_sub c a' b')

theorem lift_bv_mul (hO : O.Sound FS) {c a a' b b'} (ha : Refines FS a a')
    (hb : Refines FS b b') : Refines FS (bv_mul.spec c a b) (O.bv_mul c a' b') :=
  Refines.trans
    (Refines.binop ha hb (fun w => by simp [ty_refines ha (WT_binop.1 w).2.1]))
    (hO.bv_mul c a' b')

theorem lift_bv_div (hO : O.Sound FS) {s a a' b b'} (ha : Refines FS a a')
    (hb : Refines FS b b') : Refines FS (bv_div.spec s a b) (O.bv_div s a' b') :=
  Refines.trans
    (Refines.binop ha hb (fun w => by simp [ty_refines ha (WT_binop.1 w).2.1]))
    (hO.bv_div s a' b')

theorem lift_bv_neg (hO : O.Sound FS) {c a a'} (ha : Refines FS a a') :
    Refines FS (bv_neg.spec c a) (O.bv_neg c a') :=
  Refines.trans
    (Refines.unop ha (fun w => by simp [ty_refines ha (WT_unop.1 w).2]))
    (hO.bv_neg c a')

theorem lift_bv_extend (hO : O.Sound FS) {s k a a'} (ha : Refines FS a a') :
    Refines FS (bv_extend.spec s k a) (O.bv_extend s k a') :=
  Refines.trans
    (Refines.unop ha (fun w => by
      simp [ty_refines ha (WT_unop.1 w).2]))
    (hO.bv_extend s k a')

theorem lift_b_ite (hO : O.Sound FS) {g g' a a' b b'} (hg : Refines FS g g')
    (ha : Refines FS a a') (hb : Refines FS b b') :
    Refines FS (b_ite.spec g a b) (O.b_ite g' a' b') :=
  Refines.trans
    (Refines.ite hg ha hb (fun w => by simp [ty_refines ha (WT_triop.1 w).2.2.1]))
    (hO.b_ite g' a' b')

/-- `Refines.trans`, with the lifting first so that it determines the middle
term. -/
theorem Refines.of_lift {s m r : Term} (hl : Refines FS m r) (hm : Refines FS s m) :
    Refines FS s r :=
  Refines.trans hm hl

/-- Proves `Refines FS ?S body`, finding `?S` (see above). -/
syntax "bvr_lift" : tactic
macro_rules
  | `(tactic| bvr_lift) => `(tactic| first
      | (apply lift_bv_add ‹Ops.Sound _ _› <;> bvr_lift)
      | (apply lift_bv_sub ‹Ops.Sound _ _› <;> bvr_lift)
      | (apply lift_bv_mul ‹Ops.Sound _ _› <;> bvr_lift)
      | (apply lift_bv_div ‹Ops.Sound _ _› <;> bvr_lift)
      | (apply lift_bv_neg ‹Ops.Sound _ _› <;> bvr_lift)
      | (apply lift_bv_extend ‹Ops.Sound _ _› <;> bvr_lift)
      | (apply lift_b_ite ‹Ops.Sound _ _› <;> bvr_lift)
      | exact Refines.refl)

/-- Replaces the goal `Refines FS s body` by `Refines FS s S`, with the calls of
`body` lifted to their specs in `S`. -/
macro "bvr_lift_body" : tactic => `(tactic| (apply Refines.of_lift; case hl => bvr_lift))

end Bvr.Lib
