import Tiny.Lib.Int

/-! The integer operations, proved per alternative. -/

namespace Tiny

open Classical Kanon Lib

/-- A multiple of `n` has a zero remainder by `n`, both for `rem` and `mod`. -/
macro "kanon_multiple" : tactic => `(tactic| (
  intro O hO v1 n t h
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · simp_all [kanon_spec, zero, int_z, WT_binop, Binop.WT]
  · simp only [kanon_spec, ev, evBinop] at e
    obtain ⟨x, y, hx, hy, hn, he⟩ := divOp_eq_some.1 e
    simp only [Option.some.injEq, Val.int.injEq] at hy; subst hy he
    have := is_mod_sound hn h hx
    simp [zero, int_z, ev, zrem, Int.emod_eq_zero_of_dvd this]))

@[kanon_arm] theorem rem.r_multiple.main.proof : rem.r_multiple.main.Stmt := by kanon_multiple

@[kanon_arm] theorem mod_.r_multiple.main.proof : mod_.r_multiple.main.Stmt := by kanon_multiple

set_option hygiene false in
@[kanon_arm] theorem rem.r_mul.main.proof : rem.r_mul.main.Stmt := by
  kanon_rule_lift
  refine Refines.intro ?_ ?_
  · kanon_wt
  · kanon_sem_core
    all_goals simp_all [zrem_mul_pos]

set_option hygiene false in
@[kanon_arm] theorem mod_.r_mod_mod.main.proof : mod_.r_mod_mod.main.Stmt := by
  kanon_rule_lift
  refine Refines.intro ?_ ?_
  · kanon_wt
  · kanon_sem_core
    all_goals simp_all [Int.emod_emod_of_dvd]

set_option hygiene false in
@[kanon_arm] theorem mod_.r_add_mod.main.proof : mod_.r_add_mod.main.Stmt := by
  kanon_rule_lift
  refine Refines.intro ?_ ?_
  · kanon_wt
  · kanon_sem_core
    all_goals simp_all [add_emod_emod_of_dvd]

end Tiny
