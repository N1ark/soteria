import Lean

/-- The specs of the rule functions (`f.spec`), unfolded by the rule tactics. -/
register_simp_attr bvr_spec

open Lean

namespace Bvr

/-- The tactics given to rule functions by `bvr_tactic`, by their spec. -/
initialize bvrTacticExt : SimplePersistentEnvExtension (Name × String) (NameMap String) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, t) => m.insert n t
    addImportedFn := mkStateFromImportedEntries (fun m (n, t) => m.insert n t) {}
  }

/-- The hand-written proofs of arms given by `bvr_arm`, by arm. -/
initialize bvrArmExt : SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, p) => m.insert n p
    addImportedFn := mkStateFromImportedEntries (fun m (n, p) => m.insert n p) {}
  }

end Bvr

/-- `attribute [bvr_tactic "tac"] f.spec`: the arms of the rule function `f` are
proved by the tactic `tac` (and otherwise by `bvr_auto`), unless they have a
hand-written proof. The tactic is a string, parsed where it is used, as the
arguments of attributes are macro-expanded. -/
syntax (name := bvr_tactic) "bvr_tactic " str : attr

/-- `@[bvr_arm] theorem ... : f.r_rule.arm.Stmt`: a hand-written proof of an arm,
which its generated proof then uses. -/
syntax (name := bvr_arm) "bvr_arm" : attr

initialize registerBuiltinAttribute {
  name := `bvr_tactic
  descr := "the tactic that proves the arms of a rule function, given on its spec"
  add := fun decl stx _ => do
    unless decl.getString! == "spec" do
      throwError "bvr_tactic: {decl} is not the spec of a rule function"
    if (Bvr.bvrTacticExt.getState (← getEnv)).contains decl then
      throwError "bvr_tactic: {decl} already has a tactic"
    let some tac := stx[1].isStrLit? | throwError "bvr_tactic: expected a string"
    if let .error e := Parser.runParserCategory (← getEnv) `tactic tac then
      throwError "bvr_tactic: {e}"
    modifyEnv (Bvr.bvrTacticExt.addEntry · (decl, tac))
}

initialize registerBuiltinAttribute {
  name := `bvr_arm
  descr := "a hand-written proof of the statement `X.Stmt` of an arm `X`"
  add := fun decl _ _ => do
    let some info := (← getEnv).find? decl | throwError "bvr_arm: unknown {decl}"
    let .const stmt [] := info.type
      | throwError "bvr_arm: {decl} does not prove the statement of an arm"
    let arm := stmt.getPrefix
    -- `Bvr.f.r_rule.arm.Stmt`
    unless stmt.getString! == "Stmt" && arm.components.length == 4 do
      throwError "bvr_arm: {decl} does not prove the statement of an arm"
    if let some p := (Bvr.bvrArmExt.getState (← getEnv)).find? arm then
      throwError "bvr_arm: {arm} is already proved by {p}"
    modifyEnv (Bvr.bvrArmExt.addEntry · (arm, decl))
}
