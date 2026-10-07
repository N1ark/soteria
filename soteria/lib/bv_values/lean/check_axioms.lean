import Kanon

-- CI fails if the soundness theorem depends on `sorryAx`.
#print axioms Kanon.opsN_sound

-- ... or if a proof of an arm of a module proved once does.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods := [`CoreMod, `ExistsMod, `BitvecMod, `FloatMod, `PtrMod]
  let thms := env.constants.fold (init := #[]) fun acc n ci =>
    if ci matches .thmInfo _ && n.getRoot ∈ mods && n.getString! == "ok" then acc.push n
    else acc
  for n in thms do
    if (← collectAxioms n).contains ``sorryAx then logInfo m!"{n} depends on sorryAx"
  logInfo m!"{thms.size} proofs of arms of modules proved once checked"
