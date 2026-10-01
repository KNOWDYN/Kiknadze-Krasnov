import KiknadzeKrasnov
import Lean.Util.CollectAxioms

open Lean Elab Command in
-- Check the transitive proof dependencies of every declaration in this project.
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (imp, data) in env.header.modules.zip env.header.moduleData do
    if (`KiknadzeKrasnov).isPrefixOf imp.module then
      for name in data.constNames do
        for axiomName in (← collectAxioms name) do
          unless allowed.contains axiomName do
            throwError "{name} depends on forbidden axiom {axiomName}"
        checked := checked + 1
  if checked == 0 then
    throwError "No project declarations were loaded for the trust audit"
  logInfo m!"Trust audit passed for {checked} project declarations."
