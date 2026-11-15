module

import FitzhughFarnsworth
import Lean

/-! Audit transitive axiom dependencies of every declaration in our namespace. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if (`FitzhughFarnsworth).isPrefixOf (privateToUserName name) then
      checked := checked + 1
      for axiomName in ← collectAxioms name do
        unless allowed.contains axiomName do
          throwError "{name} depends on unapproved axiom {axiomName}"
  if checked == 0 then
    throwError "No project declarations found; refusing an empty audit"
  logInfo m!"Axiom audit passed for {checked} project declarations."
