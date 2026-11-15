/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

import all Mathlib.Topology.MetricSpace.HausdorffDistance
import all Mathlib.Topology.MetricSpace.Midset
import Batteries.Tactic.Lint

/-!
# Check the proposed mathlib additions

Run in a mathlib checkout with both candidate patches applied. Only new
declarations are linted and axiom-audited; imported mathlib is the baseline.
-/

open Lean Elab Command Batteries.Tactic.Lint in
run_cmd do
  let env := (← getEnv).setExporting false
  let decls := env.constants.toList.toArray.filterMap fun (n, _) =>
    if n == `Metric.infDist_union ||
        (env.getModuleIdxFor? n).any (fun i =>
          env.header.moduleNames[i]! == `Mathlib.Topology.MetricSpace.Midset) then
      some n
    else none
  if decls.isEmpty then throwError "No candidate declarations found"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in decls do
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  let linters ← liftCoreM <| getChecks (slow := true) (runOnly := none) (runAlways := none)
  let results ← liftCoreM <| lintCore decls linters
  for (linter, failures) in results do
    for (name, message) in failures.toArray do
      logError m!"{linter.name}: {name}: {message}"
  logInfo m!"Axiom-audited {decls.size} candidate declarations and ran \
    {linters.size} environment linters."
