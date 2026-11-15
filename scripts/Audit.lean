/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

import all FitzhughFarnsworth
import all FitzhughFarnsworth.AngleConventions
import all FitzhughFarnsworth.AngleConventions.Comparison
import all FitzhughFarnsworth.Convergence
import all FitzhughFarnsworth.Convergence.Angles
import all FitzhughFarnsworth.Convergence.Enclosures
import all FitzhughFarnsworth.Convergence.Monotonicity
import all FitzhughFarnsworth.Dynamics.Basic
import all FitzhughFarnsworth.Dynamics.Canonical
import all FitzhughFarnsworth.Dynamics.Correctness
import all FitzhughFarnsworth.Dynamics.Global
import all FitzhughFarnsworth.Dynamics.Iteration
import all FitzhughFarnsworth.Dynamics.Reduction
import all FitzhughFarnsworth.Dynamics.Rotation
import all FitzhughFarnsworth.Dynamics.Sequence
import all FitzhughFarnsworth.Dynamics.Uniqueness
import all FitzhughFarnsworth.IteratedMidsets
import all FitzhughFarnsworth.IteratedMidsets.Algebra
import all FitzhughFarnsworth.LineConfigurations
import all FitzhughFarnsworth.LineConfigurations.Boundary
import all FitzhughFarnsworth.LineConfigurations.Euclidean
import all FitzhughFarnsworth.LineConfigurations.Reduction
import all FitzhughFarnsworth.LineConfigurations.Translated
import all FitzhughFarnsworth.LineDistances
import all FitzhughFarnsworth.Mathlib.Topology.MetricSpace.InfDist
import all FitzhughFarnsworth.Mathlib.Topology.MetricSpace.Midset
import all FitzhughFarnsworth.MetricGeometry
import all FitzhughFarnsworth.Midsets
import Lean

/-!
# Audit project proofs

Check transitive axiom dependencies of every declaration defined by a project
module, including the general-purpose lemmas in `Metric` and `IsometryEquiv`.
Module ownership, rather than namespace alone, keeps extracted lemmas in scope.
Explicit `import all` is required for each project module: it is not transitive,
and ordinary imports can hide unused private declarations from the environment.
-/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  for imported in env.header.modules do
    if (`FitzhughFarnsworth).isPrefixOf imported.module && !imported.importAll then
      throwError "Project module {imported.module} is missing an explicit `import all`"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut extracted : Nat := 0
  for (name, _) in env.constants.toList do
    let ownedModule := match env.getModuleIdxFor? name with
      | some idx => (`FitzhughFarnsworth).isPrefixOf env.header.moduleNames[idx]!
      | none => false
    let ownedNamespace := (`FitzhughFarnsworth).isPrefixOf (privateToUserName name)
    if ownedModule || ownedNamespace then
      checked := checked + 1
      if !ownedNamespace then
        extracted := extracted + 1
      for axiomName in ← collectAxioms name do
        unless allowed.contains axiomName do
          throwError "{name} depends on unapproved axiom {axiomName}"
  if checked == 0 then
    throwError "No project declarations found; refusing an empty audit"
  logInfo m!"Axiom audit passed for {checked} project declarations \
    ({extracted} outside the project namespace)."
