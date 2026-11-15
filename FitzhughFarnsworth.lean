/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.MetricGeometry
public import FitzhughFarnsworth.Midsets
public import FitzhughFarnsworth.LineDistances
public import FitzhughFarnsworth.LineConfigurations
public import FitzhughFarnsworth.IteratedMidsets
public import FitzhughFarnsworth.Convergence
public import FitzhughFarnsworth.IteratedMidsets.Algebra
public import FitzhughFarnsworth.LineConfigurations.Reduction
public import FitzhughFarnsworth.LineConfigurations.Boundary
public import FitzhughFarnsworth.LineConfigurations.Euclidean
public import FitzhughFarnsworth.LineConfigurations.Translated
public import FitzhughFarnsworth.Convergence.Angles
public import FitzhughFarnsworth.Convergence.Enclosures
public import FitzhughFarnsworth.AngleConventions
public import FitzhughFarnsworth.AngleConventions.Comparison
public import FitzhughFarnsworth.Dynamics.Correctness
public import FitzhughFarnsworth.Wallis.Classical
public import FitzhughFarnsworth.Wallis.Convergence
public import FitzhughFarnsworth.Wallis.Asymptotics
public import FitzhughFarnsworth.Wallis.BoxConvergence
public import FitzhughFarnsworth.Wallis.BoxSpecializations
public import FitzhughFarnsworth.Wallis.Hypercube
public import FitzhughFarnsworth.Wallis.FiniteProducts

/-!
# Fitzhugh–Farnsworth formalizations

The verified library for the Fitzhugh–Farnsworth papers: the complete midset
iteration at the stated intersecting-line scope, and the Wallis constructions
in two, three, and N dimensions, with Gamma limits and measured p-circle areas
for `p ≥ 1`.
See `docs/ROADMAP.md` for the status of each of the three papers.
-/
