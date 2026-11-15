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

/-!
# Fitzhugh–Farnsworth midset iteration

The complete formalization, including the generic metric API, taxicab geometry,
canonical slope iteration, and correctness for arbitrary intersecting affine lines.
-/
