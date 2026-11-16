/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Minimizers of differentiable convex real functions

At an interior point of a convex domain, a differentiable convex function has
a global minimum exactly when its derivative vanishes.
-/

@[expose] public section

/-- At an interior point of a convex domain, a specified derivative vanishes
exactly when the function attains its minimum over the whole domain. -/
theorem ConvexOn.isMinOn_iff_of_hasDerivAt {s : Set ℝ} {f : ℝ → ℝ} {x d : ℝ}
    (hf : ConvexOn ℝ s f) (hx : x ∈ interior s) (hd : HasDerivAt f d x) :
    IsMinOn f s x ↔ d = 0 := by
  constructor
  · intro h
    exact (h.isLocalMin (mem_interior_iff_mem_nhds.mp hx)).hasDerivAt_eq_zero hd
  · intro h
    subst d
    exact hf.isMinOn_of_rightDeriv_eq_zero hx
      (hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x))

/-- The `deriv` version requires differentiability at the point; otherwise Lean's
default value of `deriv` would not imply minimality. -/
theorem ConvexOn.isMinOn_iff_deriv_eq_zero {s : Set ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hf : ConvexOn ℝ s f) (hx : x ∈ interior s) (hd : DifferentiableAt ℝ f x) :
    IsMinOn f s x ↔ deriv f x = 0 :=
  hf.isMinOn_iff_of_hasDerivAt hx hd.hasDerivAt
