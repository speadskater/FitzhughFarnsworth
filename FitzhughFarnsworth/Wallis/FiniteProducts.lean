/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Mathlib.Analysis.SpecialFunctions.Gamma.FiniteProducts

/-!
# Balanced Gamma products with any finite number of factors

Equations (8)–(9) of Fitzhugh–Farnsworth (2013), using the equivalent zero-based
indexing. All shifts are positive, so the paper's one-based shifts must exceed
`-1`. The numerator and denominator have the same finite index set, and the
sums of their shifts must agree.
-/

@[expose] public section

namespace FitzhughFarnsworth.Wallis

open Filter Topology

/-- Equations (8)–(9), for an arbitrary finite number of positive linear factors. -/
theorem tendsto_balanced_finset_prod {ι : Type*} (s : Finset ι) (x y : ι → ℝ)
    (hx : ∀ i ∈ s, 0 < x i) (hy : ∀ i ∈ s, 0 < y i)
    (hbalance : ∑ i ∈ s, x i = ∑ i ∈ s, y i) :
    Tendsto (fun n : ℕ =>
      ∏ k ∈ Finset.range n, (∏ i ∈ s, (x i + k)) / (∏ i ∈ s, (y i + k)))
      atTop (𝓝 ((∏ i ∈ s, Real.Gamma (y i)) / (∏ i ∈ s, Real.Gamma (x i)))) :=
  Real.tendsto_prod_linear_factors s x y hx hy hbalance

end FitzhughFarnsworth.Wallis
