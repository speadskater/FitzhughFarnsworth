/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Gluing functions with the same value and derivative

The choice between the two functions may be arbitrary: agreement to first
order at the point is sufficient for differentiability of the glued function.
-/

@[expose] public section

/-- Choosing between two functions with the same value and derivative at a point
preserves their derivative, without any regularity assumption on the selector. -/
theorem HasDerivAt.ite_of_eq {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f g : 𝕜 → F} {x : 𝕜} {d : F}
    (hf : HasDerivAt f d x) (hg : HasDerivAt g d x) (he : f x = g x)
    (P : 𝕜 → Prop) [DecidablePred P] :
    HasDerivAt (fun t => if P t then f t else g t) d x := by
  apply HasDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  filter_upwards [hf.isLittleO.bound hc, hg.isLittleO.bound hc] with t ht₁ ht₂
  by_cases hx : P x <;> by_cases ht : P t <;> simp only [hx, ht, ↓reduceIte, he] at *
  all_goals assumption
