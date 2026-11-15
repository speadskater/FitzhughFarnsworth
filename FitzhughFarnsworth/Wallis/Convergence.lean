/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Wallis.Construction
public import FitzhughFarnsworth.Wallis.GammaProducts

/-!
# Equal-area rectangle limits

Equation (23) of Fitzhugh–Farnsworth (2013), for arbitrary positive starting
width and height and equal positive attached areas. The limit is proved for
the actual dimension recurrence, via its finite products and Euler's Gamma limit.
-/

@[expose] public section

namespace FitzhughFarnsworth.Wallis.Parameters

open Filter Topology

/-- The normalized initial area for the equal-area construction. -/
noncomputable def gammaArgument (c : Parameters) : ℝ := c.a * c.b / (2 * c.A)

theorem gammaArgument_pos (c : Parameters) : 0 < c.gammaArgument :=
  div_pos (mul_pos c.a_pos c.b_pos) (mul_pos two_pos c.A_pos)

theorem ratioFactor_eq_balanced (c : Parameters) (hAB : c.A = c.B) (n : ℕ) :
    c.ratioFactor n =
      ((c.gammaArgument + 1 / 2 + n) * (c.gammaArgument + 1 / 2 + n)) /
        ((c.gammaArgument + n) * (c.gammaArgument + 1 + n)) := by
  have ha := c.a_pos
  have hb := c.b_pos
  have hA := c.A_pos
  unfold ratioFactor gammaArgument
  rw [← hAB]
  push_cast
  field_simp
  ring

/-- The positive constant appearing in equation (23). -/
noncomputable def gammaLimit (c : Parameters) : ℝ :=
  c.a ^ 2 / (2 * c.A) * Real.Gamma c.gammaArgument ^ 2 /
    Real.Gamma (c.gammaArgument + 1 / 2) ^ 2

theorem gammaLimit_pos (c : Parameters) : 0 < c.gammaLimit := by
  unfold gammaLimit
  apply div_pos
  · exact mul_pos (div_pos (sq_pos_of_pos c.a_pos) (mul_pos two_pos c.A_pos))
      (sq_pos_of_pos (Real.Gamma_pos_of_pos c.gammaArgument_pos))
  · exact sq_pos_of_pos (Real.Gamma_pos_of_pos (by linarith [c.gammaArgument_pos]))

/-- Equation (23): the ratio of the actual dimensions converges to the Gamma formula. -/
theorem ratio_tendsto_gammaLimit (c : Parameters) (hAB : c.A = c.B) :
    Tendsto c.ratio atTop (𝓝 c.gammaLimit) := by
  have ht := c.gammaArgument_pos
  have hhalf : 0 < c.gammaArgument + 1 / 2 := by linarith
  have hone : 0 < c.gammaArgument + 1 := by linarith
  have hlim := (tendsto_balanced_prod hhalf hhalf ht hone (by ring)).const_mul (c.a / c.b)
  have heq : c.a / c.b *
      (Real.Gamma c.gammaArgument * Real.Gamma (c.gammaArgument + 1) /
        (Real.Gamma (c.gammaArgument + 1 / 2) * Real.Gamma (c.gammaArgument + 1 / 2))) =
      c.gammaLimit := by
    rw [Real.Gamma_add_one ht.ne']
    unfold gammaLimit gammaArgument
    field_simp [c.b_pos.ne']
  rw [heq] at hlim
  convert hlim using 1
  ext n
  rw [ratio_eq_prod]
  congr 1
  exact Finset.prod_congr rfl fun k _ => c.ratioFactor_eq_balanced hAB k

end FitzhughFarnsworth.Wallis.Parameters
