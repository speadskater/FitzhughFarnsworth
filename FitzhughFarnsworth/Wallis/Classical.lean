/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Wallis.Construction
public import FitzhughFarnsworth.Wallis.PCircle
public import Mathlib.Analysis.Real.Pi.Wallis

/-!
# The unit-square construction and the classical Wallis limit

For `a = b = A = B = 1`, the actual rectangle dimensions give mathlib's finite
Wallis products. Equations (1)–(2) of Fitzhugh–Farnsworth (2013) follow from this
identity and mathlib's Wallis theorem. The general Gamma limit in equation (23)
is proved in `FitzhughFarnsworth.Wallis.Convergence`.
-/

@[expose] public section

namespace FitzhughFarnsworth.Wallis

open Filter Topology

/-- Start from the unit square and attach rectangles of area one. -/
def unitSquare : Parameters where
  a := 1
  b := 1
  A := 1
  B := 1
  a_pos := zero_lt_one
  b_pos := zero_lt_one
  A_pos := zero_lt_one
  B_pos := zero_lt_one

theorem unitSquare_ratioFactor (n : ℕ) :
    unitSquare.ratioFactor n =
      ((2 * n + 2) / (2 * n + 1)) * ((2 * n + 2) / (2 * n + 3)) := by
  unfold Parameters.ratioFactor unitSquare
  push_cast
  congr 2 <;> ring

/-- Every finite aspect ratio is exactly the corresponding Wallis partial product. -/
theorem unitSquare_ratio_eq_wallis (n : ℕ) : unitSquare.ratio n = Real.Wallis.W n := by
  rw [Parameters.ratio_eq_prod]
  simp only [unitSquare, div_self one_ne_zero, one_mul]
  exact Finset.prod_congr rfl fun k _ => unitSquare_ratioFactor k

/-- Equations (1)–(2): the aspect ratios of the constructed rectangles tend to `π / 2`. -/
theorem unitSquare_ratio_tendsto : Tendsto unitSquare.ratio atTop (𝓝 (Real.pi / 2)) := by
  rw [show unitSquare.ratio = Real.Wallis.W from funext unitSquare_ratio_eq_wallis]
  exact Real.Wallis.tendsto_W_nhds_pi_div_two

/-- Mathlib's Wallis bounds apply to the actual construction at every finite stage. -/
theorem unitSquare_ratio_bounds (n : ℕ) :
    ((2 : ℝ) * n + 1) / (2 * n + 2) * (Real.pi / 2) ≤ unitSquare.ratio n ∧
      unitSquare.ratio n ≤ Real.pi / 2 := by
  rw [unitSquare_ratio_eq_wallis]
  exact ⟨Real.Wallis.le_W n, Real.Wallis.W_le n⟩

/-- The classical construction is the `p = 2` instance of the p-circle products. -/
theorem unitSquare_ratio_eq_pCircleProduct (n : ℕ) :
    unitSquare.ratio n = pCircleProduct 2 n := by
  rw [unitSquare_ratio_eq_wallis]
  unfold Real.Wallis.W pCircleProduct
  apply Finset.prod_congr rfl
  intro k _
  congr 2
  ring

theorem unitSquare_ratio_tendsto_area :
    Tendsto unitSquare.ratio atTop (𝓝 (upperHalfArea 2)) :=
  (pCircleProduct_tendsto_area (by norm_num : (1 : ℝ) ≤ 2)).congr
    fun n => (unitSquare_ratio_eq_pCircleProduct n).symm

theorem upperHalfArea_two : upperHalfArea 2 = Real.pi / 2 :=
  tendsto_nhds_unique unitSquare_ratio_tendsto_area unitSquare_ratio_tendsto

theorem diskArea_two : diskArea 2 = Real.pi := by
  rw [diskArea_eq_gamma (by norm_num : (1 : ℝ) ≤ 2),
    ← upperHalfArea_eq_gamma (by norm_num : (1 : ℝ) ≤ 2), upperHalfArea_two]
  ring

end FitzhughFarnsworth.Wallis
