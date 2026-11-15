/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The normality paper's slope map and boundary directions

Fitzhugh–Farnsworth (2013), equations (3)–(6). This module defines and analyzes
the slope formulas as an algebraic map. Their derivation from geometric
tangency or distance minimization is a separate roadmap obligation; no such
characterization is assumed here. Horizontal and vertical directions are
handled explicitly by `Direction.next`.
-/

@[expose] public section

namespace FitzhughFarnsworth.Normality

/-- The normality paper excludes `p = 1` and requires a finite exponent `p > 1`. -/
structure Parameters where
  /-- Exponent of the unit p-circle. -/
  p : ℝ
  one_lt_p : 1 < p

namespace Parameters

/-- The positive exponent `1/(p-1)` in the normal-slope recurrence. -/
noncomputable def exponent (g : Parameters) : ℝ := 1 / (g.p - 1)

theorem exponent_pos (g : Parameters) : 0 < g.exponent :=
  one_div_pos.mpr (sub_pos.mpr g.one_lt_p)

/-- Equations (3)–(4), for finite nonzero slopes. The value at zero is auxiliary;
the horizontal line is sent to the vertical line by `Direction.next`. -/
noncomputable def normalSlope (g : Parameters) (m : ℝ) : ℝ :=
  if 0 < m then -(m ^ (-g.exponent)) else (-m) ^ (-g.exponent)

theorem normalSlope_of_pos (g : Parameters) {m : ℝ} (hm : 0 < m) :
    g.normalSlope m = -(m ^ (-g.exponent)) := by
  simp only [normalSlope, hm, ↓reduceIte]

theorem normalSlope_of_neg (g : Parameters) {m : ℝ} (hm : m < 0) :
    g.normalSlope m = (-m) ^ (-g.exponent) := by
  simp only [normalSlope, not_lt.mpr hm.le, ↓reduceIte]

/-- Equation (3) in its printed reciprocal-power form. -/
theorem normalSlope_positive_formula (g : Parameters) {m : ℝ} (hm : 0 < m) :
    g.normalSlope m = -((1 / m) ^ g.exponent) := by
  rw [normalSlope_of_pos g hm, Real.rpow_neg_eq_inv_rpow, one_div]

/-- Equation (4) in its printed form, with a positive base. -/
theorem normalSlope_negative_formula (g : Parameters) {m : ℝ} (hm : m < 0) :
    g.normalSlope m = (-1 / m) ^ g.exponent := by
  rw [normalSlope_of_neg g hm, Real.rpow_neg_eq_inv_rpow]
  congr 1
  simp [div_eq_mul_inv]

theorem normalSlope_neg_of_pos (g : Parameters) {m : ℝ} (hm : 0 < m) :
    g.normalSlope m < 0 := by
  rw [normalSlope_of_pos g hm]
  exact neg_neg_of_pos (Real.rpow_pos_of_pos hm _)

theorem normalSlope_pos_of_neg (g : Parameters) {m : ℝ} (hm : m < 0) :
    0 < g.normalSlope m := by
  rw [normalSlope_of_neg g hm]
  exact Real.rpow_pos_of_pos (neg_pos.mpr hm) _

theorem normalSlope_ne_zero (g : Parameters) {m : ℝ} (hm : m ≠ 0) :
    g.normalSlope m ≠ 0 := by
  rcases lt_or_gt_of_ne hm with h | h
  · exact (g.normalSlope_pos_of_neg h).ne'
  · exact (g.normalSlope_neg_of_pos h).ne

/-- Equation (5), for a positive current slope. -/
theorem normalSlope_twoStep_of_pos (g : Parameters) {m : ℝ} (hm : 0 < m) :
    g.normalSlope (g.normalSlope m) = m ^ (g.exponent ^ 2) := by
  rw [g.normalSlope_of_neg (g.normalSlope_neg_of_pos hm), g.normalSlope_of_pos hm,
    neg_neg, ← Real.rpow_mul hm.le]
  congr 1
  ring

/-- Equation (6), for a negative current slope. -/
theorem normalSlope_twoStep_of_neg (g : Parameters) {m : ℝ} (hm : m < 0) :
    g.normalSlope (g.normalSlope m) = -((-m) ^ (g.exponent ^ 2)) := by
  rw [g.normalSlope_of_pos (g.normalSlope_pos_of_neg hm), g.normalSlope_of_neg hm,
    ← Real.rpow_mul (neg_nonneg.mpr hm.le)]
  congr 2
  ring

theorem normalSlope_neg (g : Parameters) {m : ℝ} (hm : m ≠ 0) :
    g.normalSlope (-m) = -(g.normalSlope m) := by
  rcases lt_or_gt_of_ne hm with h | h
  · rw [g.normalSlope_of_pos (neg_pos.mpr h), g.normalSlope_of_neg h]
  · rw [g.normalSlope_of_neg (neg_neg_of_pos h), g.normalSlope_of_pos h, neg_neg, neg_neg]

theorem normalSlope_reciprocal (g : Parameters) {m : ℝ} (hm : m ≠ 0) :
    g.normalSlope (1 / m) = 1 / g.normalSlope m := by
  rcases lt_or_gt_of_ne hm with h | h
  · rw [g.normalSlope_of_neg (div_neg_of_pos_of_neg zero_lt_one h), g.normalSlope_of_neg h]
    rw [show -(1 / m) = (-m)⁻¹ by simp [one_div], Real.inv_rpow (neg_nonneg.mpr h.le)]
    rw [one_div]
  · rw [g.normalSlope_of_pos (one_div_pos.mpr h), g.normalSlope_of_pos h, one_div,
      Real.inv_rpow h.le]
    simp

end Parameters

/-- Finite slopes and the vertical direction; zero slope denotes the horizontal direction. -/
inductive Direction where
  | finite (slope : ℝ)
  | vertical

namespace Direction

/-- The slope recurrence with explicit horizontal/vertical boundary cases.
Its interpretation as geometric normality remains to be proved. -/
noncomputable def next (g : Parameters) : Direction → Direction
  | vertical => finite 0
  | finite m => if m = 0 then vertical else finite (g.normalSlope m)

@[simp] theorem next_vertical (g : Parameters) : next g vertical = finite 0 := rfl

@[simp] theorem next_horizontal (g : Parameters) : next g (finite 0) = vertical := by
  simp [next]

theorem next_finite (g : Parameters) {m : ℝ} (hm : m ≠ 0) :
    next g (finite m) = finite (g.normalSlope m) := by
  simp only [next, hm, ↓reduceIte]

@[simp] theorem next_diagonal (g : Parameters) : next g (finite 1) = finite (-1) := by
  norm_num [next, Parameters.normalSlope]

@[simp] theorem next_antidiagonal (g : Parameters) : next g (finite (-1)) = finite 1 := by
  norm_num [next, Parameters.normalSlope]

theorem axes_cycle (g : Parameters) :
    next g (next g vertical) = vertical ∧ next g (next g (finite 0)) = finite 0 := by simp

theorem diagonals_cycle (g : Parameters) :
    next g (next g (finite 1)) = finite 1 ∧ next g (next g (finite (-1))) = finite (-1) := by simp

end Direction

/-- The Euclidean parameter value. -/
def euclidean : Parameters := ⟨2, by norm_num⟩

@[simp] theorem euclidean_exponent : euclidean.exponent = 1 := by
  norm_num [Parameters.exponent, euclidean]

/-- At `p = 2` the defined direction map is an involution, including the two axes. -/
theorem euclidean_next_involutive : Function.Involutive (Direction.next euclidean) := by
  intro d
  cases d with
  | vertical => simp
  | finite m =>
    by_cases hm : m = 0
    · subst m
      simp
    · rw [Direction.next_finite euclidean hm,
        Direction.next_finite euclidean (euclidean.normalSlope_ne_zero hm)]
      congr 1
      rcases lt_or_gt_of_ne hm with h | h
      · simp [euclidean.normalSlope_twoStep_of_neg h]
      · simp [euclidean.normalSlope_twoStep_of_pos h]

end FitzhughFarnsworth.Normality
