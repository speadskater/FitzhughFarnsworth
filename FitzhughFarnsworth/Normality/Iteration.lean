/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Normality.Basic

/-!
# Algebra of iterated normal-slope formulas

Lemmas 3.2–3.3, equations (5)–(11), of Fitzhugh–Farnsworth (2013), for the
defined algebraic recurrence. `Geometry` identifies this recurrence with normal
lines; `Convergence` and `LineConvergence` prove its scalar and geometric limits.
-/

@[expose] public section

namespace FitzhughFarnsworth.Normality

namespace Parameters

/-- Repeated application of the finite-slope formula, for nonzero initial slopes. -/
noncomputable def slopeIterate (g : Parameters) (m : ℝ) : ℕ → ℝ
  | 0 => m
  | n + 1 => g.normalSlope (g.slopeIterate m n)

@[simp] theorem slopeIterate_zero (g : Parameters) (m : ℝ) : g.slopeIterate m 0 = m := rfl

theorem slopeIterate_succ (g : Parameters) (m : ℝ) (n : ℕ) :
    g.slopeIterate m (n + 1) = g.normalSlope (g.slopeIterate m n) := rfl

theorem slopeIterate_add_two (g : Parameters) (m : ℝ) (n : ℕ) :
    g.slopeIterate m (n + 2) = g.normalSlope (g.normalSlope (g.slopeIterate m n)) := rfl

theorem slopeIterate_ne_zero (g : Parameters) {m : ℝ} (hm : m ≠ 0) (n : ℕ) :
    g.slopeIterate m n ≠ 0 := by
  induction n with
  | zero => exact hm
  | succ n ih => exact g.normalSlope_ne_zero ih

/-- Equation (7): the positive even subsequence, starting at paper index zero. -/
theorem slopeIterate_even_formula (g : Parameters) {m : ℝ} (hm : 0 < m) (n : ℕ) :
    g.slopeIterate m (2 * n) = m ^ (g.exponent ^ (2 * n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpos : 0 < g.slopeIterate m (2 * n) := by
      rw [ih]
      exact Real.rpow_pos_of_pos hm _
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, slopeIterate_add_two,
      g.normalSlope_twoStep_of_pos hpos, ih, ← Real.rpow_mul hm.le, pow_add]

/-- Equation (8), equivalently equation (9) combined with the even formula. -/
theorem slopeIterate_odd_formula (g : Parameters) {m : ℝ} (hm : 0 < m) (n : ℕ) :
    g.slopeIterate m (2 * n + 1) = -((1 / m) ^ (g.exponent ^ (2 * n + 1))) := by
  rw [slopeIterate_succ, g.slopeIterate_even_formula hm,
    g.normalSlope_of_pos (Real.rpow_pos_of_pos hm _), ← Real.rpow_mul hm.le, one_div,
    ← Real.rpow_neg_eq_inv_rpow m (g.exponent ^ (2 * n + 1)), pow_succ]
  congr 2
  ring

theorem slopeIterate_even_pos (g : Parameters) {m : ℝ} (hm : 0 < m) (n : ℕ) :
    0 < g.slopeIterate m (2 * n) := by
  rw [g.slopeIterate_even_formula hm]
  exact Real.rpow_pos_of_pos hm _

theorem slopeIterate_odd_neg (g : Parameters) {m : ℝ} (hm : 0 < m) (n : ℕ) :
    g.slopeIterate m (2 * n + 1) < 0 := by
  rw [g.slopeIterate_odd_formula hm]
  exact neg_neg_of_pos (Real.rpow_pos_of_pos (one_div_pos.mpr hm) _)

/-- Reflection transports the formulas to negative initial slopes. -/
theorem slopeIterate_neg (g : Parameters) {m : ℝ} (hm : m ≠ 0) (n : ℕ) :
    g.slopeIterate (-m) n = -(g.slopeIterate m n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [slopeIterate_succ, slopeIterate_succ, ih,
      g.normalSlope_neg (g.slopeIterate_ne_zero hm n)]

/-- Lemma 3.3, equations (10)–(11), for either sign of a nonzero initial slope. -/
theorem slopeIterate_reciprocal (g : Parameters) {m : ℝ} (hm : m ≠ 0) (n : ℕ) :
    g.slopeIterate (1 / m) n = 1 / g.slopeIterate m n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [slopeIterate_succ, slopeIterate_succ, ih,
      g.normalSlope_reciprocal (g.slopeIterate_ne_zero hm n)]

end Parameters

namespace Direction

/-- Iterate the direction map with its explicit horizontal and vertical cases. -/
noncomputable def iterate (g : Parameters) (d : Direction) : ℕ → Direction
  | 0 => d
  | n + 1 => next g (iterate g d n)

/-- Every nonzero finite-slope iterate agrees with the corresponding direction iterate. -/
theorem iterate_finite (g : Parameters) {m : ℝ} (hm : m ≠ 0) (n : ℕ) :
    iterate g (finite m) n = finite (g.slopeIterate m n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change next g (iterate g (finite m) n) = _
    rw [ih, next_finite g (g.slopeIterate_ne_zero hm n)]
    rfl

end Direction

end FitzhughFarnsworth.Normality
