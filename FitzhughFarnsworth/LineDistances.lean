/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Midsets
public import FitzhughFarnsworth.MetricGeometry
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Distances to lines

The formulas are proved from the infimum over all points on a line, using a
lower bound and an explicit nearest point. They are not definitions of distance.
-/

@[expose] public section

namespace FitzhughFarnsworth

theorem infDist_verticalAxis (p : Point) :
    Metric.infDist p verticalAxis = |p.x| := by
  apply le_antisymm
  · calc
      Metric.infDist p verticalAxis ≤ dist p (Point.mk 0 p.y) :=
        Metric.infDist_le_dist_of_mem rfl
      _ = |p.x| := by simp [dist_eq]
  · apply (Metric.le_infDist verticalAxis_nonempty).mpr
    intro q hq
    change q.x = 0 at hq
    simp only [dist_eq, hq, sub_zero]
    exact le_add_of_nonneg_right (abs_nonneg _)

theorem shallow_residual_le_dist (p q : Point) (m : ℝ)
    (hm : |m| ≤ 1) (hq : q ∈ slopeLine m) :
    |p.y - m * p.x| ≤ dist p q := by
  change q.y = m * q.x at hq
  calc
    |p.y - m * p.x| = |(p.y - q.y) + m * (q.x - p.x)| := by rw [hq]; ring_nf
    _ ≤ |p.y - q.y| + |m * (q.x - p.x)| := abs_add_le _ _
    _ = |p.y - q.y| + |m| * |q.x - p.x| := by rw [abs_mul]
    _ ≤ |p.y - q.y| + 1 * |q.x - p.x| := by
      gcongr
    _ = dist p q := by simp [dist_eq, abs_sub_comm, add_comm]

theorem infDist_slopeLine_of_abs_le_one (p : Point) (m : ℝ) (hm : |m| ≤ 1) :
    Metric.infDist p (slopeLine m) = |p.y - m * p.x| := by
  apply le_antisymm
  · calc
      Metric.infDist p (slopeLine m) ≤ dist p (Point.mk p.x (m * p.x)) :=
        Metric.infDist_le_dist_of_mem rfl
      _ = |p.y - m * p.x| := by simp [dist_eq]
  · exact (Metric.le_infDist (slopeLine_nonempty m)).mpr
      (fun _ hq => shallow_residual_le_dist p _ m hm hq)

theorem infDist_horizontalAxis (p : Point) :
    Metric.infDist p horizontalAxis = |p.y| := by
  simpa [horizontalAxis] using infDist_slopeLine_of_abs_le_one p 0 (by norm_num)

theorem infDist_slopeLine_of_one_le_abs (p : Point) (m : ℝ) (hm : 1 ≤ |m|) :
    Metric.infDist p (slopeLine m) = |p.x - p.y / m| := by
  have hm0 : m ≠ 0 := by intro h; norm_num [h] at hm
  have hinv : |1 / m| ≤ 1 := by
    rw [abs_div, abs_one]
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hm
  apply le_antisymm
  · have hproj : (Point.mk (p.y / m) p.y) ∈ slopeLine m := by
      change p.y = m * (p.y / m)
      field_simp
    calc
      Metric.infDist p (slopeLine m) ≤ dist p (Point.mk (p.y / m) p.y) :=
        Metric.infDist_le_dist_of_mem hproj
      _ = |p.x - p.y / m| := by simp [dist_eq]
  · apply (Metric.le_infDist (slopeLine_nonempty m)).mpr
    intro q hq
    change q.y = m * q.x at hq
    have hswap : (Point.mk q.y q.x) ∈ slopeLine (1 / m) := by
      change q.x = (1 / m) * q.y
      rw [hq]
      field_simp
    have h := shallow_residual_le_dist (Point.mk p.y p.x) (Point.mk q.y q.x) (1 / m) hinv hswap
    simpa [dist_eq, div_eq_mul_inv, mul_comm, add_comm] using h

/-- A uniform formula covering every finite slope, including the boundaries ±1. -/
theorem infDist_slopeLine (p : Point) (m : ℝ) :
    Metric.infDist p (slopeLine m) = |p.y - m * p.x| / max 1 |m| := by
  rcases le_total |m| 1 with hm | hm
  · rw [max_eq_left hm, div_one]
    exact infDist_slopeLine_of_abs_le_one p m hm
  · have hm0 : m ≠ 0 := by intro h; norm_num [h] at hm
    rw [max_eq_right hm, infDist_slopeLine_of_one_le_abs p m hm, ← abs_div]
    have h : p.x - p.y / m = -((p.y - m * p.x) / m) := by
      field_simp
      ring
    rw [h, abs_neg]

/-- Theorem 3, from the coordinate axes to the two diagonal lines. -/
theorem midset_axes :
    midset horizontalAxis verticalAxis = slopeLine 1 ∪ slopeLine (-1) := by
  ext p
  simp only [mem_midset, infDist_horizontalAxis, infDist_verticalAxis,
    Set.mem_union, slopeLine, Set.mem_ofPred_eq, one_mul, neg_one_mul]
  exact abs_eq_abs

/-- Theorem 3, from the two diagonal lines back to the coordinate axes. -/
theorem midset_diagonals :
    midset (slopeLine 1) (slopeLine (-1)) = horizontalAxis ∪ verticalAxis := by
  ext p
  rw [mem_midset, infDist_slopeLine_of_abs_le_one p 1 (by norm_num),
    infDist_slopeLine_of_abs_le_one p (-1) (by norm_num)]
  simp only [Set.mem_union, horizontalAxis, slopeLine, verticalAxis,
    Set.mem_ofPred_eq, zero_mul, one_mul, neg_one_mul, abs_eq_abs]
  constructor
  · rintro (h | h)
    · right; linarith
    · left; linarith
  · rintro (h | h)
    · right; linarith
    · left; linarith

/-- The geometric source of the rational slope updates in Algorithm 6.
The two output lines are unordered, so the same identity serves both parities. -/
theorem midset_shallow_steep (a b : ℝ) (ha : |a| ≤ 1) (hb : 1 < |b|) :
    midset (slopeLine a) (slopeLine b) =
      slopeLine (b * (a - 1) / (b - 1)) ∪ slopeLine (b * (a + 1) / (b + 1)) := by
  have hb0 : b ≠ 0 := by intro h; norm_num [h] at hb
  have hbm : b - 1 ≠ 0 := by
    intro h
    have : b = 1 := by linarith
    norm_num [this] at hb
  have hbp : b + 1 ≠ 0 := by
    intro h
    have : b = -1 := by linarith
    norm_num [this] at hb
  ext p
  rw [mem_midset, infDist_slopeLine_of_abs_le_one p a ha,
    infDist_slopeLine_of_one_le_abs p b hb.le, abs_eq_abs]
  change (p.y - a * p.x = p.x - p.y / b ∨ p.y - a * p.x = -(p.x - p.y / b)) ↔
    (p.y = b * (a - 1) / (b - 1) * p.x ∨ p.y = b * (a + 1) / (b + 1) * p.x)
  constructor
  · rintro (h | h)
    · right
      field_simp [hb0, hbp] at h ⊢
      nlinarith [h]
    · left
      field_simp [hb0, hbm] at h ⊢
      nlinarith [h]
  · rintro (h | h)
    · right
      field_simp [hb0, hbm] at h ⊢
      nlinarith [h]
    · left
      field_simp [hb0, hbp] at h ⊢
      nlinarith [h]

end FitzhughFarnsworth
