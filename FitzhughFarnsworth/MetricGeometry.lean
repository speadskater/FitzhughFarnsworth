/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# The taxicab plane

The plane is mathlib's `WithLp 1 (ℝ × ℝ)`, equipped with its standard metric,
normed additive group, and real normed-space structures. Coordinate accessors
retain the paper's `x` and `y` notation without introducing another metric.
-/

@[expose] public section

namespace FitzhughFarnsworth

/-- The real taxicab plane, using mathlib's standard `L¹` product metric. -/
abbrev Point := WithLp 1 (ℝ × ℝ)

namespace Point

/-- Construct a point from its Cartesian coordinates. -/
abbrev mk (x y : ℝ) : Point := WithLp.toLp 1 (x, y)

/-- The horizontal coordinate of a point in the taxicab plane. -/
abbrev x (p : Point) : ℝ := p.fst

/-- The vertical coordinate of a point in the taxicab plane. -/
abbrev y (p : Point) : ℝ := p.snd

@[simp] theorem mk_x (x y : ℝ) : (Point.mk x y).x = x := rfl

@[simp] theorem mk_y (x y : ℝ) : (Point.mk x y).y = y := rfl

/-- Two taxicab points are equal when their Cartesian coordinates agree. -/
@[ext] theorem ext {p q : Point} (hx : p.x = q.x) (hy : p.y = q.y) : p = q :=
  (WithLp.equiv 1 (ℝ × ℝ)).injective (Prod.ext hx hy)

@[simp] theorem mk_xy (p : Point) : Point.mk p.x p.y = p := by
  apply Point.ext <;> rfl

@[simp] theorem add_x (p q : Point) : (p + q).x = p.x + q.x := rfl

@[simp] theorem add_y (p q : Point) : (p + q).y = p.y + q.y := rfl

@[simp] theorem neg_x (p : Point) : (-p).x = -p.x := rfl

@[simp] theorem neg_y (p : Point) : (-p).y = -p.y := rfl

@[simp] theorem sub_x (p q : Point) : (p - q).x = p.x - q.x := rfl

@[simp] theorem sub_y (p q : Point) : (p - q).y = p.y - q.y := rfl

end Point

/-- The inherited `L¹` distance is the sum of the absolute coordinate differences. -/
theorem dist_eq (p q : Point) : dist p q = |p.x - q.x| + |p.y - q.y| := by
  simpa only [Point.x, Point.y, Real.dist_eq] using WithLp.prod_dist_eq_of_L1 p q

/-- The origin of the taxicab plane. -/
def origin : Point := Point.mk 0 0

/-- A finite-slope line through the origin. Vertical lines are defined separately. -/
def slopeLine (m : ℝ) : Set Point := {p | p.y = m * p.x}

/-- The vertical coordinate axis. -/
def verticalAxis : Set Point := {p | p.x = 0}

/-- The horizontal coordinate axis, expressed as a zero-slope line. -/
def horizontalAxis : Set Point := slopeLine 0

theorem slopeLine_nonempty (m : ℝ) : (slopeLine m).Nonempty :=
  ⟨origin, by simp [slopeLine, origin]⟩

theorem verticalAxis_nonempty : verticalAxis.Nonempty := ⟨origin, rfl⟩

end FitzhughFarnsworth
