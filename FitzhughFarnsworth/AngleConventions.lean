/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.LineConfigurations.Euclidean
public import FitzhughFarnsworth.Convergence

/-!
# The four bisector conventions in Section 4

Euclidean angles are measured in radians. Taxicab arc coordinates are measured
in taxicab length along the unit diamond, counterclockwise from `(1, 0)`.
The arc-bisector construction below is tied to explicit points on the diamond
and equal lengths of its polygonal arcs.
-/

@[expose] public section

namespace FitzhughFarnsworth

/-- The first edge of the unit diamond, parametrized by taxicab arc length. -/
noncomputable def diamondFirst (t : ℝ) : Point := Point.mk (1 - t / 2) (t / 2)

/-- The second edge of the unit diamond, with arc coordinate starting at 2. -/
noncomputable def diamondSecond (t : ℝ) : Point := Point.mk (1 - t / 2) (2 - t / 2)

theorem diamondFirst_two_eq_diamondSecond_two : diamondFirst 2 = diamondSecond 2 := by
  ext <;> norm_num [diamondFirst, diamondSecond]

theorem dist_diamondFirst (t u : ℝ) : dist (diamondFirst t) (diamondFirst u) = |t - u| := by
  rw [dist_eq]
  dsimp [diamondFirst]
  rw [show 1 - t / 2 - (1 - u / 2) = -(t - u) / 2 by ring,
    show t / 2 - u / 2 = (t - u) / 2 by ring]
  norm_num only [abs_div, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem dist_diamondSecond (t u : ℝ) : dist (diamondSecond t) (diamondSecond u) = |t - u| := by
  rw [dist_eq]
  dsimp [diamondSecond]
  rw [show 1 - t / 2 - (1 - u / 2) = -(t - u) / 2 by ring,
    show 2 - t / 2 - (2 - u / 2) = -(t - u) / 2 by ring]
  norm_num only [abs_div, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem diamondFirst_on_unitDiamond {t : ℝ} (h0 : 0 ≤ t) (h2 : t ≤ 2) :
    dist origin (diamondFirst t) = 1 := by
  rw [dist_eq]
  change |0 - (1 - t / 2)| + |0 - t / 2| = 1
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  ring

theorem diamondSecond_on_unitDiamond {t : ℝ} (h2 : 2 ≤ t) (h4 : t ≤ 4) :
    dist origin (diamondSecond t) = 1 := by
  rw [dist_eq]
  change |0 - (1 - t / 2)| + |0 - (2 - t / 2)| = 1
  rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
  ring

/-- The coordinate formula for the unsigned Euclidean area of the triangle
whose vertices are the origin, `p`, and `q`. -/
noncomputable def originTriangleArea (p q : Point) : ℝ :=
  |p.x * q.y - p.y * q.x| / 2

theorem four_mul_originTriangleArea_first (t u : ℝ) :
    4 * originTriangleArea (diamondFirst t) (diamondFirst u) =
      dist (diamondFirst t) (diamondFirst u) := by
  rw [dist_diamondFirst]
  dsimp [originTriangleArea, diamondFirst]
  rw [show (1 - t / 2) * (u / 2) - t / 2 * (1 - u / 2) = (u - t) / 2 by ring]
  norm_num only [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [abs_sub_comm u t]
  ring

theorem four_mul_originTriangleArea_second (t u : ℝ) :
    4 * originTriangleArea (diamondSecond t) (diamondSecond u) =
      dist (diamondSecond t) (diamondSecond u) := by
  rw [dist_diamondSecond]
  dsimp [originTriangleArea, diamondSecond]
  rw [show (1 - t / 2) * (2 - u / 2) - (2 - t / 2) * (1 - u / 2) = (u - t) / 2 by ring]
  norm_num only [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [abs_sub_comm u t]
  ring

theorem unitDiamond_perimeter :
    dist (Point.mk 1 0) (Point.mk 0 1) + dist (Point.mk 0 1) (Point.mk (-1) 0) +
      dist (Point.mk (-1) 0) (Point.mk 0 (-1)) + dist (Point.mk 0 (-1)) (Point.mk 1 0) = 8 := by
  norm_num [dist_eq]

/-- The taxicab opposite-side/hypotenuse convention for sine. -/
noncomputable def taxicabSine (p : Point) : ℝ :=
  Metric.infDist p horizontalAxis / dist origin p

theorem taxicabSine_diamondFirst {t : ℝ} (h0 : 0 ≤ t) (h2 : t ≤ 2) :
    taxicabSine (diamondFirst t) = t / 2 := by
  rw [taxicabSine, infDist_horizontalAxis, diamondFirst_on_unitDiamond h0 h2, div_one]
  exact abs_of_nonneg (div_nonneg h0 (by norm_num))

/-- With arc length as angle, sine divided by angle is exactly 1/2 on the
first edge. In particular its near-axis ratio is 1/2, as discussed in Section 4. -/
theorem taxicabSine_div_arcAngle {t : ℝ} (h0 : 0 < t) (h2 : t ≤ 2) :
    taxicabSine (diamondFirst t) / t = 1 / 2 := by
  rw [taxicabSine_diamondFirst h0.le h2]
  have ht := ne_of_gt h0
  field_simp

namespace SlopePair

/-- Option 1: the Euclidean midpoint angle between the two upper rays. -/
noncomputable def euclideanBisectorAngle (s : SlopePair) : ℝ :=
  (Real.arctan s.a + Real.pi + Real.arctan s.b) / 2

/-- The slope of the ray bisecting the upper-ray Euclidean angle. -/
noncomputable def euclideanBisectorSlope (s : SlopePair) : ℝ :=
  Real.tan s.euclideanBisectorAngle

theorem euclideanBisectorAngle_equal_halves (s : SlopePair) :
    s.euclideanBisectorAngle - Real.arctan s.a =
      (Real.pi + Real.arctan s.b) - s.euclideanBisectorAngle := by
  dsimp [euclideanBisectorAngle]
  ring

theorem euclideanBisectorAngle_bounds {s : SlopePair} (h : s.EvenConfig) :
    Real.pi / 4 < s.euclideanBisectorAngle ∧ s.euclideanBisectorAngle < Real.pi / 2 := by
  have ha0 := Real.arctan_pos.mpr h.1
  have ha1 := Real.arctan_strictMono h.2.1
  have hb0 := Real.neg_pi_div_two_lt_arctan s.b
  have hb1 := Real.arctan_strictMono h.2.2
  rw [Real.arctan_one] at ha1
  rw [Real.arctan_neg, Real.arctan_one] at hb1
  dsimp [euclideanBisectorAngle]
  constructor <;> linarith

theorem arctan_euclideanBisectorSlope {s : SlopePair} (h : s.EvenConfig) :
    Real.arctan s.euclideanBisectorSlope = s.euclideanBisectorAngle := by
  obtain ⟨hl, hu⟩ := euclideanBisectorAngle_bounds h
  exact Real.arctan_tan (by linarith [Real.pi_pos]) hu

/-- Arc coordinates of the intersections of the two rays with the unit diamond. -/
noncomputable def firstArcCoordinate (s : SlopePair) : ℝ := 2 * s.a / (1 + s.a)

/-- The second upper ray's arc coordinate on the taxicab unit diamond. -/
noncomputable def secondArcCoordinate (s : SlopePair) : ℝ := 2 + 2 / (1 - s.b)

/-- The midpoint of the two ray-intersection arc coordinates. -/
noncomputable def arcBisectorCoordinate (s : SlopePair) : ℝ :=
  (s.firstArcCoordinate + s.secondArcCoordinate) / 2

/-- Option 2: bisect taxicab arc length on the unit diamond. -/
noncomputable def arcBisectorSlope (s : SlopePair) : ℝ :=
  s.arcBisectorCoordinate / (2 - s.arcBisectorCoordinate)

/-- Option 3: take the upper positive line in the first geometric midset. -/
noncomputable def firstMidsetBisectorSlope (s : SlopePair) : ℝ := s.toOdd.b

/-- Option 4: use the odd limiting pair associated with an even limit `l`. -/
noncomputable def limitingBisectorSlope (l : SlopePair) : ℝ := l.toOdd.b

theorem firstArcCoordinate_bounds {s : SlopePair} (h : s.EvenConfig) :
    0 < s.firstArcCoordinate ∧ s.firstArcCoordinate < 1 := by
  have hd : 0 < 1 + s.a := by linarith [h.1]
  constructor
  · exact div_pos (mul_pos (by norm_num) h.1) hd
  · apply (div_lt_iff₀ hd).mpr
    linarith [h.2.1]

theorem secondArcCoordinate_bounds {s : SlopePair} (h : s.EvenConfig) :
    2 < s.secondArcCoordinate ∧ s.secondArcCoordinate < 3 := by
  have hd : 0 < 1 - s.b := by linarith [h.2.2]
  have hl : 0 < 2 / (1 - s.b) := div_pos (by norm_num) hd
  have hu : 2 / (1 - s.b) < 1 := (div_lt_iff₀ hd).mpr (by linarith [h.2.2])
  dsimp [secondArcCoordinate]
  constructor <;> linarith

theorem arcBisectorCoordinate_bounds {s : SlopePair} (h : s.EvenConfig) :
    1 < s.arcBisectorCoordinate ∧ s.arcBisectorCoordinate < 2 := by
  obtain ⟨ha0, ha1⟩ := firstArcCoordinate_bounds h
  obtain ⟨hb2, hb3⟩ := secondArcCoordinate_bounds h
  dsimp [arcBisectorCoordinate]
  constructor <;> linarith

theorem firstArcCoordinate_eq_length {s : SlopePair} (h : s.EvenConfig) :
    dist (diamondFirst 0) (diamondFirst s.firstArcCoordinate) = s.firstArcCoordinate := by
  rw [dist_diamondFirst, zero_sub, abs_neg, abs_of_pos (firstArcCoordinate_bounds h).1]

theorem secondArcCoordinate_eq_length {s : SlopePair} (h : s.EvenConfig) :
    dist (diamondFirst 0) (diamondFirst 2) +
      dist (diamondSecond 2) (diamondSecond s.secondArcCoordinate) = s.secondArcCoordinate := by
  rw [dist_diamondFirst, dist_diamondSecond,
    abs_of_neg (by norm_num : (0 : ℝ) - 2 < 0),
    abs_of_neg (by linarith [(secondArcCoordinate_bounds h).1])]
  ring

theorem diamondFirst_firstArcCoordinate_mem {s : SlopePair} (h : s.EvenConfig) :
    diamondFirst s.firstArcCoordinate ∈ slopeLine s.a := by
  have hd : 1 + s.a ≠ 0 := by linarith [h.1]
  change (2 * s.a / (1 + s.a)) / 2 = s.a * (1 - (2 * s.a / (1 + s.a)) / 2)
  field_simp
  ring

theorem diamondSecond_secondArcCoordinate_mem {s : SlopePair} (h : s.EvenConfig) :
    diamondSecond s.secondArcCoordinate ∈ slopeLine s.b := by
  have hd : 1 - s.b ≠ 0 := by linarith [h.2.2]
  change 2 - (2 + 2 / (1 - s.b)) / 2 = s.b * (1 - (2 + 2 / (1 - s.b)) / 2)
  field_simp
  ring

theorem diamondFirst_arcBisectorCoordinate_mem {s : SlopePair} (h : s.EvenConfig) :
    diamondFirst s.arcBisectorCoordinate ∈ slopeLine s.arcBisectorSlope := by
  have hd : 2 - s.arcBisectorCoordinate ≠ 0 := by linarith [(arcBisectorCoordinate_bounds h).2]
  change s.arcBisectorCoordinate / 2 =
    (s.arcBisectorCoordinate / (2 - s.arcBisectorCoordinate)) * (1 - s.arcBisectorCoordinate / 2)
  field_simp

theorem arcBisectorSlope_gt_one {s : SlopePair} (h : s.EvenConfig) :
    1 < s.arcBisectorSlope := by
  obtain ⟨hl, hu⟩ := arcBisectorCoordinate_bounds h
  apply (lt_div_iff₀ (by linarith : 0 < 2 - s.arcBisectorCoordinate)).mpr
  linarith

/-- The midpoint ray divides the polygonal unit-circle arc into equal lengths.
The second part passes through the top vertex; it is explicitly a sum of two
edge lengths, not the straight-line distance between the endpoints. -/
theorem arcBisector_equal_arc_lengths {s : SlopePair} (h : s.EvenConfig) :
    dist (diamondFirst s.firstArcCoordinate) (diamondFirst s.arcBisectorCoordinate) =
      dist (diamondFirst s.arcBisectorCoordinate) (diamondFirst 2) +
        dist (diamondSecond 2) (diamondSecond s.secondArcCoordinate) := by
  obtain ⟨ha0, ha1⟩ := firstArcCoordinate_bounds h
  obtain ⟨hb2, hb3⟩ := secondArcCoordinate_bounds h
  obtain ⟨ht1, ht2⟩ := arcBisectorCoordinate_bounds h
  rw [dist_diamondFirst, dist_diamondFirst, dist_diamondSecond,
    abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)]
  dsimp [arcBisectorCoordinate]
  ring

/-- Arc bisection also bisects the radial sector area, using the determinant
formula for each triangle in the polygonal sector. -/
theorem arcBisector_equal_sector_areas {s : SlopePair} (h : s.EvenConfig) :
    originTriangleArea (diamondFirst s.firstArcCoordinate) (diamondFirst s.arcBisectorCoordinate) =
      originTriangleArea (diamondFirst s.arcBisectorCoordinate) (diamondFirst 2) +
        originTriangleArea (diamondSecond 2) (diamondSecond s.secondArcCoordinate) := by
  have h1 := four_mul_originTriangleArea_first s.firstArcCoordinate s.arcBisectorCoordinate
  have h2 := four_mul_originTriangleArea_first s.arcBisectorCoordinate 2
  have h3 := four_mul_originTriangleArea_second 2 s.secondArcCoordinate
  have he := arcBisector_equal_arc_lengths h
  linarith

open Filter Topology in
theorem limitingBisectorSlope_tendsto {s l : SlopePair} (h : s.ConvergesToCycle l l.toOdd) :
    Tendsto (fun n => (s.oddIterate n).b) atTop (𝓝 l.limitingBisectorSlope) := h.2.2.2

/-- Exact arithmetic distinguishes two of the Section 4 conventions. -/
theorem arc_and_firstMidset_differ :
    let s : SlopePair := ⟨1 / 4, -2⟩
    s.EvenConfig ∧ s.arcBisectorSlope = 23 / 7 ∧
      s.firstMidsetBisectorSlope = 5 / 2 ∧ s.arcBisectorSlope ≠ s.firstMidsetBisectorSlope := by
  norm_num [EvenConfig, arcBisectorSlope, arcBisectorCoordinate, firstArcCoordinate,
    secondArcCoordinate, firstMidsetBisectorSlope, toOdd]

end SlopePair
end FitzhughFarnsworth
