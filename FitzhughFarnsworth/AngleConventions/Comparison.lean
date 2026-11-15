module

public import FitzhughFarnsworth.AngleConventions
public import FitzhughFarnsworth.Convergence.Enclosures

/-!
# An exact separation of all four bisector conventions

For the initial slopes `1/4` and `-2`, the Euclidean bisector, limiting-midset
bisector, first-midset bisector, and diamond-arc bisector occur in strictly
increasing slope order. All bounds use exact real arithmetic, and existence of
the limiting cycle is supplied by the convergence theorem.
-/

@[expose] public section

namespace FitzhughFarnsworth
namespace SlopePair

noncomputable def comparisonPair : SlopePair := ⟨1 / 4, -2⟩

theorem comparisonPair_config : comparisonPair.EvenConfig := by
  norm_num [comparisonPair, EvenConfig]

theorem comparisonPair_euclidean_quadratic :
    7 * comparisonPair.euclideanBisectorSlope ^ 2 -
      12 * comparisonPair.euclideanBisectorSlope - 7 = 0 := by
  have hθ := euclideanBisectorAngle_bounds comparisonPair_config
  have ht : 1 < comparisonPair.euclideanBisectorSlope := by
    apply Real.arctan_lt_arctan_iff.mp
    rw [Real.arctan_one, arctan_euclideanBisectorSlope comparisonPair_config]
    exact hθ.1
  have hd : 1 - comparisonPair.euclideanBisectorSlope ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (comparisonPair.euclideanBisectorSlope - 1)]
  have hsum : Real.arctan (1 / 4 : ℝ) + Real.arctan (-2 : ℝ) = Real.arctan (-7 / 6 : ℝ) := by
    convert Real.arctan_add (show (1 / 4 : ℝ) * (-2) < 1 by norm_num) using 1
    norm_num
  have hangle : 2 * comparisonPair.euclideanBisectorAngle =
      (Real.arctan (1 / 4 : ℝ) + Real.arctan (-2 : ℝ)) + Real.pi := by
    dsimp [comparisonPair, euclideanBisectorAngle]
    ring
  have htan : Real.tan (2 * comparisonPair.euclideanBisectorAngle) = (-7 / 6 : ℝ) := by
    rw [hangle, Real.tan_add_pi, hsum, Real.tan_arctan]
  rw [Real.tan_two_mul] at htan
  change 2 * comparisonPair.euclideanBisectorSlope /
    (1 - comparisonPair.euclideanBisectorSlope ^ 2) = (-7 / 6 : ℝ) at htan
  have he := (div_eq_iff hd).mp htan
  nlinarith

theorem comparisonPair_euclidean_lt : comparisonPair.euclideanBisectorSlope < 11 / 5 := by
  have ht : 1 < comparisonPair.euclideanBisectorSlope := by
    apply Real.arctan_lt_arctan_iff.mp
    rw [Real.arctan_one, arctan_euclideanBisectorSlope comparisonPair_config]
    exact (euclideanBisectorAngle_bounds comparisonPair_config).1
  have he := comparisonPair_euclidean_quadratic
  by_contra hn
  have hb : 11 / 5 ≤ comparisonPair.euclideanBisectorSlope := le_of_not_gt hn
  have hm := mul_nonneg (sub_nonneg.mpr hb)
    (show 0 ≤ 7 * comparisonPair.euclideanBisectorSlope + 17 / 5 by linarith)
  nlinarith

theorem comparisonPair_second_even_iterate :
    (comparisonPair.evenIterate 2).a = 5035 / 13426 ∧
      (comparisonPair.evenIterate 2).b = -13585 / 5194 := by
  norm_num [comparisonPair, evenIterate, twoStep, toOdd, toEven]

theorem comparisonPair_limit_enclosure {l : SlopePair} (hl : l.EvenConfig)
    (ho : l.Orthogonal) (hc : comparisonPair.ConvergesToCycle l l.toOdd) :
    18461 / 8391 ≤ l.limitingBisectorSlope ∧ l.limitingBisectorSlope ≤ 18779 / 8391 := by
  have hp : -1 ≤ comparisonPair.a * comparisonPair.b := by norm_num [comparisonPair]
  obtain ⟨ha, hb⟩ := limit_enclosure_of_product_ge comparisonPair_config hp hc 2
  rw [comparisonPair_second_even_iterate.1] at ha
  rw [comparisonPair_second_even_iterate.2] at hb
  norm_num at hb
  have hd : 0 < 1 - l.a := by linarith [hl.2.1]
  have hformula : l.limitingBisectorSlope = (l.a + 1) / (1 - l.a) := by
    rw [limitingBisectorSlope, toOdd_b_of_orthogonal hl ho,
      show l.a - 1 = -(1 - l.a) by ring, neg_div_neg_eq]
  rw [hformula]
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    nlinarith

/-- All four Section 4 conventions differ for this exact initial pair. -/
theorem exists_four_distinct_bisectors :
    ∃ l : SlopePair, l.EvenConfig ∧ l.Orthogonal ∧
      comparisonPair.ConvergesToCycle l l.toOdd ∧
      comparisonPair.euclideanBisectorSlope < l.limitingBisectorSlope ∧
      l.limitingBisectorSlope < comparisonPair.firstMidsetBisectorSlope ∧
      comparisonPair.firstMidsetBisectorSlope < comparisonPair.arcBisectorSlope := by
  obtain ⟨l, hl, ho, hc⟩ := exists_orthogonal_limit_cycle comparisonPair_config
  obtain ⟨hlo, hhi⟩ := comparisonPair_limit_enclosure hl ho hc
  have he := comparisonPair_euclidean_lt
  have hfirst : comparisonPair.firstMidsetBisectorSlope = 5 / 2 := by
    norm_num [comparisonPair, firstMidsetBisectorSlope, toOdd]
  have harc : comparisonPair.arcBisectorSlope = 23 / 7 := by
    norm_num [comparisonPair, arcBisectorSlope, arcBisectorCoordinate,
      firstArcCoordinate, secondArcCoordinate]
  refine ⟨l, hl, ho, hc, ?_, ?_, ?_⟩
  · linarith
  · rw [hfirst]
    linarith
  · rw [hfirst, harc]
    norm_num

end SlopePair
end FitzhughFarnsworth
