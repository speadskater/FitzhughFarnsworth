/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Normality.RadonGeometry

/-!
# Reflexivity of geometric normality in the joined norm

Theorem 4.1's sufficiency is proved for actual norm minimization. Directional
derivatives agree at the four axis joins, and the global convexity proved in
`RadonGeometry` turns tangency into a global minimum. No smoothness or convexity
of the joined curve is assumed.
-/

@[expose] public section

namespace FitzhughFarnsworth.Normality.Radon

open Set Filter Topology

private theorem hasDerivAt_ite {f h : ℝ → ℝ} {x d : ℝ}
    (hf : HasDerivAt f d x) (hh : HasDerivAt h d x) (he : f x = h x)
    (P : ℝ → Prop) [DecidablePred P] :
    HasDerivAt (fun t => if P t then f t else h t) d x := by
  apply HasDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  filter_upwards [hf.isLittleO.bound hc, hh.isLittleO.bound hc] with t ht₁ ht₂
  by_cases hx : P x <;> by_cases ht : P t <;> simp only [hx, ht, ↓reduceIte, he] at *
  all_goals assumption

private theorem min_iff_deriv_zero {f : ℝ → ℝ} {d : ℝ}
    (hc : ConvexOn ℝ univ f) (hd : HasDerivAt f d 0) :
    (∀ t : ℝ, f 0 ≤ f t) ↔ d = 0 := by
  constructor
  · intro h
    exact (show IsLocalMin f 0 from Eventually.of_forall h).hasDerivAt_eq_zero hd
  · intro h t
    subst d
    exact hc.isMinOn_of_rightDeriv_eq_zero (by simp)
      (hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi 0)) (mem_univ t)

theorem hasDerivAt_length_line (g : Parameters) {v : ℝ × ℝ}
    (hv : 0 < g.energy v) (w : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => length g (v + t • w))
      ((g.dualCoord v.1 * w.1 + g.dualCoord v.2 * w.2) *
        g.energy v ^ (1 / g.p - 1)) 0 := by
  have hd := (g.hasDerivAt_energy_line v w).rpow_const
    (p := 1 / g.p) (Or.inl (by simpa using hv.ne'))
  convert hd using 1
  · ext t
    exact g.norm_eq_energy _
  · simp only [zero_smul, add_zero]
    field_simp [(zero_lt_one.trans g.one_lt_p).ne']

/-- Every p-norm has the same directional derivative at the horizontal unit point. -/
theorem hasDerivAt_length_horizontal (g : Parameters) (w : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => length g ((1, 0) + t • w)) w.1 0 := by
  simpa [Parameters.energy, (zero_lt_one.trans g.one_lt_p).ne'] using
    hasDerivAt_length_line g (v := (1, 0)) (by
      simp [Parameters.energy, (zero_lt_one.trans g.one_lt_p).ne']) w

/-- Every p-norm has the same directional derivative at the vertical unit point. -/
theorem hasDerivAt_length_vertical (g : Parameters) (w : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => length g ((0, 1) + t • w)) w.2 0 := by
  simpa [Parameters.energy, (zero_lt_one.trans g.one_lt_p).ne'] using
    hasDerivAt_length_line g (v := (0, 1)) (by
      simp [Parameters.energy, (zero_lt_one.trans g.one_lt_p).ne']) w

/-- Smooth agreement at the horizontal join, for every transverse direction. -/
theorem hasDerivAt_joined_horizontal (g h : Parameters) (w : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => joinedNorm g h ((1, 0) + t • w)) w.1 0 := by
  simpa only [joinedNorm_quadrant] using hasDerivAt_ite
    (hasDerivAt_length_horizontal g w) (hasDerivAt_length_horizontal h w)
    (by simp) (fun t => 0 ≤ ((1, 0) + t • w).1 * ((1, 0) + t • w).2)

/-- Smooth agreement at the vertical join, for every transverse direction. -/
theorem hasDerivAt_joined_vertical (g h : Parameters) (w : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => joinedNorm g h ((0, 1) + t • w)) w.2 0 := by
  simpa only [joinedNorm_quadrant] using hasDerivAt_ite
    (hasDerivAt_length_vertical g w) (hasDerivAt_length_vertical h w)
    (by simp) (fun t => 0 ≤ ((0, 1) + t • w).1 * ((0, 1) + t • w).2)

private theorem joined_eq_length_eventually (g h : Parameters) {m : ℝ} (hm : 0 < m)
    (w : ℝ × ℝ) :
    (fun t : ℝ => joinedNorm g h ((1, m) + t • w)) =ᶠ[𝓝 0]
      (fun t : ℝ => length g ((1, m) + t • w)) := by
  have hc : Continuous (fun t : ℝ => (1 + t * w.1) * (m + t * w.2)) := by fun_prop
  have hp : (0 : ℝ) < (1 + 0 * w.1) * (m + 0 * w.2) := by simpa using hm
  filter_upwards [hc.continuousAt.eventually (Ioi_mem_nhds hp)] with t ht
  exact (joinedNorm_quadrant g h _).trans (ite_eq_left ht.le)

private theorem joined_eq_length_eventually_neg (g h : Parameters) {m : ℝ} (hm : m < 0)
    (w : ℝ × ℝ) :
    (fun t : ℝ => joinedNorm g h ((1, m) + t • w)) =ᶠ[𝓝 0]
      (fun t : ℝ => length h ((1, m) + t • w)) := by
  have hc : Continuous (fun t : ℝ => (1 + t * w.1) * (m + t * w.2)) := by fun_prop
  have hp : (1 + 0 * w.1) * (m + 0 * w.2) < (0 : ℝ) := by simpa using hm
  filter_upwards [hc.continuousAt.eventually (Iio_mem_nhds hp)] with t ht
  exact (joinedNorm_quadrant g h _).trans (ite_eq_right (not_le.mpr ht))

theorem convexOn_joined_line (g h : Parameters) (v w : ℝ × ℝ) :
    ConvexOn ℝ univ (fun t : ℝ => joinedNorm g h (v + t • w)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have he : v + (a • x + b • y) • w = a • (v + x • w) + b • (v + y • w) := by
    rw [smul_add, smul_add, smul_smul, smul_smul, add_smul]
    rw [add_add_add_comm, ← add_smul a b v, hab, one_smul]
    rfl
  dsimp only
  rw [he]
  exact (convexOn_joinedNorm g h).2 (mem_univ _) (mem_univ _) ha hb hab

/-- Normality defined by the actual norm on the constructed Minkowski plane. -/
def IsNormal (g : Parameters) (v w : ℝ × ℝ) : Prop :=
  ∀ t : ℝ, joinedNorm g g.conjugate v ≤ joinedNorm g g.conjugate (v + t • w)

/-- Inside each open quadrant the metric normal is computed with that quadrant's exponent.
The two axes follow from the proved agreement of derivatives at the joins. -/
theorem isNormal_direction_iff (g : Parameters) (d e : Direction) :
    IsNormal g e.vector d.vector ↔
      (if 0 ≤ e.vector.1 * e.vector.2 then g else g.conjugate).IsNormal e.vector d.vector := by
  cases e with
  | vertical =>
    have hm := min_iff_deriv_zero (convexOn_joined_line g g.conjugate (0, 1) d.vector)
      (hasDerivAt_joined_vertical g g.conjugate d.vector)
    simpa [IsNormal, Direction.vector, Parameters.isNormal_iff] using hm
  | finite m =>
    rcases lt_trichotomy m 0 with hm | rfl | hm
    · have hp : 0 < g.conjugate.energy (1, m) := by
        dsimp [Parameters.energy]
        rw [abs_one, Real.one_rpow]
        positivity
      have hd := (hasDerivAt_length_line g.conjugate hp d.vector).congr_of_eventuallyEq
        (joined_eq_length_eventually_neg g g.conjugate hm d.vector)
      have hi := min_iff_deriv_zero (convexOn_joined_line g g.conjugate (1, m) d.vector) hd
      simpa only [IsNormal, Direction.vector, zero_smul, add_zero, one_mul,
        ite_eq_right (not_le.mpr hm), Parameters.isNormal_iff, mul_eq_zero,
        (Real.rpow_pos_of_pos hp _).ne', or_false] using hi
    · have hi := min_iff_deriv_zero (convexOn_joined_line g g.conjugate (1, 0) d.vector)
        (hasDerivAt_joined_horizontal g g.conjugate d.vector)
      simpa [IsNormal, Direction.vector, Parameters.isNormal_iff] using hi
    · have hp : 0 < g.energy (1, m) := by
        dsimp [Parameters.energy]
        rw [abs_one, Real.one_rpow]
        positivity
      have hd := (hasDerivAt_length_line g hp d.vector).congr_of_eventuallyEq
        (joined_eq_length_eventually g g.conjugate hm d.vector)
      have hi := min_iff_deriv_zero (convexOn_joined_line g g.conjugate (1, m) d.vector) hd
      simpa only [IsNormal, Direction.vector, zero_smul, add_zero, one_mul,
        ite_eq_left hm.le, Parameters.isNormal_iff, mul_eq_zero,
        (Real.rpow_pos_of_pos hp _).ne', or_false] using hi

private theorem conjugate_next_next (g : Parameters) (d : Direction) :
    Direction.next g.conjugate (Direction.next g d) = d := by
  cases d with
  | vertical => simp
  | finite m =>
    by_cases hm : m = 0
    · subst m
      simp
    · rw [Direction.next_finite g hm,
        Direction.next_finite g.conjugate (g.normalSlope_ne_zero hm),
        g.conjugate_normalSlope_normalSlope hm]

private theorem normal_iff_conjugate_next (g : Parameters) (d e : Direction) :
    g.IsNormal e.vector d.vector ↔ d = Direction.next g.conjugate e := by
  rw [Direction.isNormal_iff_eq_next]
  constructor
  · rintro rfl
    exact (conjugate_next_next g d).symm
  · rintro rfl
    simpa only [Parameters.conjugate_conjugate] using (conjugate_next_next g.conjugate e).symm

/-- Tangency in the joined curve gives exactly the conjugate-quadrant direction map. -/
theorem isNormal_iff_eq_radonNext_rev (g : Parameters) (d e : Direction) :
    IsNormal g e.vector d.vector ↔ d = Direction.radonNext g e := by
  rw [isNormal_direction_iff]
  cases e with
  | vertical =>
    simpa [Direction.vector, Direction.radonNext] using normal_iff_conjugate_next g d .vertical
  | finite m =>
    rcases lt_trichotomy m 0 with hm | rfl | hm
    · simpa [Direction.vector, not_le.mpr hm, Direction.radonNext, hm.ne, not_lt.mpr hm.le,
        Direction.next_finite g hm.ne] using normal_iff_conjugate_next g.conjugate d (.finite m)
    · simpa [Direction.vector, Direction.radonNext] using normal_iff_conjugate_next g d (.finite 0)
    · simpa [Direction.vector, hm.le, Direction.radonNext, hm.ne', hm,
        Direction.next_finite g.conjugate hm.ne'] using normal_iff_conjugate_next g d (.finite m)

/-- Theorem 4.1: the joined metric has a unique normal direction, given by the involution. -/
theorem isNormal_iff_eq_radonNext (g : Parameters) (d e : Direction) :
    IsNormal g e.vector d.vector ↔ e = Direction.radonNext g d := by
  rw [isNormal_iff_eq_radonNext_rev]
  constructor <;> rintro rfl <;> exact (Direction.radonNext_involutive g _).symm

/-- Reflexivity for every line, including the four axis joins. -/
theorem normality_reflexive (g : Parameters) (d e : Direction) :
    IsNormal g e.vector d.vector ↔ IsNormal g d.vector e.vector := by
  rw [isNormal_iff_eq_radonNext, isNormal_iff_eq_radonNext_rev]

theorem IsNormal.smul (g : Parameters) {v w : ℝ × ℝ} (hn : IsNormal g v w) (a b : ℝ) :
    IsNormal g (a • v) (b • w) := by
  intro t
  by_cases ha : a = 0
  · subst a
    simpa only [zero_smul, zero_add, (joinedNorm_eq_zero_iff g g.conjugate 0).mpr rfl] using
      joinedNorm_nonneg g g.conjugate (t • (b • w))
  · have he : a • v + t • (b • w) = a • (v + (t * b / a) • w) := by
      rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ ha]
    rw [he, joinedNorm_smul, joinedNorm_smul]
    exact mul_le_mul_of_nonneg_left (hn (t * b / a)) (abs_nonneg a)

theorem isNormal_smul_iff (g : Parameters) (v w : ℝ × ℝ)
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    IsNormal g (a • v) (b • w) ↔ IsNormal g v w := by
  refine ⟨fun h => ?_, fun h => h.smul g a b⟩
  simpa only [smul_smul, inv_mul_cancel₀ ha, inv_mul_cancel₀ hb, one_smul] using h.smul g a⁻¹ b⁻¹

/-- Every nonzero coordinate vector spans one of the represented finite or vertical lines. -/
theorem exists_direction (v : ℝ × ℝ) (hv : v ≠ 0) :
    ∃ (d : Direction) (a : ℝ), a ≠ 0 ∧ v = a • d.vector := by
  rcases v with ⟨x, y⟩
  by_cases hx : x = 0
  · subst x
    refine ⟨.vertical, y, ?_, ?_⟩
    · intro hy
      apply hv
      simp [hy]
    · ext <;> simp [Direction.vector]
  · refine ⟨.finite (y / x), x, hx, ?_⟩
    ext <;> simp [Direction.vector, mul_div_cancel₀ _ hx]

/-- Reflexive distance-minimizing normality for arbitrary vectors in the constructed norm. -/
theorem normality_reflexive_vectors (g : Parameters) (v w : ℝ × ℝ) :
    IsNormal g v w ↔ IsNormal g w v := by
  by_cases hv : v = 0
  · subst v
    simp only [IsNormal, smul_zero, add_zero, le_refl, implies_true, iff_true, zero_add]
    intro t
    simpa only [(joinedNorm_eq_zero_iff g g.conjugate 0).mpr rfl] using
      joinedNorm_nonneg g g.conjugate (t • w)
  by_cases hw : w = 0
  · subst w
    simp only [IsNormal, smul_zero, add_zero, le_refl, implies_true, true_iff, zero_add]
    intro t
    simpa only [(joinedNorm_eq_zero_iff g g.conjugate 0).mpr rfl] using
      joinedNorm_nonneg g g.conjugate (t • v)
  obtain ⟨d, a, ha, rfl⟩ := exists_direction v hv
  obtain ⟨e, b, hb, rfl⟩ := exists_direction w hw
  rw [isNormal_smul_iff g _ _ ha hb, isNormal_smul_iff g _ _ hb ha]
  exact normality_reflexive g e d

/-- The infimum in the constructed metric is attained at the common origin. -/
theorem IsNormal.infDist (g : Parameters) {v w : ℝ × ℝ} (hn : IsNormal g v w) :
    Metric.infDist (ofCoords g v) (Set.range (fun t : ℝ => ofCoords g (t • w))) =
      ‖ofCoords g v‖ := by
  apply le_antisymm
  · simpa only [dist_zero_right] using Metric.infDist_le_dist_of_mem
      (show (0 : Plane g) ∈ Set.range (fun t : ℝ => ofCoords g (t • w)) from
        ⟨0, by change ofCoords g (0 • w) = 0; rw [zero_smul]; rfl⟩)
  · apply (Metric.le_infDist (Set.range_nonempty _)).mpr
    rintro _ ⟨t, rfl⟩
    rw [dist_ofCoords, norm_ofCoords]
    simpa only [sub_eq_add_neg, neg_smul] using hn (-t)

/-- Every point on the next normal line has the origin as a nearest point on the old line. -/
theorem radonNext_infDist (g : Parameters) (d : Direction) (a : ℝ) :
    Metric.infDist (ofCoords g (a • (Direction.radonNext g d).vector))
      (Set.range (fun t : ℝ => ofCoords g (t • d.vector))) =
      ‖ofCoords g (a • (Direction.radonNext g d).vector)‖ := by
  have hn := ((isNormal_iff_eq_radonNext g d _).mpr rfl).smul g a 1
  simpa only [one_smul] using hn.infDist g

end FitzhughFarnsworth.Normality.Radon
