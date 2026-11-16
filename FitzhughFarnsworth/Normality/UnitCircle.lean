/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Normality.RadonNormality

/-!
# Unit-circle contact points and the axis joins

The ordinary p-circle has explicit normalized contact points whose tangent
directions are the given lines. The joined curve has the stated quadrant
equations and differentiable graph joins on the axes. These are first derivative
claims; arbitrary higher smoothness is not asserted for real exponents.
-/

@[expose] public section

namespace FitzhughFarnsworth.Normality

namespace Parameters

/-- An explicit unit-circle point on the specified line. -/
noncomputable def contact (g : Parameters) (d : Direction) : ℝ × ℝ :=
  ‖WithLp.toLp (ENNReal.ofReal g.p) d.vector‖⁻¹ • d.vector

theorem norm_contact (g : Parameters) (d : Direction) :
    ‖WithLp.toLp (ENNReal.ofReal g.p) (g.contact d)‖ = 1 := by
  change ‖(‖WithLp.toLp (ENNReal.ofReal g.p) d.vector‖⁻¹ : ℝ) •
    WithLp.toLp (ENNReal.ofReal g.p) d.vector‖ = 1
  apply norm_smul_inv_norm
  intro h
  exact d.vector_ne_zero (congrArg WithLp.ofLp h)

theorem energy_contact (g : Parameters) (d : Direction) : g.energy (g.contact d) = 1 := by
  have h := g.norm_contact d
  rw [g.norm_eq_energy] at h
  apply (Real.rpow_left_inj (by dsimp [energy]; positivity) zero_le_one
    (one_div_pos.mpr (zero_lt_one.trans g.one_lt_p)).ne').mp
  simpa only [Real.one_rpow] using h

/-- Section 2's tangency characterization at an actual point of the unit circle. -/
theorem contact_tangent (g : Parameters) (d : Direction) :
    HasDerivAt (fun t : ℝ => g.energy (g.contact (Direction.next g d) + t • d.vector)) 0 0 := by
  have hn := Parameters.IsNormal.smul g
    ((Direction.isNormal_iff_eq_next g d _).mpr rfl)
    ‖WithLp.toLp (ENNReal.ofReal g.p) (Direction.next g d).vector‖⁻¹ 1
  simp only [one_smul] at hn
  have he := (g.isNormal_iff _ _).mp hn
  have hd := g.hasDerivAt_energy_line (g.contact (Direction.next g d)) d.vector
  simpa only [contact, he, mul_zero] using hd

end Parameters

namespace Radon

/-- The upper graph of a p-circle, also used as a horizontal graph after swapping coordinates. -/
noncomputable def arc (g : Parameters) (x : ℝ) : ℝ := (1 - |x| ^ g.p) ^ (1 / g.p)

@[simp] theorem arc_zero (g : Parameters) : arc g 0 = 1 := by
  simp [arc, (zero_lt_one.trans g.one_lt_p).ne']

@[simp] theorem arc_one (g : Parameters) : arc g 1 = 0 := by
  simp [arc, (zero_lt_one.trans g.one_lt_p).ne']

theorem arc_nonneg (g : Parameters) {x : ℝ} (hx : |x| ≤ 1) : 0 ≤ arc g x := by
  apply Real.rpow_nonneg
  have h := Real.rpow_le_rpow (abs_nonneg x) hx (zero_lt_one.trans g.one_lt_p).le
  simpa only [Real.one_rpow, sub_nonneg] using h

theorem arc_energy (g : Parameters) {x : ℝ} (hx : |x| ≤ 1) :
    g.energy (x, arc g x) = 1 := by
  have hp := zero_lt_one.trans g.one_lt_p
  have hb : 0 ≤ 1 - |x| ^ g.p := by
    have h := Real.rpow_le_rpow (abs_nonneg x) hx hp.le
    simpa only [Real.one_rpow, sub_nonneg] using h
  change |x| ^ g.p + |arc g x| ^ g.p = 1
  rw [abs_of_nonneg (arc_nonneg g hx), arc]
  rw [← Real.rpow_mul hb, one_div_mul_cancel hp.ne', Real.rpow_one]
  ring

theorem hasDerivAt_arc_zero (g : Parameters) : HasDerivAt (arc g) 0 0 := by
  have h := ((hasDerivAt_abs_rpow 0 g.one_lt_p).const_sub 1).rpow_const
    (p := 1 / g.p) (Or.inl (by simp [((zero_lt_one.trans g.one_lt_p).ne')]))
  change HasDerivAt (fun x => (1 - |x| ^ g.p) ^ (1 / g.p)) 0 0
  simpa [(zero_lt_one.trans g.one_lt_p).ne'] using h

/-- The upper joined arc; its endpoint at the y-axis is shared by both pieces. -/
noncomputable def upperArc (g h : Parameters) (x : ℝ) : ℝ :=
  if 0 ≤ x then arc g x else arc h x

@[simp] theorem upperArc_zero (g h : Parameters) : upperArc g h 0 = 1 := by
  simp [upperArc]

/-- The actual joined unit circle, not merely its filled disk. -/
theorem joinedNorm_eq_one_iff (g h : Parameters) (v : ℝ × ℝ) :
    joinedNorm g h v = 1 ↔
      if 0 ≤ v.1 * v.2 then g.energy v = 1 else h.energy v = 1 := by
  have he (k : Parameters) : length k v = 1 ↔ k.energy v = 1 := by
    rw [length, k.norm_eq_energy]
    simpa only [Real.one_rpow] using Real.rpow_left_inj
      (by dsimp [Parameters.energy]; positivity : 0 ≤ k.energy v) zero_le_one
      (one_div_pos.mpr (zero_lt_one.trans k.one_lt_p)).ne'
  rw [joinedNorm_quadrant]
  split <;> exact he _

/-- The joined graph really parametrizes the upper half of the constructed unit circle. -/
theorem upperArc_on_circle (g h : Parameters) {x : ℝ} (hx : |x| ≤ 1) :
    joinedNorm g h (x, upperArc g h x) = 1 := by
  by_cases hx0 : 0 ≤ x
  · rw [upperArc, ite_eq_left hx0, joinedNorm_first g h hx0 (arc_nonneg g hx)]
    rw [length, Parameters.norm_eq_energy, arc_energy g hx, Real.one_rpow]
  · rw [upperArc, ite_eq_right hx0,
      joinedNorm_second g h (le_of_not_ge hx0) (arc_nonneg h hx)]
    rw [length, Parameters.norm_eq_energy, arc_energy h hx, Real.one_rpow]

/-- The two graph pieces have the same tangent at the join on the positive y-axis. -/
theorem hasDerivAt_upperArc_zero (g h : Parameters) : HasDerivAt (upperArc g h) 0 0 := by
  have hr : HasDerivWithinAt (upperArc g h) 0 (Set.Ici 0) 0 :=
    (hasDerivAt_arc_zero g).hasDerivWithinAt.congr
      (fun x hx => by simp [upperArc, show 0 ≤ x from hx]) (by simp)
  have hl : HasDerivWithinAt (upperArc g h) 0 (Set.Iic 0) 0 := by
    apply (hasDerivAt_arc_zero h).hasDerivWithinAt.congr
    · intro x hx
      rcases hx.eq_or_lt with rfl | hx
      · simp
      · simp [upperArc, not_le.mpr hx]
    · simp
  have hu := hl.union hr
  rw [Set.Iic_union_Ici] at hu
  exact hasDerivWithinAt_univ.mp hu

/-- Swapping coordinates preserves the joined curve, supplying the horizontal-axis charts. -/
theorem joinedNorm_swap (g h : Parameters) (x y : ℝ) :
    joinedNorm g h (y, x) = joinedNorm g h (x, y) := by
  simp only [joinedNorm_quadrant, mul_comm]
  split <;> simp [length, Parameters.norm_eq_energy, Parameters.energy, add_comm]

theorem rightArc_on_circle (g h : Parameters) {y : ℝ} (hy : |y| ≤ 1) :
    joinedNorm g h (upperArc g h y, y) = 1 := by
  rw [joinedNorm_swap]
  exact upperArc_on_circle g h hy

/-- Theorem 4.1's necessity as equality with the explicit q-circle graph. -/
theorem quadrant_unique_graph (g : Parameters) {f f' : ℝ → ℝ}
    (hc : ContinuousOn f (Set.Icc (-1) 0)) (h0 : f 0 = 1)
    (hy : ∀ x ∈ Set.Ioo (-1) 0, 0 < f x)
    (ht : ∀ x ∈ Set.Ioo (-1) 0, 0 < f' x)
    (hd : ∀ x ∈ Set.Ioo (-1) 0, HasDerivAt f (f' x) x)
    (hn : ∀ x ∈ Set.Ioo (-1) 0, g.IsNormal (1, f' x) (x, f x)) :
    Set.EqOn f (arc g.conjugate) (Set.Icc (-1) 0) := by
  intro x hx
  have hfx : 0 ≤ f x := ContinuousWithinAt.closure_le
    (by rwa [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 0)]) continuousWithinAt_const
    ((hc x hx).mono Set.Ioo_subset_Icc_self) (fun z hz => (hy z hz).le)
  have hxabs : |x| ≤ 1 := abs_le.mpr ⟨hx.1, hx.2.trans (by norm_num)⟩
  have he := g.quadrant_unique hc h0 hy ht hd hn x hx
  have ha := arc_energy g.conjugate hxabs
  change |x| ^ g.conjugate.p + |arc g.conjugate x| ^ g.conjugate.p = 1 at ha
  rw [abs_of_nonpos hx.2, abs_of_nonneg (arc_nonneg g.conjugate hxabs)] at ha
  apply (Real.rpow_left_inj hfx (arc_nonneg g.conjugate hxabs)
    (zero_lt_one.trans g.conjugate.one_lt_p).ne').mp
  linarith

end Radon

end FitzhughFarnsworth.Normality
