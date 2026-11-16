/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Normality.UnitCircle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Arc lengths and the concluding circumference claim

We use regular radial charts on `0 ≤ t ≤ 1`, so no endpoint has an infinite
derivative. Length is the integral of the norm of the actual velocity, with
eight charts for an ordinary p-circle and four charts of each exponent for
the joined circle. The tangent to a positive p-arc is measured in the conjugate
norm in the joined plane. Its speed is `(1+t^p)^(-2/p)`.
-/

@[expose] public section

namespace FitzhughFarnsworth.Normality.Circumference

open Set MeasureTheory

/-- Radial coordinate of the first octant of the p-circle. -/
noncomputable def radius (g : Parameters) (t : ℝ) : ℝ := (1 + t ^ g.p) ^ (-1 / g.p)

/-- The regular arc from `(1,0)` to the positive diagonal. -/
noncomputable def octant (g : Parameters) (t : ℝ) : ℝ × ℝ := (radius g t, t * radius g t)

/-- The positive common factor of the two velocity coordinates. -/
noncomputable def factor (g : Parameters) (t : ℝ) : ℝ :=
  (1 + t ^ g.p) ^ (-1 / g.p - 1)

/-- The actual derivative of `octant` on the nonnegative axis. -/
noncomputable def velocity (g : Parameters) (t : ℝ) : ℝ × ℝ :=
  factor g t • (-(t ^ (g.p - 1)), 1)

theorem base_pos (g : Parameters) {t : ℝ} (ht : 0 ≤ t) : 0 < 1 + t ^ g.p := by
  positivity

theorem radius_pos (g : Parameters) {t : ℝ} (ht : 0 ≤ t) : 0 < radius g t :=
  Real.rpow_pos_of_pos (base_pos g ht) _

theorem factor_pos (g : Parameters) {t : ℝ} (ht : 0 ≤ t) : 0 < factor g t :=
  Real.rpow_pos_of_pos (base_pos g ht) _

theorem radius_eq_factor (g : Parameters) {t : ℝ} (ht : 0 ≤ t) :
    radius g t = (1 + t ^ g.p) * factor g t := by
  rw [radius, factor]
  conv_rhs => lhs; rw [← Real.rpow_one (1 + t ^ g.p)]
  rw [← Real.rpow_add (base_pos g ht)]
  congr 1
  ring

theorem hasDerivAt_radius (g : Parameters) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (radius g) (-(t ^ (g.p - 1)) * factor g t) t := by
  have hd₀ := ((hasDerivAt_id t).rpow_const (p := g.p) (Or.inr g.one_lt_p.le)).const_add 1
  have hd := hd₀.rpow_const (p := -1 / g.p) (Or.inl (by simpa using (base_pos g ht).ne'))
  convert hd using 1
  · rfl
  · dsimp [factor]
    field_simp [(zero_lt_one.trans g.one_lt_p).ne']

theorem hasDerivAt_height (g : Parameters) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => s * radius g s) (factor g t) t := by
  convert (hasDerivAt_id t).mul (hasDerivAt_radius g ht) using 1
  · rfl
  · rw [radius_eq_factor g ht]
    have he : t * t ^ (g.p - 1) = t ^ g.p := by
      conv_lhs => lhs; rw [← Real.rpow_one t]
      rw [← Real.rpow_add' ht (by linarith [g.one_lt_p])]
      congr 1
      ring
    calc
      _ = (1 + t ^ g.p) * factor g t - (t * t ^ (g.p - 1)) * factor g t := by rw [he]; ring
      _ = _ := by simp only [id_eq]; ring

theorem hasDerivAt_octant (g : Parameters) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (octant g) (velocity g t) t := by
  convert (hasDerivAt_radius g ht).prodMk (hasDerivAt_height g ht) using 1
  · rfl
  · ext <;> simp [velocity, mul_comm]

/-- The same velocity is the derivative in the actual h-normed plane. -/
theorem hasDerivAt_normed_octant (g h : Parameters) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => WithLp.toLp (ENNReal.ofReal h.p) (octant g s))
      (WithLp.toLp (ENNReal.ofReal h.p) (velocity g t)) t := by
  let e := (WithLp.prodContinuousLinearEquiv (ENNReal.ofReal h.p) ℝ ℝ ℝ).symm
  exact e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_octant g ht)

theorem octant_on_circle (g : Parameters) {t : ℝ} (ht : 0 ≤ t) :
    g.energy (octant g t) = 1 := by
  have hp := zero_lt_one.trans g.one_lt_p
  have hr := radius_pos g ht
  have he : radius g t ^ g.p = (1 + t ^ g.p)⁻¹ := by
    rw [radius, ← Real.rpow_mul (base_pos g ht).le,
      div_mul_cancel₀ _ hp.ne', Real.rpow_neg_one]
  change |radius g t| ^ g.p + |t * radius g t| ^ g.p = 1
  rw [abs_of_pos hr, abs_of_nonneg (mul_nonneg ht hr.le), Real.mul_rpow ht hr.le, he]
  field_simp [(base_pos g ht).ne']

theorem octant_norm_one (g : Parameters) {t : ℝ} (ht : 0 ≤ t) :
    Radon.length g (octant g t) = 1 := by
  rw [Radon.length, Parameters.norm_eq_energy, octant_on_circle g ht, Real.one_rpow]

/-- The chart covers the entire first octant of the unit circle. -/
theorem exists_octant_parameter (g : Parameters) {x y : ℝ}
    (hy : 0 ≤ y) (hxy : y ≤ x) (hv : g.energy (x, y) = 1) :
    ∃ t ∈ Icc (0 : ℝ) 1, octant g t = (x, y) := by
  have hx : 0 < x := by
    by_contra hn
    have hxe : x = 0 := le_antisymm (le_of_not_gt hn) (hy.trans hxy)
    have hye : y = 0 := le_antisymm (hxe ▸ hxy) hy
    simp [Parameters.energy, hxe, hye, (zero_lt_one.trans g.one_lt_p).ne'] at hv
  let t := y / x
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg hy hx.le, (div_le_one hx).mpr hxy⟩
  have hrep : (x, y) = x • (1, t) := by
    ext <;> simp [t, mul_div_cancel₀ _ hx.ne']
  have hrep' : octant g t = radius g t • (1, t) := by
    ext <;> simp [octant, mul_comm]
  have hunit : Radon.length g (x, y) = 1 := by
    rw [Radon.length, Parameters.norm_eq_energy, hv, Real.one_rpow]
  have ho := octant_norm_one g ht.1
  rw [hrep, Radon.length_smul, abs_of_pos hx] at hunit
  rw [hrep', Radon.length_smul, abs_of_pos (radius_pos g ht.1)] at ho
  have hL : 0 < Radon.length g (1, t) :=
    zero_lt_one.trans_le (by simpa using Radon.abs_fst_le_length g (1, t))
  have hr : radius g t = x := mul_right_cancel₀ hL.ne' (ho.trans hunit.symm)
  exact ⟨t, ht, by rw [hrep', hr, ← hrep]⟩

/-- The chart does not traverse any part of the circle more than once. -/
theorem octant_injOn (g : Parameters) : Set.InjOn (octant g) (Ici 0) := by
  intro s hs t ht h
  have he := congrArg (fun v : ℝ × ℝ => v.2 / v.1) h
  simpa only [octant, mul_div_cancel_right₀ _ (radius_pos g hs).ne',
    mul_div_cancel_right₀ _ (radius_pos g ht).ne'] using he

theorem continuousOn_factor (g : Parameters) : ContinuousOn (factor g) (Icc 0 1) := by
  apply ContinuousOn.rpow_const
  · exact continuousOn_const.add (continuousOn_id.rpow_const
      (fun _ _ => Or.inr (zero_lt_one.trans g.one_lt_p).le))
  · intro t ht
    exact Or.inl (base_pos g ht.1).ne'

theorem continuousOn_velocity (g : Parameters) : ContinuousOn (velocity g) (Icc 0 1) := by
  have hc : ContinuousOn (fun t : ℝ => t ^ (g.p - 1)) (Icc 0 1) :=
    continuousOn_id.rpow_const (fun _ _ => Or.inr (sub_pos.mpr g.one_lt_p).le)
  exact (continuousOn_factor g).smul (hc.neg.prodMk continuousOn_const)

theorem continuous_length (g : Parameters) : Continuous (Radon.length g) := by
  rw [show Radon.length g = fun v : ℝ × ℝ =>
    (|v.1| ^ g.p + |v.2| ^ g.p) ^ (1 / g.p) from funext g.norm_eq_energy]
  fun_prop (discharger := positivity [zero_lt_one.trans g.one_lt_p])

/-- Length of the first p-octant measured in the h-norm, using its actual velocity. -/
noncomputable def octantLength (g h : Parameters) : ℝ :=
  ∫ t : ℝ in 0..1, Radon.length h (velocity g t)

theorem speed_integrable (g h : Parameters) :
    IntervalIntegrable (fun t => Radon.length h (velocity g t)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le zero_le_one, Function.comp_def] using
    (continuous_length h).comp_continuousOn (continuousOn_velocity g)

theorem conjugate_speed (g : Parameters) {t : ℝ} (ht : 0 ≤ t) :
    Radon.length g.conjugate (velocity g t) = (1 + t ^ g.p) ^ (-2 / g.p) := by
  have hp := zero_lt_one.trans g.one_lt_p
  have hpow : (t ^ (g.p - 1)) ^ g.conjugate.p = t ^ g.p := by
    rw [← Real.rpow_mul ht]
    congr 1
    dsimp [Parameters.conjugate]
    field_simp [(sub_pos.mpr g.one_lt_p).ne']
  rw [velocity, Radon.length_smul, abs_of_pos (factor_pos g ht), Radon.length,
    Parameters.norm_eq_energy]
  simp only [Parameters.energy, abs_neg, abs_of_nonneg (Real.rpow_nonneg ht _),
    abs_one, Real.one_rpow, hpow]
  rw [factor, add_comm (t ^ g.p) 1, ← Real.rpow_add (base_pos g ht)]
  congr 1
  have hc := g.conjugate_identity
  simp only [div_eq_mul_inv] at hc ⊢
  linarith

/-- Correct arc-length expression for the p-arc in the joined geometry. -/
theorem octantLength_conjugate (g : Parameters) :
    octantLength g g.conjugate = ∫ t : ℝ in 0..1, (1 + t ^ g.p) ^ (-2 / g.p) := by
  apply intervalIntegral.integral_congr
  intro t ht
  exact conjugate_speed g (by simpa using ht.1)

/-- Circumference of the p-circle, measured in its own p-norm. -/
noncomputable def selfPerimeter (g : Parameters) : ℝ := 8 * octantLength g g

/-- Circumference of the alternating-quadrant circle, measured in the joined norm.
There are four p-octants measured in q and four q-octants measured in p. -/
noncomputable def joinedPerimeter (g : Parameters) : ℝ :=
  4 * (∫ t : ℝ in 0..1, Radon.joinedNorm g g.conjugate (velocity g t)) +
    4 * (∫ t : ℝ in 0..1, Radon.joinedNorm g g.conjugate
      (-(velocity g.conjugate t).1, (velocity g.conjugate t).2))

theorem joinedPerimeter_eq_cross_lengths (g : Parameters) :
    joinedPerimeter g = 4 * octantLength g g.conjugate + 4 * octantLength g.conjugate g := by
  have hfirst : (∫ t : ℝ in 0..1, Radon.joinedNorm g g.conjugate (velocity g t)) =
      octantLength g g.conjugate := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : 0 ≤ t := by simpa using ht.1
    apply Radon.joinedNorm_second
    · change factor g t * -(t ^ (g.p - 1)) ≤ 0
      exact mul_nonpos_of_nonneg_of_nonpos (factor_pos g ht0).le
        (neg_nonpos.mpr (Real.rpow_nonneg ht0 _))
    · change 0 ≤ factor g t * 1
      positivity [factor_pos g ht0]
  have hsecond : (∫ t : ℝ in 0..1, Radon.joinedNorm g g.conjugate
      (-(velocity g.conjugate t).1, (velocity g.conjugate t).2)) =
      octantLength g.conjugate g := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : 0 ≤ t := by simpa using ht.1
    dsimp only
    rw [Radon.joinedNorm_first g g.conjugate (by
      change 0 ≤ -(factor g.conjugate t * -(t ^ (g.conjugate.p - 1)))
      simp only [mul_neg, neg_neg]
      exact mul_nonneg (factor_pos g.conjugate ht0).le (Real.rpow_nonneg ht0 _)) (by
      change 0 ≤ factor g.conjugate t * 1
      positivity [factor_pos g.conjugate ht0])]
    simp [Radon.length, Parameters.norm_eq_energy, Parameters.energy]
  rw [joinedPerimeter, hfirst, hsecond]

theorem joinedPerimeter_formula (g : Parameters) :
    joinedPerimeter g =
      4 * (∫ t : ℝ in 0..1, (1 + t ^ g.p) ^ (-2 / g.p)) +
      4 * (∫ t : ℝ in 0..1, (1 + t ^ g.conjugate.p) ^ (-2 / g.conjugate.p)) := by
  have h := octantLength_conjugate g.conjugate
  simp only [Parameters.conjugate_conjugate] at h
  rw [joinedPerimeter_eq_cross_lengths, octantLength_conjugate, h]

theorem factor_integrable (g : Parameters) : IntervalIntegrable (factor g) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le zero_le_one] using continuousOn_factor g

theorem integral_factor (g : Parameters) : (∫ t : ℝ in 0..1, factor g t) = radius g 1 := by
  simpa only [one_mul, zero_mul, sub_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_height g (by simpa using ht.1)) (factor_integrable g)

theorem radius_one_le_octantLength_self (g : Parameters) : radius g 1 ≤ octantLength g g := by
  rw [← integral_factor]
  apply intervalIntegral.integral_mono_on zero_le_one (factor_integrable g) (speed_integrable g g)
  intro t ht
  have h := Radon.abs_snd_le_length g (velocity g t)
  change |factor g t * 1| ≤ _ at h
  simpa only [mul_one, abs_of_pos (factor_pos g ht.1)] using h

theorem octantLength_conjugate_le_one (g : Parameters) : octantLength g g.conjugate ≤ 1 := by
  have h := intervalIntegral.integral_mono_on zero_le_one (speed_integrable g g.conjugate)
    (intervalIntegrable_const (c := (1 : ℝ))) (fun t ht => ?_)
  · simpa only [octantLength, intervalIntegral.integral_const, sub_zero, one_smul] using h
  rw [conjugate_speed g ht.1]
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (le_add_of_nonneg_right (Real.rpow_nonneg ht.1 _))
    (div_nonpos_of_nonpos_of_nonneg (by norm_num) (zero_lt_one.trans g.one_lt_p).le)

/-- A convenient upper bound for the small conjugate exponent used in the counterexample. -/
theorem octantLength_conjugate_le_euclidean_radius (g : Parameters) (hp : g.p ≤ 4 / 3) :
    octantLength g g.conjugate ≤ radius euclidean 1 := by
  rw [← integral_factor euclidean]
  apply intervalIntegral.integral_mono_on zero_le_one (speed_integrable g g.conjugate)
    (factor_integrable euclidean)
  intro t ht
  have ht2 : t ^ (2 : ℝ) ≤ t ^ g.p :=
    Real.rpow_le_rpow_of_exponent_ge' ht.1 ht.2 (zero_lt_one.trans g.one_lt_p).le (by linarith)
  have hex : -2 / g.p ≤ -1 / (2 : ℝ) - 1 := by
    apply (div_le_iff₀ (zero_lt_one.trans g.one_lt_p)).mpr
    linarith
  rw [conjugate_speed g ht.1]
  change (1 + t ^ g.p) ^ (-2 / g.p) ≤ (1 + t ^ (2 : ℝ)) ^ (-1 / (2 : ℝ) - 1)
  calc
    _ ≤ (1 + t ^ (2 : ℝ)) ^ (-2 / g.p) :=
      Real.rpow_le_rpow_of_nonpos
        (add_pos_of_pos_of_nonneg zero_lt_one (Real.rpow_nonneg ht.1 _)) (by linarith)
        (div_nonpos_of_nonpos_of_nonneg (by norm_num) (zero_lt_one.trans g.one_lt_p).le)
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le
      (le_add_of_nonneg_right (Real.rpow_nonneg ht.1 _)) hex

/-- An exact parameter witnessing the incorrect final circumference claim. -/
def six : Parameters := ⟨6, by norm_num⟩

theorem euclidean_radius_lt_three_quarters : radius euclidean 1 < 3 / 4 := by
  have hp : radius euclidean 1 ^ 2 = (1 / 2 : ℝ) := by
    rw [radius]
    norm_num [euclidean]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  nlinarith [radius_pos euclidean (show (0 : ℝ) ≤ 1 by norm_num)]

theorem seven_eighths_lt_six_radius : 7 / 8 < radius six 1 := by
  have hp : radius six 1 ^ 6 = (1 / 2 : ℝ) := by
    rw [radius]
    norm_num [six]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  by_contra hn
  have h := pow_le_pow_left₀ (radius_pos six (show (0 : ℝ) ≤ 1 by norm_num)).le
    (le_of_not_gt hn) 6
  rw [hp] at h
  norm_num at h

/-- The joined circumference is strictly below seven for `p = 6`, `q = 6/5`. -/
theorem joinedPerimeter_six_lt_seven : joinedPerimeter six < 7 := by
  rw [joinedPerimeter_eq_cross_lengths]
  have h1 := octantLength_conjugate_le_one six
  have h2 := octantLength_conjugate_le_euclidean_radius six.conjugate
    (by norm_num [Parameters.conjugate, six])
  simp only [Parameters.conjugate_conjugate] at h2
  linarith [euclidean_radius_lt_three_quarters]

/-- The original p-circle's self-circumference is strictly above seven at `p = 6`. -/
theorem seven_lt_selfPerimeter_six : 7 < selfPerimeter six := by
  rw [selfPerimeter]
  linarith [radius_one_le_octantLength_self six, seven_eighths_lt_six_radius]

/-- A kernel-checked counterexample to the final paragraph's circumference equality. -/
theorem joinedPerimeter_ne_selfPerimeter : joinedPerimeter six ≠ selfPerimeter six :=
  (joinedPerimeter_six_lt_seven.trans seven_lt_selfPerimeter_six).ne

end FitzhughFarnsworth.Normality.Circumference
