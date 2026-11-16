/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Wallis.AreaIntegrals

/-!
# Integrals of arbitrary-order p-circle moments

The order is real and greater than `-1`; the disk exponent can be any positive
real number. These integrals are connected to measured planar moments in
`Wallis.Moments`.
-/

@[expose] public section

namespace FitzhughFarnsworth.Wallis

open MeasureTheory Set

/-- The vertical-slice integral for a first-quadrant area moment. -/
noncomputable def momentIntegral (p r : ℝ) : ℝ :=
  ∫ x : ℝ in 0..1, x ^ r * (1 - x ^ p) ^ (1 / p)

/-- The axis singularity is integrable for every order greater than `-1`. -/
theorem moment_intervalIntegrable {p r : ℝ} (hp : 0 < p) (hr : -1 < r) :
    IntervalIntegrable (fun x : ℝ => x ^ r * (1 - x ^ p) ^ (1 / p)) volume 0 1 := by
  apply (intervalIntegral.intervalIntegrable_rpow' hr).mul_continuousOn
  exact ((Real.continuous_rpow_const (one_div_pos.mpr hp).le).comp
    (continuous_const.sub (Real.continuous_rpow_const hp.le))).continuousOn

/-- Substitution by `x = t^(1/p)` in the weighted area integral. -/
theorem momentIntegral_substitution {p : ℝ} (hp : 0 < p) (r : ℝ) :
    momentIntegral p r = (1 / p) *
      ∫ t : ℝ in 0..1, t ^ ((r + 1) / p - 1) * (1 - t) ^ (1 / p) := by
  have hq : 0 < 1 / p := one_div_pos.mpr hp
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := 0) (b := 1) (f := fun t : ℝ => t ^ (1 / p))
    (f' := fun t : ℝ => (1 / p) * t ^ (1 / p - 1))
    (g := fun x : ℝ => x ^ r * (1 - x ^ p) ^ (1 / p))
    (Real.continuous_rpow_const hq.le).continuousOn
    (fun t ht => Real.hasDerivAt_rpow_const (Or.inl (by simpa using ht.1.ne')))
    (fun t ht => mul_nonneg hq.le (Real.rpow_nonneg (by simpa using ht.1.le) _))
  simp only [Real.zero_rpow hq.ne', Real.one_rpow] at hsub
  rw [momentIntegral, ← hsub, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
  intro t ht
  simp only [Function.comp_apply]
  rw [← Real.rpow_mul ht.1.le, ← Real.rpow_mul ht.1.le,
    one_div_mul_cancel hp.ne', Real.rpow_one]
  calc
    t ^ (1 / p * r) * (1 - t) ^ (1 / p) * (1 / p * t ^ (1 / p - 1)) =
        (1 / p) * (t ^ (1 / p * r) * t ^ (1 / p - 1)) * (1 - t) ^ (1 / p) := by ring
    _ = (1 / p) * (t ^ ((r + 1) / p - 1) * (1 - t) ^ (1 / p)) := by
      rw [← Real.rpow_add ht.1,
        show 1 / p * r + (1 / p - 1) = (r + 1) / p - 1 by ring]
      ring

/-- The beta evaluation of the moment integral, with both parameters positive. -/
theorem momentIntegral_eq_gamma {p r : ℝ} (hp : 0 < p) (hr : -1 < r) :
    momentIntegral p r = (1 / p) *
      (Real.Gamma ((r + 1) / p) * Real.Gamma (1 + 1 / p) /
        Real.Gamma ((r + 1) / p + (1 + 1 / p))) := by
  rw [momentIntegral_substitution hp]
  have hb := integral_beta (div_pos (by linarith : 0 < r + 1) hp)
    (show 0 < 1 + 1 / p by positivity)
  simpa only [add_sub_cancel_left] using congrArg (fun x : ℝ => (1 / p) * x) hb

end FitzhughFarnsworth.Wallis
