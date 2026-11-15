/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Wallis.PCircle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The beta-integral calculation of p-circle area

Equations (10)–(11) of Fitzhugh–Farnsworth (2013). The substitution and integral
evaluation hold for every `p > 0`, including the nonconvex range `0 < p < 1`.
Endpoint derivatives need not be finite: substitution only requires derivatives
on the open interval.
-/

@[expose] public section

namespace FitzhughFarnsworth.Wallis

open MeasureTheory Set

private theorem ofReal_betaIntegral (s t : ℝ) :
    ((∫ x : ℝ in 0..1, x ^ (s - 1) * (1 - x) ^ (t - 1) : ℝ) : ℂ) =
      Complex.betaIntegral s t := by
  rw [← intervalIntegral.integral_ofReal, Complex.betaIntegral]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le zero_le_one] at hx
  dsimp only
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1,
    Complex.ofReal_cpow (sub_nonneg.mpr hx.2)]
  push_cast
  rfl

/-- Equation (10), expressed as a real integral with positive parameters. -/
theorem integral_beta {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (∫ x : ℝ in 0..1, x ^ (s - 1) * (1 - x) ^ (t - 1)) =
      Real.Gamma s * Real.Gamma t / Real.Gamma (s + t) := by
  apply (eq_div_iff (Real.Gamma_pos_of_pos (add_pos hs ht)).ne').mpr
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, ofReal_betaIntegral, Complex.ofReal_mul,
    ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal,
    Complex.ofReal_add, mul_comm]
  exact (Complex.Gamma_mul_Gamma_eq_betaIntegral (by simpa using hs) (by simpa using ht)).symm

/-- The change of variables `t = x^p` in equation (11). -/
theorem pCircle_integral_substitution {p : ℝ} (hp : 0 < p) :
    (∫ x : ℝ in 0..1, (1 - x ^ p) ^ (1 / p)) =
      (1 / p) * ∫ t : ℝ in 0..1, t ^ (1 / p - 1) * (1 - t) ^ (1 / p) := by
  have hq : 0 < 1 / p := one_div_pos.mpr hp
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := 0) (b := 1) (f := fun t : ℝ => t ^ (1 / p))
    (f' := fun t : ℝ => (1 / p) * t ^ (1 / p - 1))
    (g := fun x : ℝ => (1 - x ^ p) ^ (1 / p))
    (Real.continuous_rpow_const hq.le).continuousOn
    (fun t ht => Real.hasDerivAt_rpow_const (Or.inl (by simpa using ht.1.ne')))
    (fun t ht => mul_nonneg hq.le (Real.rpow_nonneg (by simpa using ht.1.le) _))
  simp only [Real.zero_rpow hq.ne', Real.one_rpow] at hsub
  rw [← hsub, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  simp only [Function.comp_apply]
  rw [← Real.rpow_mul ht.1, one_div_mul_cancel hp.ne', Real.rpow_one]
  ring

/-- The quarter-disk integral in (11) equals one half of the Gamma expression `U(p)`. -/
theorem pCircle_integral_eq_gamma {p : ℝ} (hp : 0 < p) :
    (∫ x : ℝ in 0..1, (1 - x ^ p) ^ (1 / p)) = gammaHalfArea p / 2 := by
  have hq : 0 < 1 / p := one_div_pos.mpr hp
  rw [pCircle_integral_substitution hp]
  have hb := integral_beta hq (show 0 < 1 / p + 1 by linarith)
  simp only [add_sub_cancel_right] at hb
  rw [hb, Real.Gamma_add_one hq.ne']
  rw [show 1 / p + (1 / p + 1) = 2 / p + 1 by ring,
    Real.Gamma_add_one (div_pos two_pos hp).ne']
  unfold gammaHalfArea
  field_simp

end FitzhughFarnsworth.Wallis
