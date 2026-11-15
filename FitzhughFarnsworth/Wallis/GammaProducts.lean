/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Products of two linear factors

The two-factor case of equations (8)–(9) in Fitzhugh–Farnsworth (2013), with
zero-based indexing and positive shifts. The limit is derived from mathlib's
Euler limit for `Real.Gamma`; the balance condition cancels the powers of `n`.
Without balance, the sign of the difference of the sums determines whether
the product tends to zero or positive infinity.
-/

@[expose] public section

namespace FitzhughFarnsworth.Wallis

open Filter Topology

private theorem linear_prod_ne_zero {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (∏ k ∈ Finset.range n, (x + k)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k _
  exact (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg k)).ne'

private theorem gammaSeq_balance {x y z w : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hw : 0 < w)
    (hbalance : x + y = z + w) {n : ℕ} (hn : 0 < n) :
    Real.GammaSeq z n * Real.GammaSeq w n / (Real.GammaSeq x n * Real.GammaSeq y n) =
      ∏ k ∈ Finset.range (n + 1), ((x + k) * (y + k)) / ((z + k) * (w + k)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hscale : ((n : ℝ) ^ z * n.factorial) * ((n : ℝ) ^ w * n.factorial) =
      ((n : ℝ) ^ x * n.factorial) * ((n : ℝ) ^ y * n.factorial) := by
    calc
      _ = (n : ℝ) ^ (z + w) * (n.factorial : ℝ) ^ 2 := by
        rw [Real.rpow_add hn']
        ring
      _ = (n : ℝ) ^ (x + y) * (n.factorial : ℝ) ^ 2 := by rw [hbalance]
      _ = _ := by rw [Real.rpow_add hn']; ring
  have hscale_ne : ((n : ℝ) ^ x * n.factorial) *
      ((n : ℝ) ^ y * n.factorial) ≠ 0 := by positivity
  unfold Real.GammaSeq
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    div_mul_div_comm, div_mul_div_comm, hscale]
  field_simp [linear_prod_ne_zero hx, linear_prod_ne_zero hy,
    linear_prod_ne_zero hz, linear_prod_ne_zero hw, hscale_ne]

/-- The two-factor balanced Gamma product, with all factors strictly positive. -/
theorem tendsto_balanced_prod {x y z w : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hw : 0 < w)
    (hbalance : x + y = z + w) :
    Tendsto (fun n : ℕ =>
      ∏ k ∈ Finset.range n, ((x + k) * (y + k)) / ((z + k) * (w + k)))
      atTop (𝓝 (Real.Gamma z * Real.Gamma w / (Real.Gamma x * Real.Gamma y))) := by
  have hlim := ((Real.GammaSeq_tendsto_Gamma z).mul (Real.GammaSeq_tendsto_Gamma w)).div
    ((Real.GammaSeq_tendsto_Gamma x).mul (Real.GammaSeq_tendsto_Gamma y))
    (mul_ne_zero (Real.Gamma_pos_of_pos hx).ne' (Real.Gamma_pos_of_pos hy).ne')
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact gammaSeq_balance hx hy hz hw hbalance hn

/-- Separate the power growth from the Gamma approximation at a positive index. -/
theorem linear_prod_eq_rpow_mul_gammaSeq {x y z w : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hw : 0 < w)
    {n : ℕ} (hn : 0 < n) :
    (∏ k ∈ Finset.range (n + 1), ((x + k) * (y + k)) / ((z + k) * (w + k))) =
      (n : ℝ) ^ (x + y - z - w) *
        (Real.GammaSeq z n * Real.GammaSeq w n /
          (Real.GammaSeq x n * Real.GammaSeq y n)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [Real.rpow_sub hn', Real.rpow_sub hn', Real.rpow_add hn',
    Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  unfold Real.GammaSeq
  field_simp [linear_prod_ne_zero hx, linear_prod_ne_zero hy,
    linear_prod_ne_zero hz, linear_prod_ne_zero hw]

/-- If the numerator shifts have smaller sum, the partial products tend to zero. -/
theorem tendsto_linear_prod_zero {x y z w : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hw : 0 < w)
    (hsum : x + y < z + w) :
    Tendsto (fun n : ℕ =>
      ∏ k ∈ Finset.range n, ((x + k) * (y + k)) / ((z + k) * (w + k)))
      atTop (𝓝 0) := by
  have hlim := ((Real.GammaSeq_tendsto_Gamma z).mul (Real.GammaSeq_tendsto_Gamma w)).div
    ((Real.GammaSeq_tendsto_Gamma x).mul (Real.GammaSeq_tendsto_Gamma y))
    (mul_ne_zero (Real.Gamma_pos_of_pos hx).ne' (Real.Gamma_pos_of_pos hy).ne')
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (x + y - z - w)) atTop (𝓝 0) := by
    have he : x + y - z - w = -(z + w - (x + y)) := by ring
    rw [he]
    exact (tendsto_rpow_neg_atTop (sub_pos.mpr hsum)).comp tendsto_natCast_atTop_atTop
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hmul := hpow.mul hlim
  simp only [zero_mul] at hmul
  apply hmul.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (linear_prod_eq_rpow_mul_gammaSeq hx hy hz hw hn).symm

/-- If the numerator shifts have larger sum, the partial products tend to positive infinity. -/
theorem tendsto_linear_prod_atTop {x y z w : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hw : 0 < w)
    (hsum : z + w < x + y) :
    Tendsto (fun n : ℕ =>
      ∏ k ∈ Finset.range n, ((x + k) * (y + k)) / ((z + k) * (w + k)))
      atTop atTop := by
  have hlim := ((Real.GammaSeq_tendsto_Gamma z).mul (Real.GammaSeq_tendsto_Gamma w)).div
    ((Real.GammaSeq_tendsto_Gamma x).mul (Real.GammaSeq_tendsto_Gamma y))
    (mul_ne_zero (Real.Gamma_pos_of_pos hx).ne' (Real.Gamma_pos_of_pos hy).ne')
  have hpos : 0 < Real.Gamma z * Real.Gamma w / (Real.Gamma x * Real.Gamma y) :=
    div_pos (mul_pos (Real.Gamma_pos_of_pos hz) (Real.Gamma_pos_of_pos hw))
      (mul_pos (Real.Gamma_pos_of_pos hx) (Real.Gamma_pos_of_pos hy))
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (x + y - z - w)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply (hpow.atTop_mul_pos hpos hlim).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (linear_prod_eq_rpow_mul_gammaSeq hx hy hz hw hn).symm

end FitzhughFarnsworth.Wallis
