/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Wallis.Moments
public import FitzhughFarnsworth.Wallis.ShiftedHypercube

/-!
# Construction side ratios as measured area moments

Every ordered side ratio is a quotient of weighted moments. Unit initial volume
normalizes the last weighted moment to one. Varying the starting volume shifts
the represented orders, including fractional orders, in the same dimension.
-/

@[expose] public section

namespace FitzhughFarnsworth.Wallis

open Filter Topology

/-- Cancelling the common positive Gamma factor identifies arbitrary moment ratios. -/
theorem weightedMoment_div_eq_gamma {p r s : ℝ} (hp : 0 < p) (hr : -1 < r) (hs : -1 < s) :
    weightedMoment p r / weightedMoment p s =
      Real.Gamma ((r + 1) / p) * Real.Gamma ((s + 2) / p) /
        (Real.Gamma ((r + 2) / p) * Real.Gamma ((s + 1) / p)) := by
  have hc : Real.Gamma (1 + 1 / p) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hr2 : Real.Gamma ((r + 2) / p) ≠ 0 :=
    (Real.Gamma_pos_of_pos (div_pos (by linarith) hp)).ne'
  have hs1 : Real.Gamma ((s + 1) / p) ≠ 0 :=
    (Real.Gamma_pos_of_pos (div_pos (by linarith) hp)).ne'
  have hs2 : Real.Gamma ((s + 2) / p) ≠ 0 :=
    (Real.Gamma_pos_of_pos (div_pos (by linarith) hp)).ne'
  rw [weightedMoment_eq_gamma hp hr, weightedMoment_eq_gamma hp hs]
  field_simp

namespace Hypercube

/-- Earlier coordinates are strictly longer after every positive number of cycles. -/
theorem dimensions_strictAnti (N n : ℕ) : StrictAnti (dimensions N (n + 1)) := by
  rw [← ShiftedHypercube.dimensions_one]
  exact ShiftedHypercube.dimensions_strictAnti N n zero_lt_one

/-- Every ordered pair, including smaller-over-larger ratios, is a quotient of
weighted moments of the same planar N-disk. -/
theorem ratio_tendsto_moments {N : ℕ} (hN : 0 < N) (i j : Fin N) :
    Tendsto (fun n => dimensions N n i / dimensions N n j) atTop
      (𝓝 (weightedMoment N (i : ℕ) / weightedMoment N (j : ℕ))) := by
  rw [weightedMoment_div_eq_gamma (Nat.cast_pos.mpr hN)
    (show (-1 : ℝ) < (i : ℕ) by linarith [(Nat.cast_nonneg (i : ℕ) : (0 : ℝ) ≤ i)])
    (show (-1 : ℝ) < (j : ℕ) by linarith [(Nat.cast_nonneg (j : ℕ) : (0 : ℝ) ≤ j)])]
  exact ratio_tendsto hN i j

/-- Normalizing by the actual last (shortest) coordinate gives one weighted moment. -/
theorem normalized_side_tendsto {N : ℕ} (hN : 0 < N) (i : Fin N) :
    Tendsto (fun n => side N n i / side N n (N - 1)) atTop
      (𝓝 (weightedMoment N (i : ℕ))) := by
  have h := ratio_tendsto_moments hN i ⟨N - 1, by omega⟩
  have hw : weightedMoment N (N - 1 : ℕ) = 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    exact weightedMoment_sub_one (Nat.cast_pos.mpr hN)
  simpa only [dimensions, hw, div_one] using h

/-- All integer-order measured moments are limits of explicit rational rescalings
of the original construction's side ratios. -/
theorem scaled_ratio_tendsto_quarterMoment {N : ℕ} (hN : 0 < N) (m : ℕ) :
    Tendsto (fun n =>
      (side N n (m % N) / side N n (N - 1)) *
        (∏ k ∈ Finset.range (m / N),
          ((m % N : ℕ) + k * (N : ℝ) + 1) / ((m % N : ℕ) + k * (N : ℝ) + 2)) /
        ((m : ℝ) + 2)) atTop (𝓝 (quarterMoment N m)) := by
  have h := ((normalized_side_tendsto hN ⟨m % N, Nat.mod_lt m hN⟩).mul_const
    (∏ k ∈ Finset.range (m / N),
      ((m % N : ℕ) + k * (N : ℝ) + 1) / ((m % N : ℕ) + k * (N : ℝ) + 2))).div_const
        ((m : ℝ) + 2)
  rw [← weightedMoment_nat_eq hN m] at h
  simpa only [weightedMoment, mul_div_cancel_left₀ _ (show (m : ℝ) + 2 ≠ 0 by positivity)] using h

end Hypercube

namespace ShiftedHypercube

/-- Changing the initial cube volume shifts the moment orders represented by
the same cyclic unit-volume attachment process. -/
theorem ratio_tendsto_moments {N : ℕ} (hN : 0 < N) {v : ℝ} (hv : 0 < v) (i j : Fin N) :
    Tendsto (fun n => dimensions N v n i / dimensions N v n j) atTop
      (𝓝 (weightedMoment N (v + (i : ℕ) - 1) /
        weightedMoment N (v + (j : ℕ) - 1))) := by
  have hi : -1 < v + (i : ℕ) - 1 := by
    linarith [(Nat.cast_nonneg (i : ℕ) : (0 : ℝ) ≤ i)]
  have hj : -1 < v + (j : ℕ) - 1 := by
    linarith [(Nat.cast_nonneg (j : ℕ) : (0 : ℝ) ≤ j)]
  rw [weightedMoment_div_eq_gamma (Nat.cast_pos.mpr hN) hi hj,
    sub_add_cancel, sub_add_cancel,
    show v + (j : ℕ) - 1 + 2 = v + (j : ℕ) + 1 by ring,
    show v + (i : ℕ) - 1 + 2 = v + (i : ℕ) + 1 by ring]
  exact ratio_tendsto hN hv i j

/-- Any real order above `-1` can be exposed together with its successor by
choosing initial volume `r + 1`, without changing dimension. -/
theorem adjacent_moment_ratio_tendsto {N : ℕ} (hN : 2 ≤ N) {r : ℝ} (hr : -1 < r) :
    Tendsto (fun n => side N (r + 1) n 0 / side N (r + 1) n 1) atTop
      (𝓝 (weightedMoment N r / weightedMoment N (r + 1))) := by
  have h := ratio_tendsto_moments (by omega : 0 < N)
    (by linarith : 0 < r + 1) ⟨0, by omega⟩ ⟨1, by omega⟩
  simpa only [dimensions, Nat.cast_zero, Nat.cast_one, add_zero, add_sub_cancel_right] using h

end ShiftedHypercube

end FitzhughFarnsworth.Wallis
