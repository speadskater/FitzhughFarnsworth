/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Wallis.Area
public import FitzhughFarnsworth.Wallis.MomentIntegrals
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Measured area moments of the quarter p-disk

These are integrals on a planar region with Lebesgue measure, including real
orders greater than `-1`. Fubini identifies them with the beta integrals.
-/

@[expose] public section

namespace FitzhughFarnsworth.Wallis

open MeasureTheory Set

/-- The first-quadrant part of the planar p-disk. -/
def quarterDisk (p : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 ^ p + z.2 ^ p ≤ 1}

/-- A raw area moment about the y-axis, with planar Lebesgue measure. -/
noncomputable def quarterMoment (p r : ℝ) : ℝ :=
  ∫ z in quarterDisk p, z.1 ^ r

/-- The weighting that identifies moments with normalized construction sides. -/
noncomputable def weightedMoment (p r : ℝ) : ℝ := (r + 2) * quarterMoment p r

/-- Agreement with the original p-disk, with the quadrant restrictions explicit. -/
theorem mem_quarterDisk_iff (p : ℝ) (z : ℝ × ℝ) :
    z ∈ quarterDisk p ↔ ![z.1, z.2] ∈ unitDisk p ∧ 0 ≤ z.1 ∧ 0 ≤ z.2 := by
  constructor
  · rintro ⟨hx, hy, h⟩
    exact ⟨by simpa [unitDisk, abs_of_nonneg hx, abs_of_nonneg hy] using h, hx, hy⟩
  · rintro ⟨h, hx, hy⟩
    exact ⟨hx, hy, by simpa [unitDisk, abs_of_nonneg hx, abs_of_nonneg hy] using h⟩

theorem quarterDisk_subset_unitSquare {p : ℝ} (hp : 0 < p) :
    quarterDisk p ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  intro z hz
  rcases hz with ⟨hx, hy, h⟩
  have hxpow : z.1 ^ p ≤ (1 : ℝ) ^ p := by
    rw [Real.one_rpow]
    linarith [Real.rpow_nonneg hy p]
  have hypow : z.2 ^ p ≤ (1 : ℝ) ^ p := by
    rw [Real.one_rpow]
    linarith [Real.rpow_nonneg hx p]
  exact ⟨⟨hx, (Real.rpow_le_rpow_iff hx zero_le_one hp).mp hxpow⟩,
    hy, (Real.rpow_le_rpow_iff hy zero_le_one hp).mp hypow⟩

/-- Exact vertical sections, including the boundary axes and curve. -/
theorem quarterDisk_eq_region {p : ℝ} (hp : 0 < p) :
    quarterDisk p = {z : ℝ × ℝ | z.1 ∈ Icc 0 1 ∧ z.2 ∈ Icc 0 (pCircleProfile p z.1)} := by
  have hroot (x : ℝ) (hx : x ∈ Icc 0 1) :
      pCircleProfile p x ^ p = 1 - x ^ p := by
    have hpow : x ^ p ≤ 1 := by
      simpa using Real.rpow_le_rpow hx.1 hx.2 hp.le
    rw [pCircleProfile, abs_of_nonneg hx.1, ← Real.rpow_mul (sub_nonneg.mpr hpow),
      one_div_mul_cancel hp.ne', Real.rpow_one]
  ext z
  constructor
  · intro hz
    have hx := (quarterDisk_subset_unitSquare hp hz).1
    refine ⟨hx, hz.2.1, ?_⟩
    apply (Real.rpow_le_rpow_iff hz.2.1
      (pCircleProfile_nonneg hp ⟨by linarith [hx.1], hx.2⟩) hp).mp
    rw [hroot z.1 hx]
    linarith [hz.2.2]
  · rintro ⟨hx, hy⟩
    refine ⟨hx.1, hy.1, ?_⟩
    have h := Real.rpow_le_rpow hy.1 hy.2 hp.le
    rw [hroot z.1 hx] at h
    linarith

theorem measurableSet_quarterDisk {p : ℝ} (hp : 0 < p) : MeasurableSet (quarterDisk p) := by
  rw [quarterDisk_eq_region hp]
  exact measurableSet_region_between_cc measurable_const
    (continuous_pCircleProfile hp).measurable measurableSet_Icc

/-- Integrability of the actual planar moment, including negative orders above `-1`. -/
theorem integrableOn_quarterMoment {p r : ℝ} (hp : 0 < p) (hr : -1 < r) :
    IntegrableOn (fun z : ℝ × ℝ => z.1 ^ r) (quarterDisk p) := by
  have hx : IntegrableOn (fun x : ℝ => x ^ r) (Icc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' hr)
  have hbox : IntegrableOn (fun z : ℝ × ℝ => z.1 ^ r)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact hx.comp_fst (volume.restrict (Icc (0 : ℝ) 1))
  exact hbox.mono_set (quarterDisk_subset_unitSquare hp)

/-- Fubini's formula for the measured first-quadrant moment. -/
theorem quarterMoment_eq_integral {p r : ℝ} (hp : 0 < p) (hr : -1 < r) :
    quarterMoment p r = momentIntegral p r := by
  have hm := measurableSet_quarterDisk hp
  have hi := (integrableOn_quarterMoment hp hr).integrable_indicator hm
  rw [quarterMoment, ← integral_indicator hm, Measure.volume_eq_prod,
    integral_prod _ hi]
  have hsection (x : ℝ) :
      (∫ y : ℝ, (quarterDisk p).indicator (fun z : ℝ × ℝ => z.1 ^ r) (x, y)) =
        (Icc (0 : ℝ) 1).indicator (fun x => x ^ r * pCircleProfile p x) x := by
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · have heq : (fun y : ℝ => (quarterDisk p).indicator
          (fun z : ℝ × ℝ => z.1 ^ r) (x, y)) =
          (Icc 0 (pCircleProfile p x)).indicator (fun _ : ℝ => x ^ r) := by
        ext y
        simp only [quarterDisk_eq_region hp, Set.indicator, mem_ofPred_eq, hx, true_and]
      rw [heq, integral_indicator measurableSet_Icc, setIntegral_const,
        Real.volume_real_Icc_of_le (pCircleProfile_nonneg hp ⟨by linarith [hx.1], hx.2⟩),
        Set.indicator_of_mem hx]
      simp [smul_eq_mul, mul_comm]
    · have heq : (fun y : ℝ => (quarterDisk p).indicator
          (fun z : ℝ × ℝ => z.1 ^ r) (x, y)) = 0 := by
        ext y
        simp only [quarterDisk_eq_region hp, Set.indicator, mem_ofPred_eq, hx, false_and,
          ite_false, Pi.zero_apply]
      rw [heq, Set.indicator_of_notMem hx]
      simp
  simp_rw [hsection]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le zero_le_one] at hx
  simp [pCircleProfile, abs_of_nonneg hx.1]

/-- Gamma evaluation of the actual area moment. -/
theorem quarterMoment_eq_gamma {p r : ℝ} (hp : 0 < p) (hr : -1 < r) :
    quarterMoment p r = (1 / p) *
      (Real.Gamma ((r + 1) / p) * Real.Gamma (1 + 1 / p) /
        Real.Gamma ((r + 1) / p + (1 + 1 / p))) := by
  rw [quarterMoment_eq_integral hp hr, momentIntegral_eq_gamma hp hr]

theorem quarterMoment_pos {p r : ℝ} (hp : 0 < p) (hr : -1 < r) :
    0 < quarterMoment p r := by
  rw [quarterMoment_eq_gamma hp hr]
  have ha : 0 < (r + 1) / p := div_pos (by linarith) hp
  have hb : 0 < 1 + 1 / p := by positivity
  exact mul_pos (one_div_pos.mpr hp)
    (div_pos (mul_pos (Real.Gamma_pos_of_pos ha) (Real.Gamma_pos_of_pos hb))
      (Real.Gamma_pos_of_pos (add_pos ha hb)))

theorem weightedMoment_pos {p r : ℝ} (hp : 0 < p) (hr : -1 < r) :
    0 < weightedMoment p r :=
  mul_pos (by linarith) (quarterMoment_pos hp hr)

/-- The Gamma quotient that also occurs in the construction's side limits. -/
theorem weightedMoment_eq_gamma {p r : ℝ} (hp : 0 < p) (hr : -1 < r) :
    weightedMoment p r =
      Real.Gamma ((r + 1) / p) * Real.Gamma (1 + 1 / p) /
        Real.Gamma ((r + 2) / p) := by
  have hr2 : r + 2 ≠ 0 := ne_of_gt (by linarith)
  have hg : Real.Gamma ((r + 2) / p) ≠ 0 :=
    (Real.Gamma_pos_of_pos (div_pos (by linarith) hp)).ne'
  rw [weightedMoment, quarterMoment_eq_gamma hp hr,
    show (r + 1) / p + (1 + 1 / p) = (r + 2) / p + 1 by ring,
    Real.Gamma_add_one (div_pos (by linarith : 0 < r + 2) hp).ne']
  field_simp [hp.ne', hr2, hg]

/-- The original area result is the zeroth weighted moment. -/
theorem weightedMoment_zero {p : ℝ} (hp : 0 < p) :
    weightedMoment p 0 = upperHalfArea p := by
  rw [weightedMoment, quarterMoment_eq_integral hp (by norm_num)]
  simp only [momentIntegral, Real.rpow_zero, one_mul, zero_add]
  rw [pCircle_integral_eq_gamma hp, upperHalfArea_eq_gamma_of_pos hp]
  ring

/-- The last coordinate in the unit-cube construction supplies normalization. -/
theorem weightedMoment_sub_one {p : ℝ} (hp : 0 < p) :
    weightedMoment p (p - 1) = 1 := by
  rw [weightedMoment_eq_gamma hp (by linarith)]
  rw [show (p - 1 + 1) / p = 1 by field_simp; ring,
    show (p - 1 + 2) / p = 1 + 1 / p by field_simp; ring]
  rw [Real.Gamma_one, one_mul,
    div_self (Real.Gamma_pos_of_pos (show 0 < 1 + 1 / p by positivity)).ne']

/-- Increasing the moment order by the disk exponent multiplies its weighted value
by a rational function of the original order. -/
theorem weightedMoment_add_exponent {p r : ℝ} (hp : 0 < p) (hr : -1 < r) :
    weightedMoment p (r + p) = (r + 1) / (r + 2) * weightedMoment p r := by
  have ha : 0 < (r + 1) / p := div_pos (by linarith) hp
  have hb : 0 < (r + 2) / p := div_pos (by linarith) hp
  rw [weightedMoment_eq_gamma hp (by linarith), weightedMoment_eq_gamma hp hr,
    show (r + p + 1) / p = (r + 1) / p + 1 by field_simp; ring,
    show (r + p + 2) / p = (r + 2) / p + 1 by field_simp; ring,
    Real.Gamma_add_one ha.ne', Real.Gamma_add_one hb.ne']
  field_simp [hp.ne', (show r + 2 ≠ 0 by linarith), (Real.Gamma_pos_of_pos hb).ne']

/-- The corresponding recurrence for the unweighted measured moment. -/
theorem quarterMoment_add_exponent {p r : ℝ} (hp : 0 < p) (hr : -1 < r) :
    quarterMoment p (r + p) = (r + 1) / (r + p + 2) * quarterMoment p r := by
  have h := weightedMoment_add_exponent hp hr
  unfold weightedMoment at h
  have hcancel : (r + 1) / (r + 2) * ((r + 2) * quarterMoment p r) =
      (r + 1) * quarterMoment p r := by
    field_simp [show r + 2 ≠ 0 by linarith]
  rw [hcancel] at h
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (show r + p + 2 ≠ 0 by linarith)).mpr
  simpa only [mul_comm] using h

/-- An explicit finite product generates each entire progression of moment orders. -/
theorem weightedMoment_add_nat_mul {p r : ℝ} (hp : 0 < p) (hr : -1 < r) (q : ℕ) :
    weightedMoment p (r + q * p) = weightedMoment p r *
      ∏ k ∈ Finset.range q, (r + k * p + 1) / (r + k * p + 2) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have horder : -1 < r + q * p := by
      linarith [mul_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q) hp.le]
    rw [show r + (q + 1 : ℕ) * p = (r + q * p) + p by push_cast; ring,
      weightedMoment_add_exponent hp horder, ih, Finset.prod_range_succ]
    ring

/-- Every nonnegative integer order is recovered from one of the first `N` orders. -/
theorem weightedMoment_nat_eq {N : ℕ} (hN : 0 < N) (m : ℕ) :
    weightedMoment N m = weightedMoment N (m % N : ℕ) *
      ∏ k ∈ Finset.range (m / N),
        ((m % N : ℕ) + k * (N : ℝ) + 1) / ((m % N : ℕ) + k * (N : ℝ) + 2) := by
  have h := weightedMoment_add_nat_mul (Nat.cast_pos.mpr hN)
    (show (-1 : ℝ) < (m % N : ℕ) by
      exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _)) (m / N)
  have hm : (m : ℝ) = (m % N : ℕ) + (m / N : ℕ) * (N : ℝ) := by
    exact_mod_cast (show m = m % N + (m / N) * N by
      simpa only [Nat.mul_comm] using (Nat.mod_add_div m N).symm)
  simpa only [← hm] using h

end FitzhughFarnsworth.Wallis
