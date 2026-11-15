/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Wallis.AreaIntegrals
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Area of every positive-exponent p-disk

Equations (11)–(12) of Fitzhugh–Farnsworth (2013), now for all `p > 0`.
Vertical sections identify the closed disk and its upper half as measurable
regions between continuous graphs. Fubini gives the area integral, which the
beta calculation evaluates. Convexity is not required.
-/

@[expose] public section

namespace FitzhughFarnsworth.Wallis

open MeasureTheory Set Filter Topology

/-- Height of the upper p-circle above a horizontal coordinate in `[-1,1]`. -/
noncomputable def pCircleProfile (p x : ℝ) : ℝ := (1 - |x| ^ p) ^ (1 / p)

theorem continuous_pCircleProfile {p : ℝ} (hp : 0 < p) : Continuous (pCircleProfile p) :=
  (Real.continuous_rpow_const (one_div_pos.mpr hp).le).comp
    (continuous_const.sub ((Real.continuous_rpow_const hp.le).comp continuous_abs))

theorem pCircleProfile_nonneg {p x : ℝ} (hp : 0 < p) (hx : x ∈ Icc (-1) 1) :
    0 ≤ pCircleProfile p x := by
  have hpow : |x| ^ p ≤ 1 := by
    simpa using Real.rpow_le_rpow (abs_nonneg x) (abs_le.mpr hx) hp.le
  exact Real.rpow_nonneg (sub_nonneg.mpr hpow) _

private theorem disk_inequality_iff {p : ℝ} (hp : 0 < p) (x y : ℝ) :
    |x| ^ p + |y| ^ p ≤ 1 ↔ x ∈ Icc (-1) 1 ∧
      y ∈ Icc (-pCircleProfile p x) (pCircleProfile p x) := by
  have hroot (hx : x ∈ Icc (-1) 1) :
      pCircleProfile p x ^ p = 1 - |x| ^ p := by
    have hxpow : |x| ^ p ≤ 1 := by
      simpa using Real.rpow_le_rpow (abs_nonneg x) (abs_le.mpr hx) hp.le
    rw [pCircleProfile, ← Real.rpow_mul (sub_nonneg.mpr hxpow),
      one_div_mul_cancel hp.ne', Real.rpow_one]
  constructor
  · intro h
    have hxpow : |x| ^ p ≤ (1 : ℝ) ^ p := by
      rw [Real.one_rpow]
      linarith [Real.rpow_nonneg (abs_nonneg y) p]
    have hx : x ∈ Icc (-1) 1 :=
      abs_le.mp ((Real.rpow_le_rpow_iff (abs_nonneg x) zero_le_one hp).mp hxpow)
    refine ⟨hx, abs_le.mp ?_⟩
    apply (Real.rpow_le_rpow_iff (abs_nonneg y) (pCircleProfile_nonneg hp hx) hp).mp
    rw [hroot hx]
    linarith
  · rintro ⟨hx, hy⟩
    have h := Real.rpow_le_rpow (abs_nonneg y) (abs_le.mpr hy) hp.le
    rw [hroot hx] at h
    linarith

private theorem upper_inequality_iff {p : ℝ} (hp : 0 < p) (x y : ℝ) :
    (|x| ^ p + |y| ^ p ≤ 1 ∧ 0 ≤ y) ↔
      x ∈ Icc (-1) 1 ∧ y ∈ Icc 0 (pCircleProfile p x) := by
  rw [disk_inequality_iff hp]
  constructor
  · rintro ⟨⟨hx, _, hy⟩, h0⟩
    exact ⟨hx, h0, hy⟩
  · rintro ⟨hx, h0, hy⟩
    exact ⟨⟨hx, by linarith [pCircleProfile_nonneg hp hx], hy⟩, h0⟩

private theorem volume_between_closed (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (a b : ℝ) (hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    volume {z : ℝ × ℝ | z.1 ∈ Icc a b ∧ z.2 ∈ Icc (f z.1) (g z.1)} =
      ENNReal.ofReal (∫ x in Icc a b, g x - f x) := by
  classical
  change (volume.prod volume) _ = _
  rw [Measure.prod_apply (measurableSet_region_between_cc hf.measurable hg.measurable
    measurableSet_Icc)]
  have hsec (x : ℝ) :
      volume (Prod.mk x ⁻¹' {z : ℝ × ℝ | z.1 ∈ Icc a b ∧ z.2 ∈ Icc (f z.1) (g z.1)}) =
        (Icc a b).indicator (fun x => ENNReal.ofReal (g x - f x)) x := by
    by_cases hx : x ∈ Icc a b
    · rw [Set.indicator_of_mem hx]
      have hpre : Prod.mk x ⁻¹' {z : ℝ × ℝ | z.1 ∈ Icc a b ∧
          z.2 ∈ Icc (f z.1) (g z.1)} = Icc (f x) (g x) := by
        ext y
        exact and_iff_right hx
      rw [hpre, Real.volume_Icc]
    · rw [Set.indicator_of_notMem hx]
      have hpre : Prod.mk x ⁻¹' {z : ℝ × ℝ | z.1 ∈ Icc a b ∧
          z.2 ∈ Icc (f z.1) (g z.1)} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro y hy
        exact hx hy.1
      rw [hpre, measure_empty]
  simp_rw [hsec]
  rw [lintegral_indicator measurableSet_Icc]
  symm
  apply ofReal_integral_eq_lintegral_ofReal (hg.sub hf).integrableOn_Icc
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact sub_nonneg.mpr (hfg x hx)

private theorem integral_profile {p : ℝ} (hp : 0 < p) :
    (∫ x in Icc (-1 : ℝ) 1, pCircleProfile p x) =
      2 * ∫ x : ℝ in 0..1, (1 - x ^ p) ^ (1 / p) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hc := continuous_pCircleProfile hp
  have hneg : (∫ x : ℝ in (-1)..0, pCircleProfile p x) =
      ∫ x : ℝ in 0..1, pCircleProfile p x := by
    simpa [pCircleProfile] using
      (intervalIntegral.integral_comp_neg (pCircleProfile p) (a := 0) (b := 1)).symm
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (-1) 0) (hc.intervalIntegrable 0 1)
  rw [hneg] at hsum
  have hquarter : (∫ x : ℝ in 0..1, pCircleProfile p x) =
      ∫ x : ℝ in 0..1, (1 - x ^ p) ^ (1 / p) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    simp [pCircleProfile, abs_of_nonneg hx.1]
  rw [hquarter] at hsum
  linarith

/-- Fubini's area formula in (11), valid even for nonconvex positive-exponent disks. -/
theorem volume_unitDisk_eq_integral {p : ℝ} (hp : 0 < p) :
    volume (unitDisk p) =
      ENNReal.ofReal (4 * ∫ x : ℝ in 0..1, (1 - x ^ p) ^ (1 / p)) := by
  let region : Set (ℝ × ℝ) := {z | z.1 ∈ Icc (-1) 1 ∧
    z.2 ∈ Icc (-pCircleProfile p z.1) (pCircleProfile p z.1)}
  have hc := continuous_pCircleProfile hp
  have hm : MeasurableSet region :=
    measurableSet_region_between_cc hc.neg.measurable hc.measurable measurableSet_Icc
  have he := (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).measure_preimage hm.nullMeasurableSet
  have hpre : (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)) ⁻¹' region = unitDisk p := by
    ext x
    exact (disk_inequality_iff hp (x 0) (x 1)).symm
  rw [hpre] at he
  rw [he, volume_between_closed (fun x => -pCircleProfile p x) (pCircleProfile p)
    hc.neg hc (-1) 1 (fun x hx => by linarith [pCircleProfile_nonneg hp hx])]
  congr 1
  simp_rw [sub_neg_eq_add, ← two_mul]
  rw [MeasureTheory.integral_const_mul, integral_profile hp]
  ring

/-- The corresponding upper-half area integral, including the diameter. -/
theorem volume_upperHalfDisk_eq_integral {p : ℝ} (hp : 0 < p) :
    volume (upperHalfDisk p) =
      ENNReal.ofReal (2 * ∫ x : ℝ in 0..1, (1 - x ^ p) ^ (1 / p)) := by
  let region : Set (ℝ × ℝ) := {z | z.1 ∈ Icc (-1) 1 ∧ z.2 ∈ Icc 0 (pCircleProfile p z.1)}
  have hc := continuous_pCircleProfile hp
  have hm : MeasurableSet region :=
    measurableSet_region_between_cc measurable_const hc.measurable measurableSet_Icc
  have he := (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).measure_preimage hm.nullMeasurableSet
  have hpre : (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)) ⁻¹' region = upperHalfDisk p := by
    ext x
    exact (upper_inequality_iff hp (x 0) (x 1)).symm
  rw [hpre] at he
  rw [he, volume_between_closed (fun _ => 0) (pCircleProfile p)
    continuous_const hc (-1) 1 (fun x hx => pCircleProfile_nonneg hp hx)]
  simp only [sub_zero, integral_profile hp]

/-- Equation (11) for every positive exponent, without a convexity assumption. -/
theorem volume_unitDisk_of_pos {p : ℝ} (hp : 0 < p) :
    volume (unitDisk p) = ENNReal.ofReal (2 * gammaHalfArea p) := by
  rw [volume_unitDisk_eq_integral hp, pCircle_integral_eq_gamma hp]
  congr 1
  ring

theorem diskArea_eq_gamma_of_pos {p : ℝ} (hp : 0 < p) : diskArea p = 2 * gammaHalfArea p := by
  rw [diskArea, volume_unitDisk_of_pos hp, ENNReal.toReal_ofReal]
  exact (mul_pos two_pos (gammaHalfArea_pos hp)).le

/-- Equation (12) for every positive exponent. -/
theorem upperHalfArea_eq_gamma_of_pos {p : ℝ} (hp : 0 < p) :
    upperHalfArea p = gammaHalfArea p := by
  rw [upperHalfArea, volume_upperHalfDisk_eq_integral hp, pCircle_integral_eq_gamma hp]
  rw [show 2 * (gammaHalfArea p / 2) = gammaHalfArea p by ring,
    ENNReal.toReal_ofReal (gammaHalfArea_pos hp).le]

theorem diskArea_eq_integral {p : ℝ} (hp : 0 < p) :
    diskArea p = 4 * ∫ x : ℝ in 0..1, (1 - x ^ p) ^ (1 / p) := by
  rw [diskArea_eq_gamma_of_pos hp, pCircle_integral_eq_gamma hp]
  ring

/-- The middle, beta-integral expression in equation (11). -/
theorem diskArea_eq_beta_integral {p : ℝ} (hp : 0 < p) :
    diskArea p = (4 / p) *
      ∫ t : ℝ in 0..1, t ^ (1 / p - 1) * (1 - t) ^ (1 / p) := by
  rw [diskArea_eq_integral hp, pCircle_integral_substitution hp]
  ring

/-- The first Gamma quotient in equation (11). -/
theorem diskArea_eq_gamma_add_one {p : ℝ} (hp : 0 < p) :
    diskArea p = 4 * Real.Gamma (1 + 1 / p) ^ 2 / Real.Gamma (1 + 2 / p) := by
  rw [diskArea_eq_gamma_of_pos hp, gammaHalfArea,
    show 1 + 1 / p = 1 / p + 1 by ring, show 1 + 2 / p = 2 / p + 1 by ring,
    Real.Gamma_add_one (one_div_pos.mpr hp).ne',
    Real.Gamma_add_one (div_pos two_pos hp).ne']
  field_simp
  norm_num

/-- The disks in the additional range `0 < p < 1` are not convex. -/
theorem unitDisk_not_convex {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ¬ Convex ℝ (unitDisk p) := by
  intro hc
  have hx : ![1, 0] ∈ unitDisk p := by simp [unitDisk, Real.zero_rpow hp.ne']
  have hy : ![0, 1] ∈ unitDisk p := by simp [unitDisk, Real.zero_rpow hp.ne']
  have hm := hc hx hy (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have hm' : (1 / 2 : ℝ) ^ p + (1 / 2 : ℝ) ^ p ≤ 1 := by
    simpa [unitDisk, Pi.smul_apply, Pi.add_apply, smul_eq_mul] using hm
  have hpow : (1 / 2 : ℝ) < (1 / 2 : ℝ) ^ p := by
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_gt (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) hp1
  linarith

/-- The Wallis product gives the actual upper-half area also in the nonconvex range. -/
theorem pCircleProduct_tendsto_area_of_pos {p : ℝ} (hp : 0 < p) :
    Tendsto (pCircleProduct p) atTop (𝓝 (upperHalfArea p)) := by
  rw [upperHalfArea_eq_gamma_of_pos hp]
  exact pCircleProduct_tendsto hp

end FitzhughFarnsworth.Wallis
