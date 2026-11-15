/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Wallis.GammaProducts
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Measured p-circle areas and their Wallis products

Equations (11)–(12) for `p ≥ 1`, including the actual Lebesgue measure of the
upper half of the closed unit disk. The infinite product underlying (38)–(41)
is proved for every `p > 0`; its geometric interpretation here uses `p ≥ 1`.
The nonconvex area formula for `0 < p < 1` and the paper's integral substitution
are separate roadmap items.
-/

@[expose] public section

namespace FitzhughFarnsworth.Wallis

open Filter Topology MeasureTheory
open scoped Pointwise

/-- The closed unit p-disk in the coordinate plane with its usual Lebesgue measure. -/
def unitDisk (p : ℝ) : Set (Fin 2 → ℝ) := {x | |x 0| ^ p + |x 1| ^ p ≤ 1}

/-- The upper half of the disk, including its diameter. -/
def upperHalfDisk (p : ℝ) : Set (Fin 2 → ℝ) := unitDisk p ∩ {x | 0 ≤ x 1}

/-- Area is defined by Lebesgue measure, not by the Gamma formula. -/
noncomputable def diskArea (p : ℝ) : ℝ := (volume (unitDisk p)).toReal

/-- The Lebesgue area of the actual upper half, including its diameter. -/
noncomputable def upperHalfArea (p : ℝ) : ℝ := (volume (upperHalfDisk p)).toReal

/-- The Gamma expression `U(p)` in equation (12). -/
noncomputable def gammaHalfArea (p : ℝ) : ℝ :=
  (1 / p) * Real.Gamma (1 / p) ^ 2 / Real.Gamma (2 / p)

theorem gammaHalfArea_pos {p : ℝ} (hp : 0 < p) : 0 < gammaHalfArea p :=
  div_pos (mul_pos (one_div_pos.mpr hp)
    (sq_pos_of_pos (Real.Gamma_pos_of_pos (one_div_pos.mpr hp))))
    (Real.Gamma_pos_of_pos (div_pos two_pos hp))

/-- Equation (11), with measure-theoretic area and the paper's convexity range. -/
theorem volume_unitDisk {p : ℝ} (hp : 1 ≤ p) :
    volume (unitDisk p) = ENNReal.ofReal (2 * gammaHalfArea p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hset : {x : Fin 2 → ℝ | (∑ i, |x i| ^ p) ^ (1 / p) ≤ 1} = unitDisk p := by
    ext x
    simp only [Fin.sum_univ_two, unitDisk, Set.mem_ofPred_eq]
    simpa only [Real.one_rpow] using
      (Real.rpow_le_rpow_iff (by positivity : 0 ≤ |x 0| ^ p + |x 1| ^ p)
        zero_le_one (one_div_pos.mpr hp0))
  have hv := MeasureTheory.volume_sum_rpow_le (Fin 2) hp (1 : ℝ)
  simp only [hset, Fintype.card_fin, Nat.cast_ofNat, ENNReal.ofReal_one, one_pow,
    one_mul] at hv
  rw [hv]
  congr 1
  rw [Real.Gamma_add_one (one_div_pos.mpr hp0).ne',
    Real.Gamma_add_one (div_pos two_pos hp0).ne']
  unfold gammaHalfArea
  field_simp

theorem diskArea_eq_gamma {p : ℝ} (hp : 1 ≤ p) : diskArea p = 2 * gammaHalfArea p := by
  rw [diskArea, volume_unitDisk hp, ENNReal.toReal_ofReal]
  exact (mul_pos two_pos (gammaHalfArea_pos (lt_of_lt_of_le zero_lt_one hp))).le

/-- Equation (12): the actual upper half has the Gamma area `U(p)`. -/
theorem upperHalfArea_eq_gamma {p : ℝ} (hp : 1 ≤ p) :
    upperHalfArea p = gammaHalfArea p := by
  let lower : Set (Fin 2 → ℝ) := unitDisk p ∩ {x | x 1 ≤ 0}
  have hcont : Continuous (fun x : Fin 2 → ℝ => |x 0| ^ p + |x 1| ^ p) :=
    ((Real.continuous_rpow_const (by linarith)).comp (continuous_apply 0).abs).add
      ((Real.continuous_rpow_const (by linarith)).comp (continuous_apply 1).abs)
  have hlower : MeasurableSet lower :=
    (isClosed_le hcont continuous_const).measurableSet.inter
      (isClosed_le (continuous_apply 1) continuous_const).measurableSet
  have hneg : -upperHalfDisk p = lower := by
    ext x
    simp [upperHalfDisk, unitDisk, lower]
  have hvol : volume lower = volume (upperHalfDisk p) := by
    rw [← hneg, Measure.measure_neg]
  have hunion : upperHalfDisk p ∪ lower = unitDisk p := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · exact hx.1
    · intro hx
      rcases le_total 0 (x 1) with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have hdis : AEDisjoint volume (upperHalfDisk p) lower := by
    apply measure_mono_null (t := {x : Fin 2 → ℝ | x 1 = 0})
    · intro x hx
      exact le_antisymm hx.2.2 hx.1.2
    · exact Measure.pi_hyperplane (fun _ : Fin 2 => (volume : Measure ℝ)) 1 0
  have hfinite : volume (upperHalfDisk p) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [volume_unitDisk hp]; exact ENNReal.ofReal_ne_top)
      (measure_mono Set.inter_subset_left)
  have hsum := measure_union₀ hlower.nullMeasurableSet hdis
  rw [hunion, hvol] at hsum
  have hreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add hfinite hfinite] at hreal
  change diskArea p = upperHalfArea p + upperHalfArea p at hreal
  rw [diskArea_eq_gamma hp] at hreal
  linarith

/-- Zero-based partial products common to (38), corrected (39), (40), and (41). -/
noncomputable def pCircleProduct (p : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n,
    ((p * k + 2) / (p * k + 1)) * ((p * k + p) / (p * k + p + 1))

theorem pCircleProduct_tendsto {p : ℝ} (hp : 0 < p) :
    Tendsto (pCircleProduct p) atTop (𝓝 (gammaHalfArea p)) := by
  have hlim := tendsto_balanced_prod (div_pos two_pos hp) zero_lt_one
    (one_div_pos.mpr hp) (by linarith [one_div_pos.mpr hp])
    (show 2 / p + 1 = 1 / p + (1 / p + 1) by ring)
  have hc : Real.Gamma (1 / p) * Real.Gamma (1 / p + 1) /
      (Real.Gamma (2 / p) * Real.Gamma 1) = gammaHalfArea p := by
    rw [Real.Gamma_one, mul_one, Real.Gamma_add_one (one_div_pos.mpr hp).ne']
    unfold gammaHalfArea
    ring
  rw [hc] at hlim
  apply hlim.congr
  intro n
  apply Finset.prod_congr rfl
  intro k _
  field_simp
  ring

/-- The Wallis-type product converges to the measured area of the upper p-disk. -/
theorem pCircleProduct_tendsto_area {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (pCircleProduct p) atTop (𝓝 (upperHalfArea p)) := by
  rw [upperHalfArea_eq_gamma hp]
  exact pCircleProduct_tendsto (lt_of_lt_of_le zero_lt_one hp)

/-- The product as printed in (39), with `pn + p + 2`, diverges.
The index here is shifted from the paper's `n ≥ 1` to `k ≥ 0`. -/
theorem printed_product39_tendsto_atTop {p : ℝ} (hp : 0 < p) :
    Tendsto (fun n : ℕ => ∏ k ∈ Finset.range n,
      ((p * k + 2 * p + 2) / (p * k + 1)) * ((p * k + p) / (p * k + p + 1)))
      atTop atTop := by
  have hlim := tendsto_linear_prod_atTop
    (show 0 < 2 + 2 / p by positivity) zero_lt_one
    (one_div_pos.mpr hp) (show 0 < 1 / p + 1 by positivity)
    (show 1 / p + (1 / p + 1) < (2 + 2 / p) + 1 by ring_nf; linarith)
  apply hlim.congr
  intro n
  apply Finset.prod_congr rfl
  intro k _
  field_simp
  ring

end FitzhughFarnsworth.Wallis
