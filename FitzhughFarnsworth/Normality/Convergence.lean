/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Normality.Iteration
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Convergence and strict monotonicity of the normal slopes

Theorems 3.4 and 3.5 of Fitzhugh–Farnsworth (2013). Infinite slope limits use
`atTop` and `atBot`; they are not encoded as real numbers. Reflection gives
the corresponding results for negative initial slopes.
-/

@[expose] public section

namespace FitzhughFarnsworth.Normality.Parameters

open Filter Topology

theorem exponent_lt_one (g : Parameters) (hp : 2 < g.p) : g.exponent < 1 := by
  rw [exponent, div_lt_one (by linarith)]
  linarith

theorem one_lt_exponent (g : Parameters) (hp : g.p < 2) : 1 < g.exponent := by
  rw [exponent, lt_div_iff₀ (sub_pos.mpr g.one_lt_p)]
  linarith

private theorem even_index_tendsto : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
  tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id

private theorem odd_index_tendsto : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
  tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id

/-- Theorem 3.4: every positive initial slope has even limit `1`. -/
theorem even_tendsto_one (g : Parameters) (hp : 2 < g.p) {m : ℝ} (hm : 0 < m) :
    Tendsto (fun n => g.slopeIterate m (2 * n)) atTop (𝓝 1) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one g.exponent_pos.le
    (g.exponent_lt_one hp)).comp even_index_tendsto
  simpa only [Function.comp_def, g.slopeIterate_even_formula hm, Real.rpow_zero] using
    (tendsto_const_nhds.rpow h (Or.inl hm.ne'))

/-- Theorem 3.4: every positive initial slope has odd limit `-1`. -/
theorem odd_tendsto_neg_one (g : Parameters) (hp : 2 < g.p) {m : ℝ} (hm : 0 < m) :
    Tendsto (fun n => g.slopeIterate m (2 * n + 1)) atTop (𝓝 (-1)) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one g.exponent_pos.le
    (g.exponent_lt_one hp)).comp odd_index_tendsto
  simpa only [Function.comp_def, g.slopeIterate_odd_formula hm, Real.rpow_zero] using
    (tendsto_const_nhds.rpow h (Or.inl (one_div_pos.mpr hm).ne')).neg

/-- Theorem 3.5, shallow initial slope: even slopes approach zero. -/
theorem even_tendsto_zero (g : Parameters) (hp : g.p < 2)
    {m : ℝ} (hm : 0 < m) (hm1 : m < 1) :
    Tendsto (fun n => g.slopeIterate m (2 * n)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, g.slopeIterate_even_formula hm] using
    (tendsto_rpow_atTop_of_base_lt_one m (by linarith) hm1).comp
      ((tendsto_pow_atTop_atTop_of_one_lt (g.one_lt_exponent hp)).comp even_index_tendsto)

/-- Theorem 3.5, shallow initial slope: odd slopes diverge to negative infinity. -/
theorem odd_tendsto_atBot (g : Parameters) (hp : g.p < 2)
    {m : ℝ} (hm : 0 < m) (hm1 : m < 1) :
    Tendsto (fun n => g.slopeIterate m (2 * n + 1)) atTop atBot := by
  have hi : 1 < 1 / m := (one_lt_div hm).mpr hm1
  simpa only [Function.comp_def, g.slopeIterate_odd_formula hm] using
    tendsto_neg_atTop_atBot.comp ((tendsto_rpow_atTop_of_base_gt_one (1 / m) hi).comp
      ((tendsto_pow_atTop_atTop_of_one_lt (g.one_lt_exponent hp)).comp
        odd_index_tendsto))

/-- Theorem 3.5, steep initial slope: even slopes diverge to positive infinity. -/
theorem even_tendsto_atTop (g : Parameters) (hp : g.p < 2) {m : ℝ} (hm : 1 < m) :
    Tendsto (fun n => g.slopeIterate m (2 * n)) atTop atTop := by
  simpa only [Function.comp_def, g.slopeIterate_even_formula (zero_lt_one.trans hm)] using
    (tendsto_rpow_atTop_of_base_gt_one m hm).comp
      ((tendsto_pow_atTop_atTop_of_one_lt (g.one_lt_exponent hp)).comp even_index_tendsto)

/-- Theorem 3.5, steep initial slope: odd slopes approach zero from below. -/
theorem odd_tendsto_zero (g : Parameters) (hp : g.p < 2) {m : ℝ} (hm : 1 < m) :
    Tendsto (fun n => g.slopeIterate m (2 * n + 1)) atTop (𝓝 0) := by
  have hm0 := zero_lt_one.trans hm
  have hi : 1 / m < 1 := (div_lt_one hm0).mpr hm
  simpa only [Function.comp_def, g.slopeIterate_odd_formula hm0, neg_zero] using
    ((tendsto_rpow_atTop_of_base_lt_one (1 / m) (by linarith [one_div_pos.mpr hm0]) hi).comp
      ((tendsto_pow_atTop_atTop_of_one_lt (g.one_lt_exponent hp)).comp
        odd_index_tendsto)).neg

/-- All even slopes stay strictly between zero and one for a shallow input. -/
theorem even_mem_Ioo (g : Parameters) {m : ℝ} (hm : 0 < m) (hm1 : m < 1) (n : ℕ) :
    g.slopeIterate m (2 * n) ∈ Set.Ioo (0 : ℝ) 1 := by
  rw [g.slopeIterate_even_formula hm]
  exact ⟨Real.rpow_pos_of_pos hm _, Real.rpow_lt_one hm.le hm1
    (pow_pos g.exponent_pos _)⟩

theorem odd_lt_neg_one (g : Parameters) {m : ℝ} (hm : 0 < m) (hm1 : m < 1) (n : ℕ) :
    g.slopeIterate m (2 * n + 1) < -1 := by
  rw [g.slopeIterate_odd_formula hm]
  exact neg_lt_neg (Real.one_lt_rpow ((one_lt_div hm).mpr hm1)
    (pow_pos g.exponent_pos _))

theorem one_lt_even (g : Parameters) {m : ℝ} (hm : 1 < m) (n : ℕ) :
    1 < g.slopeIterate m (2 * n) := by
  rw [g.slopeIterate_even_formula (zero_lt_one.trans hm)]
  exact Real.one_lt_rpow hm (pow_pos g.exponent_pos _)

theorem odd_mem_Ioo (g : Parameters) {m : ℝ} (hm : 1 < m) (n : ℕ) :
    g.slopeIterate m (2 * n + 1) ∈ Set.Ioo (-1 : ℝ) 0 := by
  have hm0 := zero_lt_one.trans hm
  rw [g.slopeIterate_odd_formula hm0]
  exact ⟨neg_lt_neg (Real.rpow_lt_one (by positivity) ((div_lt_one hm0).mpr hm)
    (pow_pos g.exponent_pos _)), neg_neg_of_pos (Real.rpow_pos_of_pos (by positivity) _)⟩

/-- Both parity subsequences strictly increase in Theorem 3.4's shallow case. -/
theorem strictMono_even_of_two_lt (g : Parameters) (hp : 2 < g.p)
    {m : ℝ} (hm : 0 < m) (hm1 : m < 1) :
    StrictMono (fun n => g.slopeIterate m (2 * n)) := by
  intro i j hij
  simp only [g.slopeIterate_even_formula hm]
  exact Real.rpow_lt_rpow_of_exponent_gt hm hm1
    (pow_right_strictAnti₀ g.exponent_pos (g.exponent_lt_one hp) (by omega))

theorem strictMono_odd_of_two_lt (g : Parameters) (hp : 2 < g.p)
    {m : ℝ} (hm : 0 < m) (hm1 : m < 1) :
    StrictMono (fun n => g.slopeIterate m (2 * n + 1)) := by
  intro i j hij
  simp only [g.slopeIterate_odd_formula hm]
  exact neg_lt_neg (Real.rpow_lt_rpow_of_exponent_lt ((one_lt_div hm).mpr hm1)
    (pow_right_strictAnti₀ g.exponent_pos (g.exponent_lt_one hp) (by omega)))

theorem strictAnti_even_of_two_lt (g : Parameters) (hp : 2 < g.p)
    {m : ℝ} (hm : 1 < m) : StrictAnti (fun n => g.slopeIterate m (2 * n)) := by
  intro i j hij
  simp only [g.slopeIterate_even_formula (zero_lt_one.trans hm)]
  exact Real.rpow_lt_rpow_of_exponent_lt hm
    (pow_right_strictAnti₀ g.exponent_pos (g.exponent_lt_one hp) (by omega))

theorem strictAnti_odd_of_two_lt (g : Parameters) (hp : 2 < g.p)
    {m : ℝ} (hm : 1 < m) : StrictAnti (fun n => g.slopeIterate m (2 * n + 1)) := by
  have hm0 := zero_lt_one.trans hm
  intro i j hij
  simp only [g.slopeIterate_odd_formula hm0]
  exact neg_lt_neg (Real.rpow_lt_rpow_of_exponent_gt (one_div_pos.mpr hm0)
    ((div_lt_one hm0).mpr hm)
    (pow_right_strictAnti₀ g.exponent_pos (g.exponent_lt_one hp) (by omega)))

/-- Both parity subsequences strictly decrease in Theorem 3.5's shallow case. -/
theorem strictAnti_even_of_lt_two (g : Parameters) (hp : g.p < 2)
    {m : ℝ} (hm : 0 < m) (hm1 : m < 1) :
    StrictAnti (fun n => g.slopeIterate m (2 * n)) := by
  intro i j hij
  simp only [g.slopeIterate_even_formula hm]
  exact Real.rpow_lt_rpow_of_exponent_gt hm hm1
    (pow_right_strictMono₀ (g.one_lt_exponent hp) (by omega))

theorem strictAnti_odd_of_lt_two (g : Parameters) (hp : g.p < 2)
    {m : ℝ} (hm : 0 < m) (hm1 : m < 1) :
    StrictAnti (fun n => g.slopeIterate m (2 * n + 1)) := by
  intro i j hij
  simp only [g.slopeIterate_odd_formula hm]
  exact neg_lt_neg (Real.rpow_lt_rpow_of_exponent_lt ((one_lt_div hm).mpr hm1)
    (pow_right_strictMono₀ (g.one_lt_exponent hp) (by omega)))

theorem strictMono_even_of_lt_two (g : Parameters) (hp : g.p < 2)
    {m : ℝ} (hm : 1 < m) : StrictMono (fun n => g.slopeIterate m (2 * n)) := by
  intro i j hij
  simp only [g.slopeIterate_even_formula (zero_lt_one.trans hm)]
  exact Real.rpow_lt_rpow_of_exponent_lt hm
    (pow_right_strictMono₀ (g.one_lt_exponent hp) (by omega))

theorem strictMono_odd_of_lt_two (g : Parameters) (hp : g.p < 2)
    {m : ℝ} (hm : 1 < m) : StrictMono (fun n => g.slopeIterate m (2 * n + 1)) := by
  have hm0 := zero_lt_one.trans hm
  intro i j hij
  simp only [g.slopeIterate_odd_formula hm0]
  exact neg_lt_neg (Real.rpow_lt_rpow_of_exponent_gt (one_div_pos.mpr hm0)
    ((div_lt_one hm0).mpr hm)
    (pow_right_strictMono₀ (g.one_lt_exponent hp) (by omega)))

end FitzhughFarnsworth.Normality.Parameters
