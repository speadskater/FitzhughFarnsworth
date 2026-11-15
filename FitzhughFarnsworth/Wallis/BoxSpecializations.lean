/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Wallis.BoxConvergence
public import FitzhughFarnsworth.Wallis.PCircle

/-!
# Box constructions realizing p-circle areas

Equations (38)–(40) of Fitzhugh–Farnsworth (2013). The general parameter
conditions are proved first, followed by explicit positive-parameter examples
for every `p > 2` and every `1 < p < 2`.

The first numerator in the printed equation (39) is `pn + p + 2`. The attachment
recurrence gives `pn - p + 2`, as in (40). The finite product identities below
use the derived expression, with zero-based indexing; see the roadmap.
-/

@[expose] public section

namespace FitzhughFarnsworth.Wallis

open Filter Topology

namespace BoxParameters

/-- The paper's `p = (2A+B)/(abc)` when `A = C`. -/
noncomputable def circleExponent (s : BoxParameters) : ℝ :=
  (s.A + s.B + s.C) / (s.a * s.b * s.c)

theorem circleExponent_pos (s : BoxParameters) : 0 < s.circleExponent :=
  div_pos (add_pos (add_pos s.A_pos s.B_pos) s.C_pos)
    (mul_pos (mul_pos s.a_pos s.b_pos) s.c_pos)

theorem circleExponent_gt_two (s : BoxParameters) (hAC : s.A = s.C)
    (hA : s.A = s.a * s.b * s.c) : 2 < s.circleExponent := by
  unfold circleExponent
  rw [← hA, ← hAC]
  apply (lt_div_iff₀ s.A_pos).mpr
  linarith [s.B_pos]

theorem circleExponent_between_one_two (s : BoxParameters) (hAC : s.A = s.C)
    (hAB : s.A + s.B = s.a * s.b * s.c) :
    1 < s.circleExponent ∧ s.circleExponent < 2 := by
  unfold circleExponent
  rw [← hAB, ← hAC]
  constructor
  · apply (lt_div_iff₀ (add_pos s.A_pos s.B_pos)).mpr
    linarith [s.A_pos]
  · apply (div_lt_iff₀ (add_pos s.A_pos s.B_pos)).mpr
    linarith [s.B_pos]

/-- Corrected (39), for every box satisfying the paper's parameter conditions. -/
theorem ratio_eq_pCircleProduct_of_right_volume (s : BoxParameters)
    (hAC : s.A = s.C) (hac : s.a = s.c) (hA : s.A = s.a * s.b * s.c) (n : ℕ) :
    s.ratio n = pCircleProduct s.circleExponent n := by
  rw [ratio_eq_prod, hac, div_self s.c_pos.ne', one_mul]
  apply Finset.prod_congr rfl
  intro k _
  have hAp := s.A_pos
  have hBp := s.B_pos
  unfold ratioFactor circleExponent
  rw [← hA, ← hAC]
  push_cast
  field_simp
  ring

/-- Equation (40), for every box satisfying the paper's parameter conditions. -/
theorem ratio_eq_pCircleProduct_of_right_top_volume (s : BoxParameters)
    (hAC : s.A = s.C) (hac : s.a = s.c) (hAB : s.A + s.B = s.a * s.b * s.c) (n : ℕ) :
    s.ratio n = pCircleProduct s.circleExponent n := by
  rw [ratio_eq_prod, hac, div_self s.c_pos.ne', one_mul]
  apply Finset.prod_congr rfl
  intro k _
  have hAp := s.A_pos
  have hBp := s.B_pos
  unfold ratioFactor circleExponent
  rw [← hAB, ← hAC]
  push_cast
  field_simp
  ring

theorem ratio_tendsto_area_of_right_volume (s : BoxParameters)
    (hAC : s.A = s.C) (hac : s.a = s.c) (hA : s.A = s.a * s.b * s.c) :
    Tendsto s.ratio atTop (𝓝 (upperHalfArea s.circleExponent)) := by
  rw [show s.ratio = pCircleProduct s.circleExponent from
    funext (s.ratio_eq_pCircleProduct_of_right_volume hAC hac hA)]
  exact pCircleProduct_tendsto_area (by linarith [s.circleExponent_gt_two hAC hA])

theorem ratio_tendsto_area_of_right_top_volume (s : BoxParameters)
    (hAC : s.A = s.C) (hac : s.a = s.c) (hAB : s.A + s.B = s.a * s.b * s.c) :
    Tendsto s.ratio atTop (𝓝 (upperHalfArea s.circleExponent)) := by
  rw [show s.ratio = pCircleProduct s.circleExponent from
    funext (s.ratio_eq_pCircleProduct_of_right_top_volume hAC hac hAB)]
  exact pCircleProduct_tendsto_area (s.circleExponent_between_one_two hAC hAB).1.le

end BoxParameters

/-- A unit initial cube realizing each exponent `p > 2` in (39). -/
def boxAboveTwo (p : ℝ) (hp : 2 < p) : BoxParameters where
  a := 1
  b := 1
  c := 1
  A := 1
  B := p - 2
  C := 1
  a_pos := zero_lt_one
  b_pos := zero_lt_one
  c_pos := zero_lt_one
  A_pos := zero_lt_one
  B_pos := sub_pos.mpr hp
  C_pos := zero_lt_one

/-- A unit initial cube realizing each exponent `1 < p < 2` in (40). -/
def boxBelowTwo (p : ℝ) (hp : 1 < p) (hp2 : p < 2) : BoxParameters where
  a := 1
  b := 1
  c := 1
  A := p - 1
  B := 2 - p
  C := p - 1
  a_pos := zero_lt_one
  b_pos := zero_lt_one
  c_pos := zero_lt_one
  A_pos := sub_pos.mpr hp
  B_pos := sub_pos.mpr hp2
  C_pos := sub_pos.mpr hp

@[simp] theorem boxAboveTwo_exponent (p : ℝ) (hp : 2 < p) :
    (boxAboveTwo p hp).circleExponent = p := by
  dsimp [boxAboveTwo, BoxParameters.circleExponent]
  ring

@[simp] theorem boxBelowTwo_exponent (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    (boxBelowTwo p hp hp2).circleExponent = p := by
  dsimp [boxBelowTwo, BoxParameters.circleExponent]
  ring

theorem boxAboveTwo_ratio (p : ℝ) (hp : 2 < p) (n : ℕ) :
    (boxAboveTwo p hp).ratio n = pCircleProduct p n := by
  simpa only [boxAboveTwo_exponent] using
    (boxAboveTwo p hp).ratio_eq_pCircleProduct_of_right_volume rfl rfl (by norm_num [boxAboveTwo]) n

theorem boxBelowTwo_ratio (p : ℝ) (hp : 1 < p) (hp2 : p < 2) (n : ℕ) :
    (boxBelowTwo p hp hp2).ratio n = pCircleProduct p n := by
  simpa only [boxBelowTwo_exponent] using
    (boxBelowTwo p hp hp2).ratio_eq_pCircleProduct_of_right_top_volume rfl rfl
      (by dsimp [boxBelowTwo]; ring) n

theorem boxAboveTwo_ratio_tendsto (p : ℝ) (hp : 2 < p) :
    Tendsto (boxAboveTwo p hp).ratio atTop (𝓝 (upperHalfArea p)) := by
  rw [show (boxAboveTwo p hp).ratio = pCircleProduct p from funext (boxAboveTwo_ratio p hp)]
  exact pCircleProduct_tendsto_area (by linarith)

theorem boxBelowTwo_ratio_tendsto (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    Tendsto (boxBelowTwo p hp hp2).ratio atTop (𝓝 (upperHalfArea p)) := by
  rw [show (boxBelowTwo p hp hp2).ratio = pCircleProduct p from funext (boxBelowTwo_ratio p hp hp2)]
  exact pCircleProduct_tendsto_area hp.le

/-- Equation (38): initial and attached boxes all have unit volume. -/
def unitCube : BoxParameters := boxAboveTwo 3 (by norm_num)

theorem unitCube_ratio_tendsto : Tendsto unitCube.ratio atTop (𝓝 (upperHalfArea 3)) :=
  boxAboveTwo_ratio_tendsto 3 (by norm_num)

theorem unitCube_ratio_one : unitCube.ratio 1 = 3 / 2 := by
  rw [show unitCube.ratio 1 = pCircleProduct 3 1 from boxAboveTwo_ratio 3 (by norm_num) 1]
  norm_num [pCircleProduct]

end FitzhughFarnsworth.Wallis
