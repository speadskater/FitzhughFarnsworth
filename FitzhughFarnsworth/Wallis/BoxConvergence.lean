/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Wallis.BoxConstruction
public import FitzhughFarnsworth.Wallis.GammaProducts

/-!
# Limits of the three-dimensional box construction

Equations (35)–(37) of Fitzhugh–Farnsworth (2013). The width-to-depth ratio
has a positive finite Gamma limit exactly when `A = C`. The two unequal cases
are also classified, retaining the distinction between zero and positive infinity.
-/

@[expose] public section

namespace FitzhughFarnsworth.Wallis.BoxParameters

open Filter Topology

/-- Initial volume in units of the volume attached during one complete iteration. -/
noncomputable def volumeShift (s : BoxParameters) : ℝ := s.a * s.b * s.c / (s.A + s.B + s.C)

/-- Normalized volume after the first width attachment. -/
noncomputable def widthShift (s : BoxParameters) : ℝ :=
  (s.a * s.b * s.c + s.A) / (s.A + s.B + s.C)

/-- Normalized volume after the first width and height attachments. -/
noncomputable def heightShift (s : BoxParameters) : ℝ :=
  (s.a * s.b * s.c + s.A + s.B) / (s.A + s.B + s.C)

theorem volumeShift_pos (s : BoxParameters) : 0 < s.volumeShift :=
  div_pos (mul_pos (mul_pos s.a_pos s.b_pos) s.c_pos)
    (add_pos (add_pos s.A_pos s.B_pos) s.C_pos)

theorem widthShift_pos (s : BoxParameters) : 0 < s.widthShift :=
  div_pos (add_pos (mul_pos (mul_pos s.a_pos s.b_pos) s.c_pos) s.A_pos)
    (add_pos (add_pos s.A_pos s.B_pos) s.C_pos)

theorem heightShift_pos (s : BoxParameters) : 0 < s.heightShift :=
  div_pos (add_pos (add_pos (mul_pos (mul_pos s.a_pos s.b_pos) s.c_pos) s.A_pos) s.B_pos)
    (add_pos (add_pos s.A_pos s.B_pos) s.C_pos)

theorem shift_difference (s : BoxParameters) :
    s.widthShift + s.heightShift - (s.volumeShift + (s.volumeShift + 1)) =
      (s.A - s.C) / (s.A + s.B + s.C) := by
  unfold widthShift heightShift volumeShift
  field_simp [(add_pos (add_pos s.A_pos s.B_pos) s.C_pos).ne']
  ring

/-- Equation (36) is exactly the balance condition `A = C`. -/
theorem balance_iff (s : BoxParameters) :
    (s.a * s.b * s.c - s.B - s.C) / (s.A + s.B + s.C) +
        (s.a * s.b * s.c - s.C) / (s.A + s.B + s.C) =
      (s.a * s.b * s.c - s.A - s.B - s.C) / (s.A + s.B + s.C) +
        s.a * s.b * s.c / (s.A + s.B + s.C) ↔ s.A = s.C := by
  field_simp [(add_pos (add_pos s.A_pos s.B_pos) s.C_pos).ne']
  constructor <;> intro h <;> linarith

theorem ratioFactor_eq_linear (s : BoxParameters) (n : ℕ) :
    s.ratioFactor n = ((s.widthShift + n) * (s.heightShift + n)) /
      ((s.volumeShift + n) * (s.volumeShift + 1 + n)) := by
  have ha := s.a_pos
  have hb := s.b_pos
  have hc := s.c_pos
  have hA := s.A_pos
  have hB := s.B_pos
  have hC := s.C_pos
  unfold ratioFactor widthShift heightShift volumeShift
  push_cast
  field_simp
  ring

/-- Finite version of (35), with equivalent zero-based shifts. -/
theorem ratio_eq_linear_prod (s : BoxParameters) (n : ℕ) :
    s.ratio n = s.a / s.c *
      ∏ k ∈ Finset.range n, ((s.widthShift + k) * (s.heightShift + k)) /
        ((s.volumeShift + k) * (s.volumeShift + 1 + k)) := by
  rw [ratio_eq_prod]
  congr 1
  exact Finset.prod_congr rfl fun k _ => s.ratioFactor_eq_linear k

/-- The positive Gamma constant for the balanced width-to-depth ratio. -/
noncomputable def gammaLimit (s : BoxParameters) : ℝ :=
  s.a / s.c * s.volumeShift * Real.Gamma s.volumeShift ^ 2 /
    (Real.Gamma s.widthShift * Real.Gamma s.heightShift)

theorem gammaLimit_pos (s : BoxParameters) : 0 < s.gammaLimit :=
  div_pos (mul_pos (mul_pos (div_pos s.a_pos s.c_pos) s.volumeShift_pos)
    (sq_pos_of_pos (Real.Gamma_pos_of_pos s.volumeShift_pos)))
    (mul_pos (Real.Gamma_pos_of_pos s.widthShift_pos) (Real.Gamma_pos_of_pos s.heightShift_pos))

/-- The constant in the exact form printed in equation (37). -/
theorem gammaLimit_eq_paper (s : BoxParameters) (hAC : s.A = s.C) :
    s.gammaLimit = s.a / s.c * (s.a * s.b * s.c / (2 * s.A + s.B)) *
      Real.Gamma (s.a * s.b * s.c / (2 * s.A + s.B)) ^ 2 /
        (Real.Gamma ((s.a * s.b * s.c + s.A) / (2 * s.A + s.B)) *
          Real.Gamma ((s.a * s.b * s.c + s.A + s.B) / (2 * s.A + s.B))) := by
  have hsum : s.A + s.B + s.C = 2 * s.A + s.B := by rw [← hAC]; ring
  simp only [gammaLimit, volumeShift, widthShift, heightShift, hsum]

/-- Equation (37), for the ratio of the actual constructed box dimensions. -/
theorem ratio_tendsto_gammaLimit (s : BoxParameters) (hAC : s.A = s.C) :
    Tendsto s.ratio atTop (𝓝 s.gammaLimit) := by
  have hbalance : s.widthShift + s.heightShift = s.volumeShift + (s.volumeShift + 1) := by
    have hd := s.shift_difference
    rw [hAC, sub_self, zero_div] at hd
    linarith
  have hlim := (tendsto_balanced_prod s.widthShift_pos s.heightShift_pos s.volumeShift_pos
    (by linarith [s.volumeShift_pos]) hbalance).const_mul (s.a / s.c)
  have heq : s.a / s.c *
      (Real.Gamma s.volumeShift * Real.Gamma (s.volumeShift + 1) /
        (Real.Gamma s.widthShift * Real.Gamma s.heightShift)) = s.gammaLimit := by
    rw [Real.Gamma_add_one s.volumeShift_pos.ne']
    unfold gammaLimit
    ring
  rw [heq] at hlim
  exact hlim.congr fun n => (s.ratio_eq_linear_prod n).symm

theorem ratio_tendsto_zero (s : BoxParameters) (hAC : s.A < s.C) :
    Tendsto s.ratio atTop (𝓝 0) := by
  have hsum : s.widthShift + s.heightShift < s.volumeShift + (s.volumeShift + 1) := by
    have hneg := div_neg_of_neg_of_pos (sub_neg.mpr hAC)
      (add_pos (add_pos s.A_pos s.B_pos) s.C_pos)
    linarith [s.shift_difference]
  have hlim := (tendsto_linear_prod_zero s.widthShift_pos s.heightShift_pos s.volumeShift_pos
    (by linarith [s.volumeShift_pos]) hsum).const_mul (s.a / s.c)
  simp only [mul_zero] at hlim
  exact hlim.congr fun n => (s.ratio_eq_linear_prod n).symm

theorem ratio_tendsto_atTop (s : BoxParameters) (hAC : s.C < s.A) :
    Tendsto s.ratio atTop atTop := by
  have hsum : s.volumeShift + (s.volumeShift + 1) < s.widthShift + s.heightShift := by
    have hpos := div_pos (sub_pos.mpr hAC) (add_pos (add_pos s.A_pos s.B_pos) s.C_pos)
    linarith [s.shift_difference]
  have hlim := (tendsto_linear_prod_atTop s.widthShift_pos s.heightShift_pos s.volumeShift_pos
    (by linarith [s.volumeShift_pos]) hsum).const_mul_atTop (div_pos s.a_pos s.c_pos)
  exact hlim.congr fun n => (s.ratio_eq_linear_prod n).symm

theorem ratio_tendsto_pos_iff (s : BoxParameters) {l : ℝ} (hl : 0 < l) :
    Tendsto s.ratio atTop (𝓝 l) ↔ s.A = s.C ∧ l = s.gammaLimit := by
  constructor
  · intro h
    rcases lt_trichotomy s.A s.C with hlt | heq | hgt
    · have := tendsto_nhds_unique h (s.ratio_tendsto_zero hlt)
      linarith
    · exact ⟨heq, tendsto_nhds_unique h (s.ratio_tendsto_gammaLimit heq)⟩
    · exact (not_tendsto_nhds_of_tendsto_atTop (s.ratio_tendsto_atTop hgt) l h).elim
  · rintro ⟨hAC, rfl⟩
    exact s.ratio_tendsto_gammaLimit hAC

end FitzhughFarnsworth.Wallis.BoxParameters
