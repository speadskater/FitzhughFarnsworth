/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Wallis.Convergence

/-!
# Classification of rectangle aspect-ratio limits

Section 2 and Section 5.1 of Fitzhugh–Farnsworth (2013): equal attachment areas
give the positive Gamma limit; larger right attachments give positive infinity;
larger top attachments give zero. Equation (22) characterizes balance, which
must be distinguished from the existence of a finite limit that may be zero.
-/

@[expose] public section

namespace FitzhughFarnsworth.Wallis.Parameters

open Filter Topology

/-- Initial area divided by the area attached during a complete iteration. -/
noncomputable def areaShift (c : Parameters) : ℝ := c.a * c.b / (c.A + c.B)

/-- Area after the first right attachment, in units of the area added per iteration. -/
noncomputable def widthShift (c : Parameters) : ℝ := (c.a * c.b + c.A) / (c.A + c.B)

theorem areaShift_pos (c : Parameters) : 0 < c.areaShift :=
  div_pos (mul_pos c.a_pos c.b_pos) (add_pos c.A_pos c.B_pos)

theorem widthShift_pos (c : Parameters) : 0 < c.widthShift :=
  div_pos (add_pos (mul_pos c.a_pos c.b_pos) c.A_pos) (add_pos c.A_pos c.B_pos)

/-- The total exponent controlling the growth of the finite product. -/
theorem shift_difference (c : Parameters) :
    c.widthShift + c.widthShift - (c.areaShift + (c.areaShift + 1)) =
      (c.A - c.B) / (c.A + c.B) := by
  unfold widthShift areaShift
  field_simp [(add_pos c.A_pos c.B_pos).ne']
  ring

/-- Equation (22), with the paper's one-based shifts, is exactly `A = B`. -/
theorem balance_iff (c : Parameters) :
    (c.a * c.b - c.B) / (c.A + c.B) + (c.a * c.b - c.B) / (c.A + c.B) =
      (c.a * c.b - c.A - c.B) / (c.A + c.B) + c.a * c.b / (c.A + c.B) ↔
        c.A = c.B := by
  field_simp [(add_pos c.A_pos c.B_pos).ne']
  constructor <;> intro h <;> linarith

/-- Normalize equation (20) without assuming equal attachment areas. -/
theorem ratioFactor_eq_linear (c : Parameters) (n : ℕ) :
    c.ratioFactor n = ((c.widthShift + n) * (c.widthShift + n)) /
      ((c.areaShift + n) * (c.areaShift + 1 + n)) := by
  have ha := c.a_pos
  have hb := c.b_pos
  have hA := c.A_pos
  have hB := c.B_pos
  unfold ratioFactor widthShift areaShift
  push_cast
  field_simp
  ring

/-- Finite version of the product in (21), with the equivalent zero-based shifts. -/
theorem ratio_eq_linear_prod (c : Parameters) (n : ℕ) :
    c.ratio n = c.a / c.b *
      ∏ k ∈ Finset.range n, ((c.widthShift + k) * (c.widthShift + k)) /
        ((c.areaShift + k) * (c.areaShift + 1 + k)) := by
  rw [ratio_eq_prod]
  congr 1
  exact Finset.prod_congr rfl fun k _ => c.ratioFactor_eq_linear k

/-- When more area is attached above than to the right, aspect ratios tend to zero. -/
theorem ratio_tendsto_zero (c : Parameters) (hAB : c.A < c.B) :
    Tendsto c.ratio atTop (𝓝 0) := by
  have hsum : c.widthShift + c.widthShift < c.areaShift + (c.areaShift + 1) := by
    have hneg := div_neg_of_neg_of_pos (sub_neg.mpr hAB) (add_pos c.A_pos c.B_pos)
    linarith [c.shift_difference]
  have hlim := (tendsto_linear_prod_zero c.widthShift_pos c.widthShift_pos c.areaShift_pos
    (by linarith [c.areaShift_pos]) hsum).const_mul (c.a / c.b)
  simp only [mul_zero] at hlim
  exact hlim.congr fun n => (c.ratio_eq_linear_prod n).symm

/-- When more area is attached to the right than above, aspect ratios grow without bound. -/
theorem ratio_tendsto_atTop (c : Parameters) (hAB : c.B < c.A) :
    Tendsto c.ratio atTop atTop := by
  have hsum : c.areaShift + (c.areaShift + 1) < c.widthShift + c.widthShift := by
    have hpos := div_pos (sub_pos.mpr hAB) (add_pos c.A_pos c.B_pos)
    linarith [c.shift_difference]
  have hlim := (tendsto_linear_prod_atTop c.widthShift_pos c.widthShift_pos c.areaShift_pos
    (by linarith [c.areaShift_pos]) hsum).const_mul_atTop (div_pos c.a_pos c.b_pos)
  exact hlim.congr fun n => (c.ratio_eq_linear_prod n).symm

/-- A positive finite aspect-ratio limit exists exactly in the balanced case. -/
theorem ratio_tendsto_pos_iff (c : Parameters) {l : ℝ} (hl : 0 < l) :
    Tendsto c.ratio atTop (𝓝 l) ↔ c.A = c.B ∧ l = c.gammaLimit := by
  constructor
  · intro h
    rcases lt_trichotomy c.A c.B with hlt | heq | hgt
    · have := tendsto_nhds_unique h (c.ratio_tendsto_zero hlt)
      linarith
    · exact ⟨heq, tendsto_nhds_unique h (c.ratio_tendsto_gammaLimit heq)⟩
    · exact (not_tendsto_nhds_of_tendsto_atTop (c.ratio_tendsto_atTop hgt) l h).elim
  · rintro ⟨hAB, rfl⟩
    exact c.ratio_tendsto_gammaLimit hAB

/-- A finite limit may be zero: its existence is equivalent to `A ≤ B`. -/
theorem exists_ratio_limit_iff (c : Parameters) :
    (∃ l : ℝ, Tendsto c.ratio atTop (𝓝 l)) ↔ c.A ≤ c.B := by
  constructor
  · rintro ⟨l, hl⟩
    by_contra h
    exact not_tendsto_nhds_of_tendsto_atTop (c.ratio_tendsto_atTop (lt_of_not_ge h)) l hl
  · intro h
    rcases h.eq_or_lt with heq | hlt
    · exact ⟨c.gammaLimit, c.ratio_tendsto_gammaLimit heq⟩
    · exact ⟨0, c.ratio_tendsto_zero hlt⟩

end FitzhughFarnsworth.Wallis.Parameters
