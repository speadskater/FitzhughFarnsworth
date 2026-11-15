/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Wallis.PCircle
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The cyclic unit-volume construction in N dimensions

Section 5.3 and equation (41) of Fitzhugh–Farnsworth (2013). Explicit finite
products define positive side lengths. Intermediate states in `Fin N → ℝ`
have volume `1 + N*n + j`; each coordinate update attaches volume exactly one.
All side-ratio limits and the first-to-last p-circle area limit follow.
-/

@[expose] public section

namespace FitzhughFarnsworth.Wallis.Hypercube

open Filter Topology

/-- Multiplier for coordinate `i` in complete iteration `n`; coordinates start at zero. -/
noncomputable def sideFactor (N n i : ℕ) : ℝ :=
  ((N : ℝ) * n + i + 2) / ((N : ℝ) * n + i + 1)

/-- The finite side product; geometrical coordinates have `i < N`. -/
noncomputable def side (N n i : ℕ) : ℝ := ∏ k ∈ Finset.range n, sideFactor N k i

/-- The box dimensions after `N*n` attachments. -/
noncomputable def dimensions (N n : ℕ) : Fin N → ℝ := fun i => side N n i

@[simp] theorem side_zero (N i : ℕ) : side N 0 i = 1 := by simp [side]

theorem side_succ (N n i : ℕ) : side N (n + 1) i = side N n i * sideFactor N n i :=
  Finset.prod_range_succ _ _

theorem side_pos (N n i : ℕ) : 0 < side N n i := by
  apply Finset.prod_pos
  intro k _
  unfold sideFactor
  positivity

private theorem prod_sideFactor (N n j : ℕ) :
    (∏ i ∈ Finset.range j, sideFactor N n i) =
      ((N : ℝ) * n + j + 1) / ((N : ℝ) * n + 1) := by
  induction j with
  | zero => simp [show (N : ℝ) * n + 1 ≠ 0 by positivity]
  | succ j ih =>
    rw [Finset.prod_range_succ, ih]
    unfold sideFactor
    push_cast
    field_simp
    ring

theorem volume_cycle (N n : ℕ) :
    (∏ i ∈ Finset.range N, side N n i) = 1 + (N : ℝ) * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [side_succ, Finset.prod_mul_distrib]
    rw [ih, prod_sideFactor]
    push_cast
    field_simp
    ring

/-- Coordinate lengths after the first `j` attachments of iteration `n`. -/
noncomputable def partialSide (N n j i : ℕ) : ℝ :=
  side N n i * if i < j then sideFactor N n i else 1

/-- The intermediate coordinate state after `N*n + j` attachments, for `j ≤ N`. -/
noncomputable def partialDimensions (N n j : ℕ) : Fin N → ℝ :=
  fun i => partialSide N n j i

@[simp] theorem partial_zero (N n : ℕ) : partialDimensions N n 0 = dimensions N n := by
  ext i
  simp [partialDimensions, partialSide, dimensions]

@[simp] theorem partial_full (N n : ℕ) :
    partialDimensions N n N = dimensions N (n + 1) := by
  ext i
  simp [partialDimensions, partialSide, dimensions, i.isLt, side_succ]

theorem partial_pos (N n j : ℕ) (i : Fin N) : 0 < partialDimensions N n j i := by
  unfold partialDimensions partialSide
  apply mul_pos (side_pos N n i)
  split_ifs
  · unfold sideFactor
    positivity
  · exact zero_lt_one

private theorem partial_volume_nat (N n j : ℕ) (hj : j ≤ N) :
    (∏ i ∈ Finset.range N, partialSide N n j i) = 1 + (N : ℝ) * n + j := by
  have hprefix : (∏ i ∈ Finset.range N, if i < j then sideFactor N n i else 1) =
      ∏ i ∈ Finset.range j, sideFactor N n i := by
    symm
    apply Finset.prod_subset_one_on_sdiff (Finset.range_mono hj)
    · intro i hi
      exact ite_eq_right (fun h => (Finset.mem_sdiff.mp hi).2 (Finset.mem_range.mpr h))
    · intro i hi
      exact (ite_eq_left (Finset.mem_range.mp hi)).symm
  simp only [partialSide, Finset.prod_mul_distrib]
  rw [volume_cycle, hprefix, prod_sideFactor]
  field_simp
  ring

/-- The volume after `N*n + j` attachments, including the start and end of a cycle. -/
theorem volume_partial (N n j : ℕ) (hj : j ≤ N) :
    (∏ i : Fin N, partialDimensions N n j i) = 1 + (N : ℝ) * n + j := by
  simpa only [Finset.prod_range, partialDimensions] using partial_volume_nat N n j hj

theorem partial_step_other (N n j i : ℕ) (hij : i ≠ j) :
    partialSide N n (j + 1) i = partialSide N n j i := by
  have h : i < j + 1 ↔ i < j := by omega
  simp only [partialSide, h]

private theorem partial_step_delta (N n j : ℕ) :
    partialSide N n (j + 1) j - partialSide N n j j =
      partialSide N n j j / (1 + (N : ℝ) * n + j) := by
  simp only [partialSide, Nat.lt_succ_self, ↓reduceIte, lt_self_iff_false, mul_one]
  unfold sideFactor
  field_simp
  ring

/-- Every individual coordinate update attaches a box of volume exactly one. -/
theorem attachment_volume (N n : ℕ) (j : Fin N) :
    (partialDimensions N n (j + 1) j - partialDimensions N n j j) *
      (∏ i ∈ Finset.univ.erase j, partialDimensions N n j i) = 1 := by
  have hv := volume_partial N n j j.isLt.le
  have hprod := Finset.mul_prod_erase Finset.univ (fun i => partialDimensions N n j i)
    (Finset.mem_univ j)
  rw [hv] at hprod
  change (partialSide N n (j + 1) j - partialSide N n j j) * _ = 1
  rw [partial_step_delta, div_mul_eq_mul_div]
  change partialDimensions N n j j * _ / _ = 1
  rw [hprod, div_self (by positivity)]

/-- Finite ratio formula for any ordered pair of coordinates. -/
theorem ratio_eq_linear_prod {N : ℕ} (hN : 0 < N) (u v : Fin N) (n : ℕ) :
    dimensions N n u / dimensions N n v =
      ∏ k ∈ Finset.range n,
        ((((u : ℕ) + 2 : ℝ) / N + k) * (((v : ℕ) + 1 : ℝ) / N + k)) /
          ((((u : ℕ) + 1 : ℝ) / N + k) * (((v : ℕ) + 2 : ℝ) / N + k)) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  unfold dimensions side
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro k _
  unfold sideFactor
  field_simp
  ring

/-- The general side-ratio limit displayed immediately before (41). -/
theorem ratio_tendsto {N : ℕ} (hN : 0 < N) (u v : Fin N) :
    Tendsto (fun n => dimensions N n u / dimensions N n v) atTop
      (𝓝 (Real.Gamma (((u : ℕ) + 1 : ℝ) / N) * Real.Gamma (((v : ℕ) + 2 : ℝ) / N) /
        (Real.Gamma (((u : ℕ) + 2 : ℝ) / N) * Real.Gamma (((v : ℕ) + 1 : ℝ) / N)))) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hlim := tendsto_balanced_prod
    (show 0 < ((u : ℕ) + 2 : ℝ) / N by positivity)
    (show 0 < ((v : ℕ) + 1 : ℝ) / N by positivity)
    (show 0 < ((u : ℕ) + 1 : ℝ) / N by positivity)
    (show 0 < ((v : ℕ) + 2 : ℝ) / N by positivity) (by ring)
  exact hlim.congr fun n => (ratio_eq_linear_prod hN u v n).symm

/-- Finite first-to-last ratio in (41), including its interpretation as a p-circle product. -/
theorem first_last_ratio_eq_product {N : ℕ} (hN : 0 < N) (n : ℕ) :
    side N n 0 / side N n (N - 1) = pCircleProduct N n := by
  unfold side pCircleProduct
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro k _
  unfold sideFactor
  rw [Nat.cast_sub (by omega : 1 ≤ N)]
  push_cast
  rw [show (N : ℝ) * k + (N - 1) + 1 = (N : ℝ) * k + N by ring,
    show (N : ℝ) * k + (N - 1) + 2 = (N : ℝ) * k + N + 1 by ring]
  field_simp
  ring

/-- Equation (41): the cyclic construction converges to the measured upper N-circle area. -/
theorem first_last_ratio_tendsto {N : ℕ} (hN : 2 ≤ N) :
    Tendsto (fun n => side N n 0 / side N n (N - 1)) atTop (𝓝 (upperHalfArea N)) := by
  have hp : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  exact (pCircleProduct_tendsto_area hp).congr fun n =>
    (first_last_ratio_eq_product (by omega : 0 < N) n).symm

end FitzhughFarnsworth.Wallis.Hypercube
