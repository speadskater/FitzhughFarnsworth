/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Wallis.Hypercube

/-!
# Cyclic unit-volume attachments from a cube of arbitrary positive volume

The initial cube has volume `v > 0` and side `v^(1/N)`. Every individual
attachment has volume one. At `v = 1` these are exactly the original
`Wallis.Hypercube` states. Coordinates follow the order of attachment.
-/

@[expose] public section

namespace FitzhughFarnsworth.Wallis.ShiftedHypercube

open Filter Topology

/-- The multiplicative update for coordinate `i` in cycle `n`. -/
noncomputable def sideFactor (N : ℕ) (v : ℝ) (n i : ℕ) : ℝ :=
  (v + N * (n : ℝ) + i + 1) / (v + N * (n : ℝ) + i)

/-- Side lengths after complete cycles, beginning with an equal-sided cube. -/
noncomputable def side (N : ℕ) (v : ℝ) (n i : ℕ) : ℝ :=
  v ^ (1 / (N : ℝ)) * ∏ k ∈ Finset.range n, sideFactor N v k i

/-- The actual `N` coordinate lengths after `N*n` attachments. -/
noncomputable def dimensions (N : ℕ) (v : ℝ) (n : ℕ) : Fin N → ℝ :=
  fun i => side N v n i

@[simp] theorem side_zero (N : ℕ) (v : ℝ) (i : ℕ) :
    side N v 0 i = v ^ (1 / (N : ℝ)) := by simp [side]

theorem side_succ (N : ℕ) (v : ℝ) (n i : ℕ) :
    side N v (n + 1) i = side N v n i * sideFactor N v n i := by
  simp only [side, Finset.prod_range_succ, mul_assoc]

theorem sideFactor_pos (N n i : ℕ) {v : ℝ} (hv : 0 < v) : 0 < sideFactor N v n i := by
  unfold sideFactor
  positivity

theorem side_pos (N n i : ℕ) {v : ℝ} (hv : 0 < v) : 0 < side N v n i := by
  apply mul_pos (Real.rpow_pos_of_pos hv _)
  exact Finset.prod_pos (fun k _ => sideFactor_pos N k i hv)

theorem sideFactor_strictAnti (N n : ℕ) {v : ℝ} (hv : 0 < v) :
    StrictAnti (sideFactor N v n) := by
  intro i j hij
  have hijr : (i : ℝ) < j := Nat.cast_lt.mpr hij
  unfold sideFactor
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

/-- After a positive number of cycles, earlier coordinates are strictly longer. -/
theorem side_strictAnti (N n : ℕ) {v : ℝ} (hv : 0 < v) :
    StrictAnti (side N v (n + 1)) := by
  induction n with
  | zero =>
    intro i j hij
    simpa only [side_succ, side_zero] using
      mul_lt_mul_of_pos_left (sideFactor_strictAnti N 0 hv hij) (Real.rpow_pos_of_pos hv _)
  | succ n ih =>
    intro i j hij
    rw [side_succ N v (n + 1) j, side_succ N v (n + 1) i]
    exact (mul_lt_mul_of_pos_right (ih hij) (sideFactor_pos N (n + 1) j hv)).trans
      (mul_lt_mul_of_pos_left (sideFactor_strictAnti N (n + 1) hv hij)
        (side_pos N (n + 1) i hv))

theorem dimensions_strictAnti (N n : ℕ) {v : ℝ} (hv : 0 < v) :
    StrictAnti (dimensions N v (n + 1)) := fun _ _ hij => side_strictAnti N n hv hij

private theorem prod_sideFactor (N n j : ℕ) {v : ℝ} (hv : 0 < v) :
    (∏ i ∈ Finset.range j, sideFactor N v n i) =
      (v + N * (n : ℝ) + j) / (v + N * (n : ℝ)) := by
  induction j with
  | zero => simp [show v + N * (n : ℝ) ≠ 0 by positivity]
  | succ j ih =>
    rw [Finset.prod_range_succ, ih]
    unfold sideFactor
    push_cast
    field_simp
    ring

/-- The product of the actual side lengths is the initial volume plus the number
of attachments performed. -/
theorem volume_cycle {N : ℕ} (hN : 0 < N) {v : ℝ} (hv : 0 < v) (n : ℕ) :
    (∏ i ∈ Finset.range N, side N v n i) = v + N * (n : ℝ) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  induction n with
  | zero =>
    simp only [side_zero, Finset.prod_const, Finset.card_range, Nat.cast_zero, mul_zero, add_zero]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv.le, one_div_mul_cancel hNr.ne', Real.rpow_one]
  | succ n ih =>
    simp only [side_succ, Finset.prod_mul_distrib]
    rw [ih, prod_sideFactor N n N hv]
    push_cast
    field_simp
    ring

/-- Intermediate side after `j` attachments in the current cycle. -/
noncomputable def partialSide (N : ℕ) (v : ℝ) (n j i : ℕ) : ℝ :=
  side N v n i * if i < j then sideFactor N v n i else 1

/-- Intermediate box, with `j ≤ N` for geometrical states. -/
noncomputable def partialDimensions (N : ℕ) (v : ℝ) (n j : ℕ) : Fin N → ℝ :=
  fun i => partialSide N v n j i

@[simp] theorem partial_zero (N : ℕ) (v : ℝ) (n : ℕ) :
    partialDimensions N v n 0 = dimensions N v n := by
  ext i
  simp [partialDimensions, partialSide, dimensions]

@[simp] theorem partial_full (N : ℕ) (v : ℝ) (n : ℕ) :
    partialDimensions N v n N = dimensions N v (n + 1) := by
  ext i
  simp [partialDimensions, partialSide, dimensions, i.isLt, side_succ]

theorem partial_pos (N n j : ℕ) {v : ℝ} (hv : 0 < v) (i : Fin N) :
    0 < partialDimensions N v n j i := by
  apply mul_pos (side_pos N n i hv)
  split_ifs
  · exact sideFactor_pos N n i hv
  · exact zero_lt_one

/-- The volume identity holds at every intermediate attachment, not just complete cycles. -/
theorem volume_partial {N : ℕ} (hN : 0 < N) {v : ℝ} (hv : 0 < v)
    (n j : ℕ) (hj : j ≤ N) :
    (∏ i : Fin N, partialDimensions N v n j i) = v + N * (n : ℝ) + j := by
  have hprefix : (∏ i ∈ Finset.range N, if i < j then sideFactor N v n i else 1) =
      ∏ i ∈ Finset.range j, sideFactor N v n i := by
    symm
    apply Finset.prod_subset_one_on_sdiff (Finset.range_mono hj)
    · intro i hi
      exact ite_eq_right (fun h => (Finset.mem_sdiff.mp hi).2 (Finset.mem_range.mpr h))
    · intro i hi
      exact (ite_eq_left (Finset.mem_range.mp hi)).symm
  simp only [partialDimensions]
  rw [← Finset.prod_range]
  simp only [partialSide, Finset.prod_mul_distrib]
  rw [volume_cycle hN hv, hprefix, prod_sideFactor N n j hv]
  field_simp

/-- An attachment leaves all other coordinates unchanged. -/
theorem partial_step_other (N : ℕ) (v : ℝ) (n j i : ℕ) (hij : i ≠ j) :
    partialSide N v n (j + 1) i = partialSide N v n j i := by
  have h : i < j + 1 ↔ i < j := by omega
  simp only [partialSide, h]

private theorem partial_step_delta (N n j : ℕ) {v : ℝ} (hv : 0 < v) :
    partialSide N v n (j + 1) j - partialSide N v n j j =
      partialSide N v n j j / (v + N * (n : ℝ) + j) := by
  simp only [partialSide, Nat.lt_succ_self, ↓reduceIte, lt_self_iff_false, mul_one]
  unfold sideFactor
  field_simp
  ring

/-- Each update attaches an actual box of volume one across the current face. -/
theorem attachment_volume {N : ℕ} (hN : 0 < N) {v : ℝ} (hv : 0 < v)
    (n : ℕ) (j : Fin N) :
    (partialDimensions N v n (j + 1) j - partialDimensions N v n j j) *
      (∏ i ∈ Finset.univ.erase j, partialDimensions N v n j i) = 1 := by
  have hvn := volume_partial hN hv n j j.isLt.le
  have hprod := Finset.mul_prod_erase Finset.univ (fun i => partialDimensions N v n j i)
    (Finset.mem_univ j)
  rw [hvn] at hprod
  change (partialSide N v n (j + 1) j - partialSide N v n j j) * _ = 1
  rw [partial_step_delta N n j hv, div_mul_eq_mul_div]
  change partialDimensions N v n j j * _ / _ = 1
  rw [hprod, div_self (by positivity)]

/-- Finite side ratios are balanced products with shifts determined by the starting volume. -/
theorem ratio_eq_linear_prod {N : ℕ} (hN : 0 < N) {v : ℝ} (hv : 0 < v)
    (i j : Fin N) (n : ℕ) :
    dimensions N v n i / dimensions N v n j =
      ∏ k ∈ Finset.range n,
        (((v + (i : ℕ) + 1) / N + k) * ((v + (j : ℕ)) / N + k)) /
          (((v + (i : ℕ)) / N + k) * ((v + (j : ℕ) + 1) / N + k)) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  unfold dimensions side
  rw [mul_div_mul_left _ _ (Real.rpow_pos_of_pos hv _).ne', ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro k _
  unfold sideFactor
  field_simp
  ring

/-- The Gamma limit for every ordered pair of sides, with all shifts positive. -/
theorem ratio_tendsto {N : ℕ} (hN : 0 < N) {v : ℝ} (hv : 0 < v) (i j : Fin N) :
    Tendsto (fun n => dimensions N v n i / dimensions N v n j) atTop
      (𝓝 (Real.Gamma ((v + (i : ℕ)) / N) * Real.Gamma ((v + (j : ℕ) + 1) / N) /
        (Real.Gamma ((v + (i : ℕ) + 1) / N) * Real.Gamma ((v + (j : ℕ)) / N)))) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hlim := tendsto_balanced_prod
    (show 0 < (v + (i : ℕ) + 1) / N by positivity)
    (show 0 < (v + (j : ℕ)) / N by positivity)
    (show 0 < (v + (i : ℕ)) / N by positivity)
    (show 0 < (v + (j : ℕ) + 1) / N by positivity) (by ring)
  exact hlim.congr fun n => (ratio_eq_linear_prod hN hv i j n).symm

/-- Initial volume one recovers the original finite construction exactly. -/
theorem side_one (N n i : ℕ) : side N 1 n i = Hypercube.side N n i := by
  simp only [side, Real.one_rpow, one_mul, Hypercube.side]
  apply Finset.prod_congr rfl
  intro k _
  unfold sideFactor Hypercube.sideFactor
  congr 1 <;> ring

theorem dimensions_one (N n : ℕ) : dimensions N 1 n = Hypercube.dimensions N n := by
  ext i
  exact side_one N n i

theorem partialDimensions_one (N n j : ℕ) :
    partialDimensions N 1 n j = Hypercube.partialDimensions N n j := by
  ext i
  simp only [partialDimensions, partialSide, Hypercube.partialDimensions, Hypercube.partialSide,
    side_one]
  split_ifs
  · unfold sideFactor Hypercube.sideFactor
    congr 2 <;> ring
  · rfl

end FitzhughFarnsworth.Wallis.ShiftedHypercube
