/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Normality.Convergence
public import FitzhughFarnsworth.Normality.Geometry
public import Mathlib.Topology.Algebra.Projectivization

/-!
# Convergence of the actual normal lines

Lines through the origin are points of mathlib's real projective line, with
its quotient topology. This treats both signs of infinite slope as the same
vertical line. Every geometric normal evolution agrees with `Direction.iterate`.
-/

@[expose] public section

namespace FitzhughFarnsworth.Normality.Direction

open Filter Topology
open scoped LinearAlgebra.Projectivization

/-- The actual unoriented line, in the standard topological projective space. -/
noncomputable def projective (d : Direction) : ℙ ℝ (ℝ × ℝ) :=
  Projectivization.mk ℝ d.vector d.vector_ne_zero

theorem chart_ne_zero (m : ℝ) : (m, (1 : ℝ)) ≠ 0 := by simp [Prod.ext_iff]

theorem continuous_projective_finite : Continuous (fun m : ℝ => (finite m).projective) :=
  Projectivization.continuous_mk (continuous_const.prodMk continuous_id)
    (fun m => (finite m).vector_ne_zero)

theorem finite_projective_eq_reciprocal {m : ℝ} (hm : m ≠ 0) :
    (finite m).projective = Projectivization.mk ℝ (m⁻¹, 1) (chart_ne_zero _) := by
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
  refine ⟨m, ?_⟩
  ext <;> simp [vector, hm]

theorem projective_tendsto_of_tendsto {s : ℕ → ℝ} {m : ℝ}
    (h : Tendsto s atTop (𝓝 m)) :
    Tendsto (fun n => (finite (s n)).projective) atTop (𝓝 (finite m).projective) :=
  continuous_projective_finite.continuousAt.tendsto.comp h

/-- Reciprocal slopes tending to zero give convergence to the genuine vertical line. -/
theorem projective_tendsto_vertical {s : ℕ → ℝ} (hs : ∀ n, s n ≠ 0)
    (h : Tendsto (fun n => (s n)⁻¹) atTop (𝓝 0)) :
    Tendsto (fun n => (finite (s n)).projective) atTop (𝓝 vertical.projective) := by
  have hc := Projectivization.continuous_mk (K := ℝ)
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))))
    chart_ne_zero
  have hl : Tendsto (fun n => Projectivization.mk ℝ ((s n)⁻¹, 1) (chart_ne_zero _))
      atTop (𝓝 vertical.projective) := hc.continuousAt.tendsto.comp h
  exact hl.congr (fun n => (finite_projective_eq_reciprocal (hs n)).symm)

/-- Any choice of geometric normals produces the same direction sequence. -/
theorem evolution_eq_iterate (g : Parameters) (d : Direction) (s : ℕ → Direction)
    (h0 : s 0 = d) (hn : ∀ n, g.IsNormal (s (n + 1)).vector (s n).vector) :
    s = iterate g d := by
  funext n
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [(isNormal_iff_eq_next g _ _).mp (hn n), ih]
    rfl

/-- Theorem 3.4, as convergence of geometric lines. -/
theorem iterate_tendsto_diagonals (g : Parameters) (hp : 2 < g.p)
    {m : ℝ} (hm : 0 < m) :
    Tendsto (fun n => (iterate g (finite m) (2 * n)).projective)
      atTop (𝓝 (finite 1).projective) ∧
    Tendsto (fun n => (iterate g (finite m) (2 * n + 1)).projective)
      atTop (𝓝 (finite (-1)).projective) := by
  simp only [iterate_finite g hm.ne']
  exact ⟨projective_tendsto_of_tendsto (g.even_tendsto_one hp hm),
    projective_tendsto_of_tendsto (g.odd_tendsto_neg_one hp hm)⟩

/-- Theorem 3.5, shallow positive initial slope: horizontal then vertical. -/
theorem iterate_tendsto_axes_of_lt_one (g : Parameters) (hp : g.p < 2)
    {m : ℝ} (hm : 0 < m) (hm1 : m < 1) :
    Tendsto (fun n => (iterate g (finite m) (2 * n)).projective)
      atTop (𝓝 (finite 0).projective) ∧
    Tendsto (fun n => (iterate g (finite m) (2 * n + 1)).projective)
      atTop (𝓝 vertical.projective) := by
  simp only [iterate_finite g hm.ne']
  exact ⟨projective_tendsto_of_tendsto (g.even_tendsto_zero hp hm hm1),
    projective_tendsto_vertical (fun n => g.slopeIterate_ne_zero hm.ne' _)
      (g.odd_tendsto_atBot hp hm hm1).inv_tendsto_atBot⟩

/-- Theorem 3.5, steep positive initial slope: vertical then horizontal. -/
theorem iterate_tendsto_axes_of_one_lt (g : Parameters) (hp : g.p < 2)
    {m : ℝ} (hm : 1 < m) :
    Tendsto (fun n => (iterate g (finite m) (2 * n)).projective)
      atTop (𝓝 vertical.projective) ∧
    Tendsto (fun n => (iterate g (finite m) (2 * n + 1)).projective)
      atTop (𝓝 (finite 0).projective) := by
  have hm0 := zero_lt_one.trans hm
  simp only [iterate_finite g hm0.ne']
  exact ⟨projective_tendsto_vertical (fun n => g.slopeIterate_ne_zero hm0.ne' _)
      (g.even_tendsto_atTop hp hm).inv_tendsto_atTop,
    projective_tendsto_of_tendsto (g.odd_tendsto_zero hp hm)⟩

/-- Reflection transports Theorem 3.4, reversing the order of the diagonals. -/
theorem iterate_tendsto_diagonals_of_neg (g : Parameters) (hp : 2 < g.p)
    {m : ℝ} (hm : m < 0) :
    Tendsto (fun n => (iterate g (finite m) (2 * n)).projective)
      atTop (𝓝 (finite (-1)).projective) ∧
    Tendsto (fun n => (iterate g (finite m) (2 * n + 1)).projective)
      atTop (𝓝 (finite 1).projective) := by
  have he : Tendsto (fun n => g.slopeIterate m (2 * n)) atTop (𝓝 (-1)) := by
    simpa only [g.slopeIterate_neg hm.ne, neg_neg] using
      (g.even_tendsto_one hp (neg_pos.mpr hm)).neg
  have ho : Tendsto (fun n => g.slopeIterate m (2 * n + 1)) atTop (𝓝 1) := by
    simpa only [g.slopeIterate_neg hm.ne, neg_neg] using
      (g.odd_tendsto_neg_one hp (neg_pos.mpr hm)).neg
  simpa only [iterate_finite g hm.ne] using
    And.intro (projective_tendsto_of_tendsto he) (projective_tendsto_of_tendsto ho)

theorem iterate_tendsto_axes_of_neg_lt_one (g : Parameters) (hp : g.p < 2)
    {m : ℝ} (hm : m < 0) (hm1 : -1 < m) :
    Tendsto (fun n => (iterate g (finite m) (2 * n)).projective)
      atTop (𝓝 (finite 0).projective) ∧
    Tendsto (fun n => (iterate g (finite m) (2 * n + 1)).projective)
      atTop (𝓝 vertical.projective) := by
  have he : Tendsto (fun n => g.slopeIterate m (2 * n)) atTop (𝓝 0) := by
    simpa only [g.slopeIterate_neg hm.ne, neg_neg, neg_zero] using
      (g.even_tendsto_zero hp (neg_pos.mpr hm) (by linarith)).neg
  have ho : Tendsto (fun n => g.slopeIterate m (2 * n + 1)) atTop atTop := by
    simpa only [Function.comp_def, g.slopeIterate_neg hm.ne, neg_neg] using
      tendsto_neg_atBot_atTop.comp (g.odd_tendsto_atBot hp (neg_pos.mpr hm) (by linarith))
  simp only [iterate_finite g hm.ne]
  exact ⟨projective_tendsto_of_tendsto he,
    projective_tendsto_vertical (fun n => g.slopeIterate_ne_zero hm.ne _)
      ho.inv_tendsto_atTop⟩

theorem iterate_tendsto_axes_of_lt_neg_one (g : Parameters) (hp : g.p < 2)
    {m : ℝ} (hm : m < -1) :
    Tendsto (fun n => (iterate g (finite m) (2 * n)).projective)
      atTop (𝓝 vertical.projective) ∧
    Tendsto (fun n => (iterate g (finite m) (2 * n + 1)).projective)
      atTop (𝓝 (finite 0).projective) := by
  have hm0 : m < 0 := by linarith
  have he : Tendsto (fun n => g.slopeIterate m (2 * n)) atTop atBot := by
    simpa only [Function.comp_def, g.slopeIterate_neg hm0.ne, neg_neg] using
      tendsto_neg_atTop_atBot.comp (g.even_tendsto_atTop hp (by linarith : 1 < -m))
  have ho : Tendsto (fun n => g.slopeIterate m (2 * n + 1)) atTop (𝓝 0) := by
    simpa only [g.slopeIterate_neg hm0.ne, neg_neg, neg_zero] using
      (g.odd_tendsto_zero hp (by linarith : 1 < -m)).neg
  simp only [iterate_finite g hm0.ne]
  exact ⟨projective_tendsto_vertical (fun n => g.slopeIterate_ne_zero hm0.ne _)
      he.inv_tendsto_atBot, projective_tendsto_of_tendsto ho⟩

/-- Any two-cycle remains exact at every even and odd index. -/
theorem iterate_of_cycle (g : Parameters) {d : Direction} (hd : next g (next g d) = d)
    (n : ℕ) : iterate g d (2 * n) = d ∧ iterate g d (2 * n + 1) = next g d := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    have he : iterate g d (2 * (n + 1)) = d := by
      change iterate g d (2 * n + 2) = d
      change next g (iterate g d (2 * n + 1)) = d
      rw [ih.2, hd]
    exact ⟨he, by change next g (iterate g d (2 * (n + 1))) = _; rw [he]⟩

end FitzhughFarnsworth.Normality.Direction
