/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Wallis.GammaProducts

/-!
# Balanced Gamma products with any finite number of factors

Equations (8)–(9) of Fitzhugh–Farnsworth (2013), using the equivalent zero-based
indexing. All shifts are positive, so the paper's one-based shifts must exceed
`-1`. The numerator and denominator have the same finite index set, and the
sums of their shifts must agree.
-/

@[expose] public section

namespace FitzhughFarnsworth.Wallis

open Filter Topology

private theorem gammaSeq_finset {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {n : ℕ} (hn : 0 < n) :
    (∏ i ∈ s, Real.GammaSeq (x i) n) =
      (n : ℝ) ^ (∑ i ∈ s, x i) * (n.factorial : ℝ) ^ s.card /
        ∏ k ∈ Finset.range (n + 1), ∏ i ∈ s, (x i + k) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  simp only [Real.GammaSeq, Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const]
  rw [← Real.rpow_sum_of_pos hn', Finset.prod_comm]

private theorem gammaSeq_finset_balance {ι : Type*} (s : Finset ι) (x y : ι → ℝ)
    (hx : ∀ i ∈ s, 0 < x i) (hy : ∀ i ∈ s, 0 < y i)
    (hbalance : ∑ i ∈ s, x i = ∑ i ∈ s, y i) {n : ℕ} (hn : 0 < n) :
    (∏ i ∈ s, Real.GammaSeq (y i) n) / (∏ i ∈ s, Real.GammaSeq (x i) n) =
      ∏ k ∈ Finset.range (n + 1), (∏ i ∈ s, (x i + k)) / (∏ i ∈ s, (y i + k)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hscale : (n : ℝ) ^ (∑ i ∈ s, y i) * (n.factorial : ℝ) ^ s.card ≠ 0 := by positivity
  have hxp : (∏ k ∈ Finset.range (n + 1), ∏ i ∈ s, (x i + k)) ≠ 0 := by
    apply ne_of_gt
    exact Finset.prod_pos fun k _ => Finset.prod_pos fun i hi =>
      add_pos_of_pos_of_nonneg (hx i hi) (Nat.cast_nonneg k)
  have hyp : (∏ k ∈ Finset.range (n + 1), ∏ i ∈ s, (y i + k)) ≠ 0 := by
    apply ne_of_gt
    exact Finset.prod_pos fun k _ => Finset.prod_pos fun i hi =>
      add_pos_of_pos_of_nonneg (hy i hi) (Nat.cast_nonneg k)
  rw [gammaSeq_finset s x hn, gammaSeq_finset s y hn, hbalance, Finset.prod_div_distrib]
  field_simp [hscale, hxp, hyp]

/-- Equations (8)–(9), for an arbitrary finite number of positive linear factors. -/
theorem tendsto_balanced_finset_prod {ι : Type*} (s : Finset ι) (x y : ι → ℝ)
    (hx : ∀ i ∈ s, 0 < x i) (hy : ∀ i ∈ s, 0 < y i)
    (hbalance : ∑ i ∈ s, x i = ∑ i ∈ s, y i) :
    Tendsto (fun n : ℕ =>
      ∏ k ∈ Finset.range n, (∏ i ∈ s, (x i + k)) / (∏ i ∈ s, (y i + k)))
      atTop (𝓝 ((∏ i ∈ s, Real.Gamma (y i)) / (∏ i ∈ s, Real.Gamma (x i)))) := by
  have hden : (∏ i ∈ s, Real.Gamma (x i)) ≠ 0 :=
    (Finset.prod_pos fun i hi => Real.Gamma_pos_of_pos (hx i hi)).ne'
  have hlim := (tendsto_finsetProd s (fun i _ => Real.GammaSeq_tendsto_Gamma (y i))).div
    (tendsto_finsetProd s (fun i _ => Real.GammaSeq_tendsto_Gamma (x i))) hden
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact gammaSeq_finset_balance s x y hx hy hbalance hn

end FitzhughFarnsworth.Wallis
