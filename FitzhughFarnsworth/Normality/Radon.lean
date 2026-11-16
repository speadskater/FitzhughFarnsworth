/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Normality.Geometry
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Conjugate exponents and the Radon construction

The algebra in Theorem 4.1 and equations (12)–(14). The conjugate parameter is
`q = p/(p-1)`. The normal map uses the exponent of the quadrant containing the
normal vector, and is an involution. The uniqueness result is formulated for
a continuous quadrant graph with positive height and positive tangent slope
in its interior; the endpoint value fixes the integration constant.
-/

@[expose] public section

namespace FitzhughFarnsworth.Normality

open Set Filter Topology

namespace Parameters

/-- The conjugate exponent, characterized by `1/p + 1/q = 1`. -/
noncomputable def conjugate (g : Parameters) : Parameters where
  p := g.p / (g.p - 1)
  one_lt_p := (lt_div_iff₀ (sub_pos.mpr g.one_lt_p)).mpr (by linarith)

theorem conjugate_sub_one (g : Parameters) : g.conjugate.p - 1 = g.exponent := by
  dsimp [conjugate, exponent]
  field_simp [(sub_pos.mpr g.one_lt_p).ne']
  ring

theorem conjugate_exponent (g : Parameters) : g.conjugate.exponent = g.p - 1 := by
  rw [exponent, conjugate_sub_one, exponent]
  simp

theorem conjugate_identity (g : Parameters) : 1 / g.p + 1 / g.conjugate.p = 1 := by
  dsimp [conjugate]
  field_simp [(zero_lt_one.trans g.one_lt_p).ne', (sub_pos.mpr g.one_lt_p).ne']
  ring

@[simp] theorem conjugate_conjugate (g : Parameters) : g.conjugate.conjugate = g := by
  apply Parameters.ext
  change g.conjugate.p / (g.conjugate.p - 1) = g.p
  rw [conjugate_sub_one]
  dsimp [conjugate, exponent]
  field_simp [(sub_pos.mpr g.one_lt_p).ne']

theorem conjugate_normalSlope_normalSlope (g : Parameters) {m : ℝ} (hm : m ≠ 0) :
    g.conjugate.normalSlope (g.normalSlope m) = m := by
  have he : (-g.exponent) * (-g.conjugate.exponent) = 1 := by
    rw [conjugate_exponent, exponent]
    field_simp [(sub_pos.mpr g.one_lt_p).ne']
  rcases lt_or_gt_of_ne hm with hm | hm
  · rw [g.conjugate.normalSlope_of_pos (g.normalSlope_pos_of_neg hm),
      g.normalSlope_of_neg hm, ← Real.rpow_mul (neg_pos.mpr hm).le, he, Real.rpow_one,
      neg_neg]
  · rw [g.conjugate.normalSlope_of_neg (g.normalSlope_neg_of_pos hm),
      g.normalSlope_of_pos hm, neg_neg, ← Real.rpow_mul hm.le, he, Real.rpow_one]

/-- Equations (12)–(14): reflexivity fixes the tangent slope of the unknown quadrant. -/
theorem reflexive_tangent_iff (g : Parameters) {x y t : ℝ}
    (hx : x < 0) (hy : 0 < y) (ht : 0 < t) :
    g.IsNormal (1, t) (x, y) ↔ t = ((-x) / y) ^ g.exponent := by
  rw [g.isNormal_iff]
  simp only [dualCoord_one, one_mul, g.dualCoord_of_pos ht]
  have hb : 0 < (-x) / y := div_pos (neg_pos.mpr hx) hy
  have he : g.exponent * (g.p - 1) = 1 := by
    rw [exponent]
    exact one_div_mul_cancel (sub_pos.mpr g.one_lt_p).ne'
  constructor
  · intro h
    apply (Real.rpow_left_inj ht.le (Real.rpow_nonneg hb.le _)
      (sub_pos.mpr g.one_lt_p).ne').mp
    rw [← Real.rpow_mul hb.le, he, Real.rpow_one]
    apply (eq_div_iff hy.ne').mpr
    linarith
  · rintro rfl
    rw [← Real.rpow_mul hb.le, he, Real.rpow_one]
    field_simp
    ring

/-- The differential equation forces the conjugate-power quantity to be constant. -/
theorem hasDerivAt_conjugate_energy_zero (g : Parameters) {f : ℝ → ℝ} {x t : ℝ}
    (hx : x < 0) (hy : 0 < f x) (ht : 0 < t) (hd : HasDerivAt f t x)
    (hn : g.IsNormal (1, t) (x, f x)) :
    HasDerivAt (fun z => (-z) ^ g.conjugate.p + f z ^ g.conjugate.p) 0 x := by
  have ht' := (g.reflexive_tangent_iff hx hy ht).mp hn
  have hcancel : (f x) ^ g.exponent * t = (-x) ^ g.exponent := by
    rw [ht', Real.div_rpow (neg_pos.mpr hx).le hy.le]
    field_simp [(Real.rpow_pos_of_pos hy g.exponent).ne']
  have hxder := (hasDerivAt_neg x).rpow_const
    (Or.inl (neg_pos.mpr hx).ne') (p := g.conjugate.p)
  have hyder := hd.rpow_const (Or.inl hy.ne') (p := g.conjugate.p)
  convert hxder.add hyder using 1
  rw [conjugate_sub_one]
  calc
    0 = g.conjugate.p * ((f x) ^ g.exponent * t - (-x) ^ g.exponent) := by
      rw [hcancel, sub_self, mul_zero]
    _ = _ := by ring

/-- Necessity in Theorem 4.1, including the endpoint that fixes the constant.
The hypotheses express a regular upper-left quadrant and reflexivity with the
given upper-right p-circle, without assuming any formula for the unknown graph. -/
theorem quadrant_unique (g : Parameters) {f f' : ℝ → ℝ}
    (hc : ContinuousOn f (Icc (-1) 0)) (h0 : f 0 = 1)
    (hy : ∀ x ∈ Ioo (-1) 0, 0 < f x)
    (ht : ∀ x ∈ Ioo (-1) 0, 0 < f' x)
    (hd : ∀ x ∈ Ioo (-1) 0, HasDerivAt f (f' x) x)
    (hn : ∀ x ∈ Ioo (-1) 0, g.IsNormal (1, f' x) (x, f x)) :
    ∀ x ∈ Icc (-1) 0, (-x) ^ g.conjugate.p + f x ^ g.conjugate.p = 1 := by
  let F : ℝ → ℝ := fun x => (-x) ^ g.conjugate.p + f x ^ g.conjugate.p
  have hF : ContinuousOn F (Icc (-1) 0) := by
    exact ((continuous_neg.rpow_const (fun _ => Or.inr
      (by linarith [g.conjugate.one_lt_p]))).continuousOn).add
      (hc.rpow_const (fun x _ => Or.inr (by linarith [g.conjugate.one_lt_p])))
  have hFd : ∀ x ∈ Ioo (-1) 0, HasDerivAt F 0 x :=
    fun x hx => g.hasDerivAt_conjugate_energy_zero hx.2 (hy x hx) (ht x hx) (hd x hx) (hn x hx)
  have hcst : ∀ x ∈ Ioo (-1) 0, F x = F (-1 / 2) := by
    intro x hx
    have hb := (convex_Ioo (-1 : ℝ) 0).norm_image_sub_le_of_norm_hasDerivWithin_le
      (C := 0) (fun z hz => (hFd z hz).hasDerivWithinAt) (fun _ _ => by simp)
      (by norm_num : (-1 / 2 : ℝ) ∈ Ioo (-1) 0) hx
    exact sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa only [zero_mul] using hb))
  have hclosed : EqOn F (fun _ => F (-1 / 2)) (Icc (-1) 0) := by
    apply Set.EqOn.of_subset_closure hcst hF continuousOn_const Ioo_subset_Icc_self
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 0)]
  have hF0 : F 0 = 1 := by simp [F, h0, (zero_lt_one.trans g.conjugate.one_lt_p).ne']
  intro x hx
  exact (hclosed hx).trans ((hclosed (by norm_num : (0 : ℝ) ∈ Icc (-1) 0)).symm.trans hF0)

end Parameters

namespace Direction

/-- Normal direction for the curve with p-arcs in quadrants I/III and q-arcs in II/IV. -/
noncomputable def radonNext (g : Parameters) : Direction → Direction
  | vertical => finite 0
  | finite m => if m = 0 then vertical
      else if 0 < m then finite (g.conjugate.normalSlope m) else finite (g.normalSlope m)

/-- Sufficiency at the direction level, including both joins on the axes. -/
theorem radonNext_involutive (g : Parameters) : Function.Involutive (radonNext g) := by
  intro d
  cases d with
  | vertical => simp [radonNext]
  | finite m =>
    rcases lt_trichotomy m 0 with hm | rfl | hm
    · simp only [radonNext, hm.ne, ↓reduceIte, not_lt.mpr hm.le,
        (g.normalSlope_pos_of_neg hm).ne', g.normalSlope_pos_of_neg hm,
        g.conjugate_normalSlope_normalSlope hm.ne]
    · simp [radonNext]
    · simp only [radonNext, hm.ne', ↓reduceIte, hm,
        (g.conjugate.normalSlope_neg_of_pos hm).ne,
        not_lt.mpr (g.conjugate.normalSlope_neg_of_pos hm).le]
      have h := g.conjugate.conjugate_normalSlope_normalSlope hm.ne'
      simpa only [Parameters.conjugate_conjugate] using congrArg finite h

end Direction

end FitzhughFarnsworth.Normality
