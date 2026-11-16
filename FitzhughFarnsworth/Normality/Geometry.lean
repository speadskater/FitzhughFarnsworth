/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Normality.Iteration
public import Mathlib.Analysis.InnerProductSpace.NormPow
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Geometric normality in the p-plane

The slope formula is derived from distance minimization in mathlib's `WithLp`
metric. The derivative of the pth power of the norm also identifies its tangent
directions. Horizontal and vertical directions remain explicit.
-/

@[expose] public section

namespace FitzhughFarnsworth.Normality

open Set Filter Topology

namespace Parameters

/-- The pth power of the p-norm, in Cartesian coordinates. -/
noncomputable def energy (g : Parameters) (v : ℝ × ℝ) : ℝ :=
  |v.1| ^ g.p + |v.2| ^ g.p

/-- One coordinate of the gradient, with its common positive factor `p` removed. -/
noncomputable def dualCoord (g : Parameters) (x : ℝ) : ℝ := |x| ^ (g.p - 2) * x

@[simp] theorem dualCoord_zero (g : Parameters) : g.dualCoord 0 = 0 := by
  simp [dualCoord]

@[simp] theorem dualCoord_one (g : Parameters) : g.dualCoord 1 = 1 := by
  simp [dualCoord]

theorem dualCoord_neg (g : Parameters) (x : ℝ) : g.dualCoord (-x) = -g.dualCoord x := by
  simp [dualCoord]

theorem dualCoord_of_pos (g : Parameters) {x : ℝ} (hx : 0 < x) :
    g.dualCoord x = x ^ (g.p - 1) := by
  rw [dualCoord, abs_of_pos hx]
  conv_lhs => rhs; rw [← Real.rpow_one x]
  rw [← Real.rpow_add hx]
  congr 1
  ring

theorem dualCoord_of_neg (g : Parameters) {x : ℝ} (hx : x < 0) :
    g.dualCoord x = -((-x) ^ (g.p - 1)) := by
  have h := g.dualCoord_of_pos (neg_pos.mpr hx)
  rw [g.dualCoord_neg] at h
  linarith

theorem dualCoord_pos (g : Parameters) {x : ℝ} (hx : 0 < x) : 0 < g.dualCoord x := by
  rw [g.dualCoord_of_pos hx]
  exact Real.rpow_pos_of_pos hx _

theorem dualCoord_strictMono (g : Parameters) : StrictMono g.dualCoord := by
  intro x y hxy
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rcases lt_trichotomy y 0 with hy | rfl | hy
    · rw [g.dualCoord_of_neg hx, g.dualCoord_of_neg hy]
      exact neg_lt_neg (Real.rpow_lt_rpow (by linarith) (by linarith)
        (sub_pos.mpr g.one_lt_p))
    · rw [dualCoord_zero, g.dualCoord_of_neg hx]
      exact neg_neg_of_pos (Real.rpow_pos_of_pos (neg_pos.mpr hx) _)
    · rw [g.dualCoord_of_neg hx, g.dualCoord_of_pos hy]
      exact (neg_neg_of_pos (Real.rpow_pos_of_pos (neg_pos.mpr hx) _)).trans
        (Real.rpow_pos_of_pos hy _)
  · simpa using g.dualCoord_pos hxy
  · rw [g.dualCoord_of_pos hx, g.dualCoord_of_pos (hx.trans hxy)]
    exact Real.rpow_lt_rpow hx.le hxy (sub_pos.mpr g.one_lt_p)

private theorem convexOn_abs_rpow_affine (g : Parameters) (u v : ℝ) :
    ConvexOn ℝ univ (fun t : ℝ => |u + t * v| ^ g.p) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have heq : u + (a * x + b * y) * v = a * (u + x * v) + b * (u + y * v) := by
    calc
      _ = (a + b) * u + (a * x + b * y) * v := by rw [hab, one_mul]
      _ = _ := by ring
  rw [heq]
  calc
    _ ≤ (a * |u + x * v| + b * |u + y * v|) ^ g.p := by
      apply Real.rpow_le_rpow (abs_nonneg _)
      · simpa [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using
          abs_add_le (a * (u + x * v)) (b * (u + y * v))
      · linarith [g.one_lt_p]
    _ ≤ _ := (convexOn_rpow g.one_lt_p.le).2
      (abs_nonneg _) (abs_nonneg _) ha hb hab

theorem convexOn_energy_line (g : Parameters) (v w : ℝ × ℝ) :
    ConvexOn ℝ univ (fun t : ℝ => g.energy (v + t • w)) := by
  exact (convexOn_abs_rpow_affine g v.1 w.1).add
    (convexOn_abs_rpow_affine g v.2 w.2)

theorem hasDerivAt_energy_line (g : Parameters) (v w : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => g.energy (v + t • w))
      (g.p * (g.dualCoord v.1 * w.1 + g.dualCoord v.2 * w.2)) 0 := by
  have hx := (hasDerivAt_abs_rpow (v.1 + id 0 * w.1) g.one_lt_p).comp 0
    (((hasDerivAt_id (0 : ℝ)).mul_const w.1).const_add v.1)
  have hy := (hasDerivAt_abs_rpow (v.2 + id 0 * w.2) g.one_lt_p).comp 0
    (((hasDerivAt_id (0 : ℝ)).mul_const w.2).const_add v.2)
  convert hx.add hy using 1
  · ext t
    rfl
  · simp [dualCoord]
    ring

/-- The supporting-tangent equation is equivalent to global distance minimization. -/
theorem energy_min_iff (g : Parameters) (v w : ℝ × ℝ) :
    (∀ t : ℝ, g.energy v ≤ g.energy (v + t • w)) ↔
      g.dualCoord v.1 * w.1 + g.dualCoord v.2 * w.2 = 0 := by
  have hd := g.hasDerivAt_energy_line v w
  constructor
  · intro h
    have hmin : IsLocalMin (fun t : ℝ => g.energy (v + t • w)) 0 := by
      filter_upwards [] with t
      simpa using h t
    have hz := hmin.hasDerivAt_eq_zero hd
    exact (mul_eq_zero.mp hz).resolve_left (by linarith [g.one_lt_p])
  · intro h t
    rw [h, mul_zero] at hd
    have hmin := (g.convexOn_energy_line v w).isMinOn_of_rightDeriv_eq_zero
      (x := 0) (by simp) (hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi 0))
    simpa using hmin (mem_univ t)

/-- The standard normed p-plane, with the paper's real exponent. -/
abbrev Plane (g : Parameters) := WithLp (ENNReal.ofReal g.p) (ℝ × ℝ)

instance (g : Parameters) : Fact (1 ≤ ENNReal.ofReal g.p) :=
  ⟨by simpa using ENNReal.ofReal_le_ofReal g.one_lt_p.le⟩

theorem norm_eq_energy (g : Parameters) (v : ℝ × ℝ) :
    ‖WithLp.toLp (ENNReal.ofReal g.p) v‖ = g.energy v ^ (1 / g.p) := by
  have hp : 0 < g.p := zero_lt_one.trans g.one_lt_p
  simpa [energy, ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs] using
    WithLp.prod_norm_eq_add (p := ENNReal.ofReal g.p)
      (by simpa [ENNReal.toReal_ofReal hp.le] using hp)
      (WithLp.toLp (ENNReal.ofReal g.p) v)

/-- Birkhoff normality: the origin is a nearest point on the line spanned by `w`. -/
def IsNormal (g : Parameters) (v w : ℝ × ℝ) : Prop :=
  ∀ t : ℝ, ‖WithLp.toLp (ENNReal.ofReal g.p) v‖ ≤
    ‖WithLp.toLp (ENNReal.ofReal g.p) (v + t • w)‖

theorem isNormal_iff (g : Parameters) (v w : ℝ × ℝ) :
    g.IsNormal v w ↔ g.dualCoord v.1 * w.1 + g.dualCoord v.2 * w.2 = 0 := by
  rw [← g.energy_min_iff]
  unfold IsNormal
  simp only [g.norm_eq_energy]
  apply forall_congr'
  intro t
  exact Real.rpow_le_rpow_iff (by unfold energy; positivity)
    (by unfold energy; positivity) (one_div_pos.mpr (zero_lt_one.trans g.one_lt_p))

theorem dualCoord_normalSlope (g : Parameters) {m : ℝ} (hm : m ≠ 0) :
    g.dualCoord (g.normalSlope m) = -1 / m := by
  have he : (-g.exponent) * (g.p - 1) = -1 := by
    unfold exponent
    field_simp [(sub_pos.mpr g.one_lt_p).ne']
  rcases lt_or_gt_of_ne hm with hm | hm
  · rw [g.dualCoord_of_pos (g.normalSlope_pos_of_neg hm), g.normalSlope_of_neg hm,
      ← Real.rpow_mul (neg_pos.mpr hm).le, he, Real.rpow_neg_one]
    simp [div_eq_mul_inv]
  · rw [g.dualCoord_of_neg (g.normalSlope_neg_of_pos hm), g.normalSlope_of_pos hm,
      neg_neg, ← Real.rpow_mul hm.le, he, Real.rpow_neg_one]
    simp [div_eq_mul_inv]

/-- Lemma 3.1, with uniqueness, for every finite nonzero input slope. -/
theorem isNormal_finite_iff (g : Parameters) {m : ℝ} (hm : m ≠ 0) (n : ℝ) :
    g.IsNormal (1, n) (1, m) ↔ n = g.normalSlope m := by
  rw [g.isNormal_iff]
  simp only [dualCoord_one, one_mul]
  constructor
  · intro h
    apply g.dualCoord_strictMono.injective
    rw [g.dualCoord_normalSlope hm]
    apply (eq_div_iff hm).mpr
    linarith
  · rintro rfl
    rw [g.dualCoord_normalSlope hm]
    field_simp
    norm_num

theorem dualCoord_mul (g : Parameters) (a x : ℝ) :
    g.dualCoord (a * x) = (|a| ^ (g.p - 2) * a) * g.dualCoord x := by
  simp only [dualCoord, abs_mul, Real.mul_rpow (abs_nonneg a) (abs_nonneg x)]
  ring

/-- The normality condition holds at every point on the normal line. -/
theorem IsNormal.smul (g : Parameters) {v w : ℝ × ℝ} (h : g.IsNormal v w) (a b : ℝ) :
    g.IsNormal (a • v) (b • w) := by
  rw [g.isNormal_iff] at h ⊢
  change g.dualCoord (a * v.1) * (b * w.1) +
    g.dualCoord (a * v.2) * (b * w.2) = 0
  rw [g.dualCoord_mul, g.dualCoord_mul]
  calc
    _ = (|a| ^ (g.p - 2) * a) * b *
        (g.dualCoord v.1 * w.1 + g.dualCoord v.2 * w.2) := by ring
    _ = 0 := by rw [h, mul_zero]

/-- The actual infimum distance to the entire line is attained at the origin. -/
theorem IsNormal.infDist (g : Parameters) {v w : ℝ × ℝ} (h : g.IsNormal v w) :
    Metric.infDist (WithLp.toLp (ENNReal.ofReal g.p) v)
      (Set.range (fun t : ℝ => WithLp.toLp (ENNReal.ofReal g.p) (t • w))) =
      ‖WithLp.toLp (ENNReal.ofReal g.p) v‖ := by
  apply le_antisymm
  · simpa using Metric.infDist_le_dist_of_mem
      (show (0 : g.Plane) ∈ Set.range
        (fun t : ℝ => WithLp.toLp (ENNReal.ofReal g.p) (t • w)) from ⟨0, by simp⟩)
  · apply (Metric.le_infDist (Set.range_nonempty _)).mpr
    rintro _ ⟨t, rfl⟩
    rw [dist_eq_norm]
    change ‖WithLp.toLp (ENNReal.ofReal g.p) v‖ ≤
      ‖WithLp.toLp (ENNReal.ofReal g.p) (v - t • w)‖
    simpa only [sub_eq_add_neg, neg_smul] using h (-t)

/-- Swapping coordinates is an isometry for every exponent under consideration. -/
def swapIsometry (g : Parameters) : g.Plane ≃ᵢ g.Plane :=
  IsometryEquiv.withLpProdComm _ ℝ ℝ

/-- Reflecting one coordinate is also an isometry; rotations are not used. -/
def reflectIsometry (g : Parameters) : g.Plane ≃ᵢ g.Plane :=
  (IsometryEquiv.refl ℝ).withLpProdCongr _ (IsometryEquiv.neg ℝ)

theorem isNormal_swap_iff (g : Parameters) (v w : ℝ × ℝ) :
    g.IsNormal (v.2, v.1) (w.2, w.1) ↔ g.IsNormal v w := by
  simp only [g.isNormal_iff, add_comm]

theorem isNormal_reflect_iff (g : Parameters) (v w : ℝ × ℝ) :
    g.IsNormal (v.1, -v.2) (w.1, -w.2) ↔ g.IsNormal v w := by
  simp only [g.isNormal_iff, g.dualCoord_neg, neg_mul_neg]

end Parameters

namespace Direction

/-- A nonzero spanning vector, including a separate vertical case. -/
def vector : Direction → ℝ × ℝ
  | finite m => (1, m)
  | vertical => (0, 1)

theorem vector_ne_zero (d : Direction) : d.vector ≠ 0 := by
  cases d <;> simp [vector, Prod.ext_iff]

/-- The geometric line represented by a direction in the standard p-plane. -/
def line (g : Parameters) (d : Direction) : Set g.Plane :=
  Set.range (fun t : ℝ => WithLp.toLp (ENNReal.ofReal g.p) (t • d.vector))

/-- Lemma 3.1 and the axis cases: the defined map is the unique geometric normal. -/
theorem isNormal_iff_eq_next (g : Parameters) (d e : Direction) :
    g.IsNormal e.vector d.vector ↔ e = next g d := by
  cases d with
  | vertical =>
    cases e with
    | vertical => simp [Parameters.isNormal_iff, vector]
    | finite n =>
      simp only [Parameters.isNormal_iff, vector, mul_zero, mul_one, zero_add,
        next_vertical, finite.injEq]
      exact ⟨fun h => g.dualCoord_strictMono.injective (h.trans g.dualCoord_zero.symm),
        fun h => h ▸ g.dualCoord_zero⟩
  | finite m =>
    by_cases hm : m = 0
    · subst m
      cases e <;> simp [Parameters.isNormal_iff, vector]
    · rw [next_finite g hm]
      cases e with
      | vertical => simp [Parameters.isNormal_iff, vector, hm]
      | finite n => simpa only [vector, finite.injEq] using g.isNormal_finite_iff hm n

/-- Every step of the actual direction iteration takes a geometric normal. -/
theorem iterate_isNormal (g : Parameters) (d : Direction) (n : ℕ) :
    g.IsNormal (iterate g d (n + 1)).vector (iterate g d n).vector :=
  (isNormal_iff_eq_next g _ _).mpr rfl

/-- Every point of the new line has the origin as a nearest point on the old line. -/
theorem next_infDist (g : Parameters) (d : Direction) (a : ℝ) :
    Metric.infDist (WithLp.toLp (ENNReal.ofReal g.p) (a • (next g d).vector)) (line g d) =
      ‖WithLp.toLp (ENNReal.ofReal g.p) (a • (next g d).vector)‖ := by
  have h := Parameters.IsNormal.smul g ((isNormal_iff_eq_next g d _).mpr rfl) a 1
  simpa only [one_smul, line] using Parameters.IsNormal.infDist g h

end Direction

end FitzhughFarnsworth.Normality
