/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Normality.Radon
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# The convex unit disk with alternating p- and q-quadrants

The joined norm is constructed as the maximum of four convex functions.
Its quadrant formulas, including the axes, are the ordinary p- and q-norms.
This construction gives a global convex object before using its local tangent
formulas, avoiding an assumption that gluing convex arcs preserves convexity.
-/

@[expose] public section

namespace FitzhughFarnsworth.Normality.Radon

open Set Filter Topology

/-- The ordinary p-norm, on coordinate pairs. -/
noncomputable def length (g : Parameters) (v : ℝ × ℝ) : ℝ :=
  ‖WithLp.toLp (ENNReal.ofReal g.p) v‖

theorem length_nonneg (g : Parameters) (v : ℝ × ℝ) : 0 ≤ length g v := norm_nonneg _

theorem length_zero (g : Parameters) : length g (0, 0) = 0 := norm_zero

@[simp] theorem length_fst (g : Parameters) (x : ℝ) : length g (x, 0) = |x| := by
  simp [length, WithLp.norm_toLp_fst]

@[simp] theorem length_snd (g : Parameters) (y : ℝ) : length g (0, y) = |y| := by
  simp [length, WithLp.norm_toLp_snd]

theorem abs_fst_le_length (g : Parameters) (v : ℝ × ℝ) : |v.1| ≤ length g v :=
  WithLp.norm_fst_le ℝ (WithLp.toLp (ENNReal.ofReal g.p) v)

theorem abs_snd_le_length (g : Parameters) (v : ℝ × ℝ) : |v.2| ≤ length g v :=
  WithLp.norm_snd_le ℝ (WithLp.toLp (ENNReal.ofReal g.p) v)

theorem length_neg (g : Parameters) (v : ℝ × ℝ) : length g (-v) = length g v :=
  norm_neg _

theorem length_abs (g : Parameters) (v : ℝ × ℝ) :
    length g (|v.1|, |v.2|) = length g v := by
  simp [length, g.norm_eq_energy, Parameters.energy]

theorem length_mono (g : Parameters) {u v : ℝ × ℝ}
    (hx : |u.1| ≤ |v.1|) (hy : |u.2| ≤ |v.2|) : length g u ≤ length g v := by
  simp only [length, g.norm_eq_energy, Parameters.energy]
  apply Real.rpow_le_rpow (by positivity)
    (add_le_add (Real.rpow_le_rpow (abs_nonneg _) hx (by linarith [g.one_lt_p]))
      (Real.rpow_le_rpow (abs_nonneg _) hy (by linarith [g.one_lt_p])))
    (one_div_nonneg.mpr (zero_lt_one.trans g.one_lt_p).le)

/-- The p-norm of the part of a vector in a specified signed quadrant. -/
noncomputable def clippedNorm (g : Parameters) (sx sy : ℝ) (v : ℝ × ℝ) : ℝ :=
  length g (max (sx * v.1) 0, max (sy * v.2) 0)

theorem convexOn_clippedNorm (g : Parameters) (sx sy : ℝ) :
    ConvexOn ℝ univ (clippedNorm g sx sy) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  let U : g.Plane := WithLp.toLp _ (max (sx * u.1) 0, max (sy * u.2) 0)
  let V : g.Plane := WithLp.toLp _ (max (sx * v.1) 0, max (sy * v.2) 0)
  have hcoord (s x y : ℝ) : max (s * (a * x + b * y)) 0 ≤
      a * max (s * x) 0 + b * max (s * y) 0 := by
    apply max_le
    · nlinarith [mul_le_mul_of_nonneg_left (le_max_left (s * x) 0) ha,
        mul_le_mul_of_nonneg_left (le_max_left (s * y) 0) hb]
    · positivity
  calc
    _ ≤ ‖a • U + b • V‖ := by
      apply length_mono g
      · change |max (sx * (a * u.1 + b * v.1)) 0| ≤
          |a * max (sx * u.1) 0 + b * max (sx * v.1) 0|
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
        exact hcoord sx u.1 v.1
      · change |max (sy * (a * u.2 + b * v.2)) 0| ≤
          |a * max (sy * u.2) 0 + b * max (sy * v.2) 0|
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
        exact hcoord sy u.2 v.2
    _ ≤ a • clippedNorm g sx sy u + b • clippedNorm g sx sy v :=
      (convexOn_univ_norm : ConvexOn ℝ univ (norm : g.Plane → ℝ)).2
        (mem_univ U) (mem_univ V) ha hb hab

/-- A global norm whose alternating quadrants come from the two specified exponents. -/
noncomputable def joinedNorm (g h : Parameters) (v : ℝ × ℝ) : ℝ :=
  max (clippedNorm g 1 1 v) (max (clippedNorm g (-1) (-1) v)
    (max (clippedNorm h (-1) 1 v) (clippedNorm h 1 (-1) v)))

theorem convexOn_joinedNorm (g h : Parameters) : ConvexOn ℝ univ (joinedNorm g h) :=
  (convexOn_clippedNorm g 1 1).sup ((convexOn_clippedNorm g (-1) (-1)).sup
    ((convexOn_clippedNorm h (-1) 1).sup (convexOn_clippedNorm h 1 (-1))))

theorem joinedNorm_first (g h : Parameters) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    joinedNorm g h (x, y) = length g (x, y) := by
  have hx' : |x| ≤ length g (x, y) := abs_fst_le_length g (x, y)
  have hy' : |y| ≤ length g (x, y) := abs_snd_le_length g (x, y)
  simp only [joinedNorm, clippedNorm, one_mul, neg_one_mul, max_eq_left hx,
    max_eq_left hy, max_eq_right (neg_nonpos.mpr hx), max_eq_right (neg_nonpos.mpr hy),
    length_fst, length_snd, abs_zero]
  exact max_eq_left (max_le (length_nonneg g _) (max_le hy' hx'))

theorem joinedNorm_second (g h : Parameters) {x y : ℝ} (hx : x ≤ 0) (hy : 0 ≤ y) :
    joinedNorm g h (x, y) = length h (x, y) := by
  have hx' : |x| ≤ length h (x, y) := abs_fst_le_length h (x, y)
  have hy' : |y| ≤ length h (x, y) := abs_snd_le_length h (x, y)
  have he : length h (-x, y) = length h (x, y) := by
    simp [length, Parameters.norm_eq_energy, Parameters.energy]
  simp only [joinedNorm, clippedNorm, one_mul, neg_one_mul, max_eq_right hx,
    max_eq_left hy, max_eq_left (neg_nonneg.mpr hx), max_eq_right (neg_nonpos.mpr hy),
    length_fst, length_snd, abs_zero, abs_neg, he]
  rw [max_eq_left (length_nonneg h _), max_eq_right hx', max_eq_right hy']

theorem joinedNorm_neg (g h : Parameters) (v : ℝ × ℝ) :
    joinedNorm g h (-v) = joinedNorm g h v := by
  rcases v with ⟨x, y⟩
  change joinedNorm g h (-x, -y) = joinedNorm g h (x, y)
  simp only [joinedNorm, clippedNorm, one_mul, neg_one_mul, neg_neg]
  simp only [max_comm, max_left_comm]

theorem joinedNorm_quadrant (g h : Parameters) (v : ℝ × ℝ) :
    joinedNorm g h v = if 0 ≤ v.1 * v.2 then length g v else length h v := by
  rcases v with ⟨x, y⟩
  rcases le_total 0 x with hx | hx
  · rcases le_total 0 y with hy | hy
    · rw [joinedNorm_first g h hx hy, ite_eq_left (mul_nonneg hx hy)]
    · have he := joinedNorm_second g h (neg_nonpos.mpr hx) (neg_nonneg.mpr hy)
      rw [← show -(x, y) = (-x, -y) by rfl, joinedNorm_neg, length_neg] at he
      by_cases hz : 0 ≤ x * y
      · have hzero : x = 0 ∨ y = 0 := mul_eq_zero.mp (le_antisymm
          (mul_nonpos_of_nonneg_of_nonpos hx hy) hz)
        rcases hzero with rfl | rfl <;> simp [he, length_fst, length_snd]
      · simpa only [ite_eq_right hz] using he
  · rcases le_total 0 y with hy | hy
    · by_cases hz : 0 ≤ x * y
      · have hzero : x = 0 ∨ y = 0 := mul_eq_zero.mp (le_antisymm
          (mul_nonpos_of_nonpos_of_nonneg hx hy) hz)
        rcases hzero with rfl | rfl <;> simp [joinedNorm_second g h hx hy]
      · rw [joinedNorm_second g h hx hy, ite_eq_right hz]
    · have he := joinedNorm_first g h (neg_nonneg.mpr hx) (neg_nonneg.mpr hy)
      rw [← show -(x, y) = (-x, -y) by rfl, joinedNorm_neg, length_neg] at he
      simpa only [ite_eq_left (mul_nonneg_of_nonpos_of_nonpos hx hy)] using he

/-- The actual joined disk, rather than a definition by its desired normal map. -/
def disk (g h : Parameters) : Set (ℝ × ℝ) := {v | joinedNorm g h v ≤ 1}

theorem convex_disk (g h : Parameters) : Convex ℝ (disk g h) := by
  simpa only [disk, Set.sep_univ] using (convexOn_joinedNorm g h).convex_le 1

theorem disk_centrally_symmetric (g h : Parameters) (v : ℝ × ℝ) :
    -v ∈ disk g h ↔ v ∈ disk g h := by simp only [disk, mem_ofPred_eq, joinedNorm_neg]

theorem length_le_one_iff (g : Parameters) (v : ℝ × ℝ) :
    length g v ≤ 1 ↔ g.energy v ≤ 1 := by
  rw [length, g.norm_eq_energy]
  simpa only [Real.one_rpow] using Real.rpow_le_rpow_iff
    (by dsimp [Parameters.energy]; positivity : 0 ≤ g.energy v) zero_le_one
    (one_div_pos.mpr (zero_lt_one.trans g.one_lt_p))

/-- The unit disk has precisely the p- and q-pieces specified in Theorem 4.1. -/
theorem mem_disk_iff (g h : Parameters) (v : ℝ × ℝ) :
    v ∈ disk g h ↔ if 0 ≤ v.1 * v.2 then g.energy v ≤ 1 else h.energy v ≤ 1 := by
  simp only [disk, mem_ofPred_eq, joinedNorm_quadrant]
  split <;> exact length_le_one_iff _ _

theorem length_smul (g : Parameters) (a : ℝ) (v : ℝ × ℝ) :
    length g (a • v) = |a| * length g v := norm_smul a (WithLp.toLp _ v)

theorem joinedNorm_smul (g h : Parameters) (a : ℝ) (v : ℝ × ℝ) :
    joinedNorm g h (a • v) = |a| * joinedNorm g h v := by
  by_cases ha : a = 0
  · subst a
    simp [joinedNorm_quadrant, length]
  · have hs : 0 ≤ (a • v).1 * (a • v).2 ↔ 0 ≤ v.1 * v.2 := by
      change 0 ≤ (a * v.1) * (a * v.2) ↔ _
      rw [show (a * v.1) * (a * v.2) = a ^ 2 * (v.1 * v.2) by ring]
      exact mul_nonneg_iff_of_pos_left (sq_pos_of_ne_zero ha)
    simp only [joinedNorm_quadrant, hs]
    split <;> exact length_smul _ _ _

theorem joinedNorm_nonneg (g h : Parameters) (v : ℝ × ℝ) : 0 ≤ joinedNorm g h v := by
  rw [joinedNorm_quadrant]
  split <;> exact length_nonneg _ _

@[simp] theorem joinedNorm_eq_zero_iff (g h : Parameters) (v : ℝ × ℝ) :
    joinedNorm g h v = 0 ↔ v = 0 := by
  rw [joinedNorm_quadrant]
  split <;> simp only [length, norm_eq_zero, WithLp.toLp_eq_zero]

theorem joinedNorm_add_le (g h : Parameters) (v w : ℝ × ℝ) :
    joinedNorm g h (v + w) ≤ joinedNorm g h v + joinedNorm g h w := by
  have hc := (convexOn_joinedNorm g h).2 (mem_univ v) (mem_univ w)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num)
  rw [← smul_add, joinedNorm_smul] at hc
  norm_num [smul_eq_mul] at hc
  linarith

/-- A separate type prevents replacing the usual metric on coordinate pairs. -/
def Plane (_g : Parameters) := ℝ × ℝ

instance (g : Parameters) : AddCommGroup (Plane g) := inferInstanceAs (AddCommGroup (ℝ × ℝ))

instance (g : Parameters) : Module ℝ (Plane g) := inferInstanceAs (Module ℝ (ℝ × ℝ))

noncomputable instance (g : Parameters) : Norm (Plane g) := ⟨joinedNorm g g.conjugate⟩

theorem normCore (g : Parameters) : NormedSpace.Core ℝ (Plane g) where
  norm_nonneg := joinedNorm_nonneg g g.conjugate
  norm_smul := joinedNorm_smul g g.conjugate
  norm_triangle := joinedNorm_add_le g g.conjugate
  norm_eq_zero_iff := joinedNorm_eq_zero_iff g g.conjugate

noncomputable instance (g : Parameters) : NormedAddCommGroup (Plane g) :=
  NormedAddCommGroup.ofCore (normCore g)

noncomputable instance (g : Parameters) : NormedSpace ℝ (Plane g) :=
  NormedSpace.ofCore (normCore g)

/-- Cartesian coordinates in the constructed normed plane. -/
def coords {g : Parameters} (v : Plane g) : ℝ × ℝ := v

/-- Insert Cartesian coordinates into the constructed normed plane. -/
def ofCoords (g : Parameters) (v : ℝ × ℝ) : Plane g := v

theorem norm_ofCoords (g : Parameters) (v : ℝ × ℝ) :
    ‖ofCoords g v‖ = joinedNorm g g.conjugate v := rfl

theorem dist_ofCoords (g : Parameters) (v w : ℝ × ℝ) :
    dist (ofCoords g v) (ofCoords g w) = joinedNorm g g.conjugate (v - w) := by
  rw [dist_eq_norm]
  rfl

/-- Its standard closed unit ball is exactly the constructed convex disk. -/
theorem mem_closedBall_iff (g : Parameters) (v : Plane g) :
    v ∈ Metric.closedBall (0 : Plane g) 1 ↔ coords v ∈ disk g g.conjugate := by
  rw [Metric.mem_closedBall, dist_zero_right]
  rfl

end FitzhughFarnsworth.Normality.Radon
