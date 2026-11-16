/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Normality.Circumference
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The circumference integrals are standard path lengths

Connect the regular octant charts to mathlib's `Manifold.pathELength`, in the
ordinary p-plane and in the actual joined normed plane. Thus the circumference
comparison uses lengths in the specified metrics, not Euclidean arc lengths.
-/

@[expose] public section

namespace FitzhughFarnsworth.Normality.Circumference

open Set MeasureTheory
open scoped Manifold ENNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem pathELength_eq_integral_norm {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f v : ℝ → E}
    (hv : ContinuousOn v (Icc 0 1)) (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (v t) t) :
    Manifold.pathELength 𝓘(ℝ, E) f 0 1 = ENNReal.ofReal (∫ t : ℝ in 0..1, ‖v t‖) := by
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  calc
    _ = ∫⁻ t in Icc (0 : ℝ) 1, ‖v t‖ₑ := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      dsimp only
      rw [mfderiv_eq_fderiv, (hd t ht).hasFDerivAt.fderiv]
      change ‖(1 : ℝ) • v t‖ₑ = ‖v t‖ₑ
      rw [one_smul]
    _ = ENNReal.ofReal (∫ t in Icc (0 : ℝ) 1, ‖v t‖) :=
      (ofReal_integral_norm_eq_lintegral_eNorm hv.integrableOn_Icc).symm
    _ = _ := by rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]

/-- The octant integral equals mathlib's path length in the specified p-dependent norm. -/
theorem octant_pathELength (g h : Parameters) :
    Manifold.pathELength 𝓘(ℝ, h.Plane)
      (fun t => WithLp.toLp (ENNReal.ofReal h.p) (octant g t)) 0 1 =
      ENNReal.ofReal (octantLength g h) := by
  apply pathELength_eq_integral_norm
  · exact (WithLp.prod_continuous_toLp _ ℝ ℝ).comp_continuousOn (continuousOn_velocity g)
  · exact fun t ht => hasDerivAt_normed_octant g h ht.1

theorem selfPerimeter_eq_pathELength (g : Parameters) :
    selfPerimeter g = 8 * (Manifold.pathELength 𝓘(ℝ, g.Plane)
      (fun t => WithLp.toLp (ENNReal.ofReal g.p) (octant g t)) 0 1).toReal := by
  rw [octant_pathELength, ENNReal.toReal_ofReal]
  · rfl
  · exact intervalIntegral.integral_nonneg zero_le_one (fun _ _ => Radon.length_nonneg _ _)

/-- The coordinate identification is continuous and linear in the constructed norm. -/
noncomputable def joinedCoordinates (g : Parameters) : (ℝ × ℝ) →L[ℝ] Radon.Plane g :=
  LinearMap.toContinuousLinearMap {
    toFun := Radon.ofCoords g
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- First p-octant, now a path in the actual joined metric. -/
noncomputable def joinedOctant (g : Parameters) (t : ℝ) : Radon.Plane g :=
  joinedCoordinates g (octant g t)

/-- Adjacent q-octant, reflected into the second quadrant of the joined unit circle. -/
noncomputable def reflectedOctant (g : Parameters) (t : ℝ) : Radon.Plane g :=
  joinedCoordinates g (-(octant g.conjugate t).1, (octant g.conjugate t).2)

theorem joinedOctant_norm_one (g : Parameters) {t : ℝ} (ht : 0 ≤ t) :
    ‖joinedOctant g t‖ = 1 := by
  change Radon.joinedNorm g g.conjugate (radius g t, t * radius g t) = 1
  rw [Radon.joinedNorm_first g g.conjugate (radius_pos g ht).le
    (mul_nonneg ht (radius_pos g ht).le)]
  exact octant_norm_one g ht

theorem reflectedOctant_norm_one (g : Parameters) {t : ℝ} (ht : 0 ≤ t) :
    ‖reflectedOctant g t‖ = 1 := by
  change Radon.joinedNorm g g.conjugate (-radius g.conjugate t, t * radius g.conjugate t) = 1
  rw [Radon.joinedNorm_second g g.conjugate (neg_nonpos.mpr (radius_pos g.conjugate ht).le)
    (mul_nonneg ht (radius_pos g.conjugate ht).le)]
  have h := octant_norm_one g.conjugate ht
  simpa only [Radon.length, Parameters.norm_eq_energy, Parameters.energy, octant, abs_neg] using h

theorem joinedOctant_pathELength (g : Parameters) :
    Manifold.pathELength 𝓘(ℝ, Radon.Plane g) (joinedOctant g) 0 1 =
      ENNReal.ofReal (∫ t : ℝ in 0..1, Radon.joinedNorm g g.conjugate (velocity g t)) := by
  apply pathELength_eq_integral_norm
  · exact (joinedCoordinates g).continuous.comp_continuousOn (continuousOn_velocity g)
  · intro t ht
    exact (joinedCoordinates g).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_octant g ht.1)

theorem reflectedOctant_pathELength (g : Parameters) :
    Manifold.pathELength 𝓘(ℝ, Radon.Plane g) (reflectedOctant g) 0 1 =
      ENNReal.ofReal (∫ t : ℝ in 0..1, Radon.joinedNorm g g.conjugate
        (-(velocity g.conjugate t).1, (velocity g.conjugate t).2)) := by
  apply pathELength_eq_integral_norm
  · exact (joinedCoordinates g).continuous.comp_continuousOn
      ((continuousOn_velocity g.conjugate).fst.neg.prodMk
        (continuousOn_velocity g.conjugate).snd)
  · intro t ht
    have hd : HasDerivAt (fun s => (-(octant g.conjugate s).1, (octant g.conjugate s).2))
        (-(velocity g.conjugate t).1, (velocity g.conjugate t).2) t := by
      convert (hasDerivAt_radius g.conjugate ht.1).neg.prodMk
        (hasDerivAt_height g.conjugate ht.1) using 1
      · rfl
      · ext <;> simp [velocity, mul_comm]
    exact (joinedCoordinates g).hasFDerivAt.comp_hasDerivAt t hd

/-- The joined circumference is the sum of the eight standard path lengths. -/
theorem joinedPerimeter_eq_pathELength (g : Parameters) :
    joinedPerimeter g =
      4 * (Manifold.pathELength 𝓘(ℝ, Radon.Plane g) (joinedOctant g) 0 1).toReal +
      4 * (Manifold.pathELength 𝓘(ℝ, Radon.Plane g) (reflectedOctant g) 0 1).toReal := by
  rw [joinedOctant_pathELength, reflectedOctant_pathELength,
    ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg zero_le_one
      (fun t _ => Radon.joinedNorm_nonneg _ _ _)),
    ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg zero_le_one
      (fun t _ => Radon.joinedNorm_nonneg _ _ _))]
  rfl

end FitzhughFarnsworth.Normality.Circumference
