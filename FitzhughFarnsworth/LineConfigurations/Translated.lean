/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.LineConfigurations.Reduction
public import FitzhughFarnsworth.LineConfigurations.Euclidean

/-! # Geometric fixed cycles at arbitrary intersection points -/

@[expose] public section

namespace FitzhughFarnsworth

/-- Euclidean rotation around an arbitrary point, with translation handled by
the established taxicab isometry. The rotation itself is Euclidean only. -/
noncomputable def rotateAbout (v : Point) (θ : ℝ) (p : Point) : Point :=
  translateBy v (rotate θ ((translateBy v).symm p))

theorem rotateAbout_image_translate (v : Point) (θ : ℝ) (A : Set Point) :
    rotateAbout v θ '' (translateBy v '' A) = translateBy v '' (rotate θ '' A) := by
  simp only [Set.image_image]
  congr 1
  funext p
  simp [rotateAbout]

namespace SlopePair

theorem translated_midset_eq_toOdd {s : SlopePair} (h : s.EvenConfig) (v : Point) :
    midset (translateBy v '' slopeLine s.a) (translateBy v '' slopeLine s.b) =
      translateBy v '' s.toOdd.carrier := by
  rw [← isometryEquiv_image_midset, midset_eq_toOdd h]
  rfl

theorem translated_midset_eq_toEven {s : SlopePair} (h : s.OddConfig) (v : Point) :
    midset (translateBy v '' slopeLine s.a) (translateBy v '' slopeLine s.b) =
      translateBy v '' s.toEven.carrier := by
  rw [← isometryEquiv_image_midset, midset_eq_toEven h]
  rfl

theorem translated_midset_midset_eq_self_iff_even {s : SlopePair}
    (h : s.EvenConfig) (v : Point) :
    midset (translateBy v '' slopeLine s.toOdd.a) (translateBy v '' slopeLine s.toOdd.b) =
      translateBy v '' s.carrier ↔ s.Orthogonal := by
  rw [← isometryEquiv_image_midset]
  exact (Set.image_injective.mpr (translateBy v).injective).eq_iff.trans
    (midset_midset_eq_self_iff_even h)

theorem translated_midset_midset_eq_self_iff_odd {s : SlopePair}
    (h : s.OddConfig) (v : Point) :
    midset (translateBy v '' slopeLine s.toEven.a) (translateBy v '' slopeLine s.toEven.b) =
      translateBy v '' s.carrier ↔ s.Orthogonal := by
  rw [← isometryEquiv_image_midset]
  exact (Set.image_injective.mpr (translateBy v).injective).eq_iff.trans
    (midset_midset_eq_self_iff_odd h)

theorem translated_midset_eq_rotate_of_orthogonal {s : SlopePair}
    (ha : |s.a| < 1) (hb : 1 < |s.b|) (ho : s.Orthogonal) (v : Point) :
    midset (translateBy v '' slopeLine s.a) (translateBy v '' slopeLine s.b) =
      rotateAbout v (Real.pi / 4) '' (translateBy v '' s.carrier) := by
  rw [← isometryEquiv_image_midset, rotateAbout_image_translate,
    midset_eq_rotate_of_orthogonal ha hb ho]

end SlopePair
end FitzhughFarnsworth
