module

public import FitzhughFarnsworth.Dynamics.Sequence

/-!
# The Euclidean quarter-right-angle relation for every geometric two-cycle

The rotation conclusion applies to all orthogonal pairs, including the axes
and diagonal boundary cases, at any common intersection point. Rotation is
used only as a Euclidean interpretation, never as a taxicab isometry.
-/

@[expose] public section

namespace FitzhughFarnsworth
namespace Dynamics

theorem rotate_pi_div_four_diagonal :
    rotate (Real.pi / 4) '' slopeLine 1 = verticalAxis := by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (by positivity)
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    change p.y = 1 * p.x at hp
    change Real.cos (Real.pi / 4) * p.x - Real.sin (Real.pi / 4) * p.y = 0
    rw [Real.cos_pi_div_four, Real.sin_pi_div_four, hp]
    ring
  · intro hq
    change q.x = 0 at hq
    refine ⟨⟨q.y / Real.sqrt 2, q.y / Real.sqrt 2⟩, ?_, ?_⟩
    · simp [slopeLine]
    · ext <;> dsimp [rotate]
      · rw [Real.cos_pi_div_four, Real.sin_pi_div_four, hq]
        ring
      · rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
        field_simp
        ring

theorem rotate_pi_div_four_vertical :
    rotate (Real.pi / 4) '' verticalAxis = slopeLine (-1) := by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (by positivity)
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    change p.x = 0 at hp
    change Real.sin (Real.pi / 4) * p.x + Real.cos (Real.pi / 4) * p.y =
      -1 * (Real.cos (Real.pi / 4) * p.x - Real.sin (Real.pi / 4) * p.y)
    rw [Real.cos_pi_div_four, Real.sin_pi_div_four, hp]
    ring
  · intro hq
    change q.y = -1 * q.x at hq
    refine ⟨⟨0, 2 * q.y / Real.sqrt 2⟩, rfl, ?_⟩
    ext <;> dsimp [rotate]
    · rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
      field_simp
      nlinarith
    · rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
      field_simp
      ring

theorem rotate_pi_div_four_horizontal :
    rotate (Real.pi / 4) '' horizontalAxis = slopeLine 1 := by
  simpa [horizontalAxis] using rotate_pi_div_four_slopeLine 0 (by norm_num)

theorem rotate_pi_div_four_negative_diagonal :
    rotate (Real.pi / 4) '' slopeLine (-1) = horizontalAxis := by
  simpa [horizontalAxis] using rotate_pi_div_four_slopeLine (-1) (by norm_num)

/-- The rotation formula for every orthogonal finite-slope pair, including
diagonals and either ordering of the shallow and steep lines. -/
theorem midset_eq_rotate_of_orthogonal_slopes {s : SlopePair} (ho : s.Orthogonal) :
    midset (slopeLine s.a) (slopeLine s.b) = rotate (Real.pi / 4) '' s.carrier := by
  have hab : s.a * s.b = -1 := (SlopePair.orthogonal_iff s).mp ho
  have habs : |s.a| * |s.b| = 1 := by rw [← abs_mul, hab]; norm_num
  rcases lt_trichotomy |s.a| 1 with ha | ha | ha
  · have hb : 1 < |s.b| := by
      by_contra hn
      have hb : |s.b| ≤ 1 := le_of_not_gt hn
      have hm := mul_le_mul_of_nonneg_left hb (abs_nonneg s.a)
      nlinarith
    exact SlopePair.midset_eq_rotate_of_orthogonal ha hb ho
  · have ha' : s.a = 1 ∨ s.a = -1 := by
      have he : |s.a| = |(1 : ℝ)| := by simpa only [abs_one] using ha
      exact abs_eq_abs.mp he
    rcases ha' with ha' | ha'
    · have hb : s.b = -1 := by rw [ha'] at hab; linarith
      rw [SlopePair.carrier, ha', hb, midset_diagonals, Set.image_union,
        rotate_pi_div_four_diagonal, rotate_pi_div_four_negative_diagonal]
      exact Set.union_comm _ _
    · have hb : s.b = 1 := by rw [ha'] at hab; linarith
      rw [SlopePair.carrier, ha', hb, midset_comm, midset_diagonals, Set.image_union,
        rotate_pi_div_four_negative_diagonal, rotate_pi_div_four_diagonal]
  · have hb : |s.b| < 1 := by
      by_contra hn
      have hb : 1 ≤ |s.b| := le_of_not_gt hn
      have hm := mul_le_mul_of_nonneg_left hb (abs_nonneg s.a)
      nlinarith
    have hswap : (⟨s.b, s.a⟩ : SlopePair).Orthogonal := by
      change 1 + s.b * s.a = 0
      nlinarith
    calc
      midset (slopeLine s.a) (slopeLine s.b) = midset (slopeLine s.b) (slopeLine s.a) :=
        midset_comm _ _
      _ = rotate (Real.pi / 4) '' (slopeLine s.b ∪ slopeLine s.a) :=
        SlopePair.midset_eq_rotate_of_orthogonal (s := ⟨s.b, s.a⟩) hb ha hswap
      _ = rotate (Real.pi / 4) '' s.carrier := by rw [SlopePair.carrier, Set.union_comm]

namespace LinePair

theorem OrthogonalOrigin.midset_eq_rotate {P : LinePair} (h : P.OrthogonalOrigin) :
    midset P.1 P.2 = rotate (Real.pi / 4) '' P.carrier := by
  induction h with
  | slopes s h => exact midset_eq_rotate_of_orthogonal_slopes h
  | axes =>
    change midset horizontalAxis verticalAxis =
      rotate (Real.pi / 4) '' (horizontalAxis ∪ verticalAxis)
    rw [midset_axes, Set.image_union, rotate_pi_div_four_horizontal, rotate_pi_div_four_vertical]
  | swap h ih =>
    rw [carrier_swap]
    rw [midset_comm]
    exact ih

theorem OrthogonalAt.midset_eq_rotateAbout {v : Point} {P : LinePair} (h : P.OrthogonalAt v) :
    midset P.1 P.2 = rotateAbout v (Real.pi / 4) '' P.carrier := by
  obtain ⟨Q, hQ, rfl⟩ := h
  rw [carrier_map, rotateAbout_image_translate]
  change midset (translateBy v '' Q.1) (translateBy v '' Q.2) = _
  rw [← isometryEquiv_image_midset, hQ.midset_eq_rotate]

end LinePair

/-- Every geometric two-cycle consists of orthogonal pairs related by a
Euclidean rotation of π/4 around their common intersection. -/
theorem TwoCycleAt.rotate {v : Point} {P Q : LinePair} (h : TwoCycleAt v P Q) :
    Q.carrier = rotateAbout v (Real.pi / 4) '' P.carrier :=
  h.step_left.symm.trans h.orthogonal_left.midset_eq_rotateAbout

theorem TwoCycleAt.rotate_right {v : Point} {P Q : LinePair} (h : TwoCycleAt v P Q) :
    P.carrier = rotateAbout v (Real.pi / 4) '' Q.carrier :=
  h.step_right.symm.trans h.orthogonal_right.midset_eq_rotateAbout

end Dynamics
end FitzhughFarnsworth
