/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.IteratedMidsets.Algebra
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Euclidean interpretations

The taxicab metric determines the midsets. Euclidean inner products and
rotations are used only to interpret the paper's orthogonality and angle claims.
In particular, a 45-degree rotation is not asserted to preserve taxicab distance.
-/

@[expose] public section

namespace FitzhughFarnsworth

/-- Read the coordinates of a taxicab point as a vector with the Euclidean norm. -/
noncomputable def euclideanVector (p : Point) : EuclideanSpace ℝ (Fin 2) := !₂[p.x, p.y]

theorem euclidean_inner (p q : Point) :
    inner ℝ (euclideanVector p) (euclideanVector q) = p.x * q.x + p.y * q.y := by
  simp [euclideanVector, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  ring

/-- The usual Euclidean rotation, expressed on the taxicab plane's point type. -/
noncomputable def rotate (θ : ℝ) (p : Point) : Point :=
  Point.mk (Real.cos θ * p.x - Real.sin θ * p.y)
    (Real.sin θ * p.x + Real.cos θ * p.y)

theorem rotate_preserves_euclidean_inner (θ : ℝ) (p q : Point) :
    inner ℝ (euclideanVector (rotate θ p)) (euclideanVector (rotate θ q)) =
      inner ℝ (euclideanVector p) (euclideanVector q) := by
  simp only [euclidean_inner, rotate, Point.mk_x, Point.mk_y]
  calc
    _ = (Real.sin θ ^ 2 + Real.cos θ ^ 2) * (p.x * q.x + p.y * q.y) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, one_mul]

/-- The coordinate form of a quarter-right-angle rotation, up to a scalar factor. -/
private noncomputable def scaledTurn (c : ℝ) (p : Point) : Point :=
  Point.mk (c * (p.x - p.y)) (c * (p.x + p.y))

private theorem scaledTurn_slopeLine (m c : ℝ) (hm : m ≠ 1) (hc : c ≠ 0) :
    scaledTurn c '' slopeLine m = slopeLine ((m + 1) / (1 - m)) := by
  have hm' : 1 - m ≠ 0 := sub_ne_zero.mpr (Ne.symm hm)
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    change p.y = m * p.x at hp
    change c * (p.x + p.y) = (m + 1) / (1 - m) * (c * (p.x - p.y))
    rw [hp]
    field_simp
    ring
  · intro hq
    change q.y = (m + 1) / (1 - m) * q.x at hq
    refine ⟨Point.mk (q.x / (c * (1 - m))) (m * (q.x / (c * (1 - m)))), rfl, ?_⟩
    ext <;> dsimp [scaledTurn]
    · field_simp
    · rw [hq]
      field_simp
      ring

/-- A rotation by π/4 maps a non-diagonal finite-slope line to this slope. -/
theorem rotate_pi_div_four_slopeLine (m : ℝ) (hm : m ≠ 1) :
    rotate (Real.pi / 4) '' slopeLine m = slopeLine ((m + 1) / (1 - m)) := by
  have hrot : rotate (Real.pi / 4) = scaledTurn (Real.sqrt 2 / 2) := by
    funext p
    ext <;> simp [rotate, scaledTurn, Real.cos_pi_div_four, Real.sin_pi_div_four] <;> ring
  rw [hrot]
  exact scaledTurn_slopeLine m _ hm (ne_of_gt (by positivity))

namespace SlopePair

/-- The geometric union of the two origin lines represented by a slope pair. -/
def carrier (s : SlopePair) : Set Point := slopeLine s.a ∪ slopeLine s.b

theorem orthogonal_iff_euclidean_inner (s : SlopePair) :
    s.Orthogonal ↔
      inner ℝ (euclideanVector (Point.mk 1 s.a)) (euclideanVector (Point.mk 1 s.b)) = 0 := by
  simp [Orthogonal, euclidean_inner]

/-- The 45-degree assertion in Theorem 2, for either orientation of Configuration 1. -/
theorem midset_eq_rotate_of_orthogonal {s : SlopePair}
    (ha : |s.a| < 1) (hb : 1 < |s.b|) (ho : s.Orthogonal) :
    midset (slopeLine s.a) (slopeLine s.b) = rotate (Real.pi / 4) '' s.carrier := by
  have ha1 : s.a ≠ 1 := by intro he; norm_num [he] at ha
  have hb1 : s.b ≠ 1 := by intro he; norm_num [he] at hb
  have hbp : s.b + 1 ≠ 0 := by
    intro he
    have : s.b = -1 := by linarith
    norm_num [this] at hb
  have hbm : s.b - 1 ≠ 0 := sub_ne_zero.mpr hb1
  have ham : 1 - s.a ≠ 0 := sub_ne_zero.mpr ha1.symm
  have hab := (orthogonal_iff s).mp ho
  have hδ : s.b * (s.a - 1) / (s.b - 1) = (s.b + 1) / (1 - s.b) := by
    rw [mul_sub, mul_one, mul_comm s.b s.a, hab]
    field_simp
    ring
  have hε : s.b * (s.a + 1) / (s.b + 1) = (s.a + 1) / (1 - s.a) := by
    field_simp
    nlinarith [congrArg (fun x : ℝ => x * (s.a + 1)) hab]
  rw [midset_shallow_steep s.a s.b ha.le hb, carrier, Set.image_union,
    rotate_pi_div_four_slopeLine s.a ha1, rotate_pi_div_four_slopeLine s.b hb1, hδ, hε]
  exact Set.union_comm _ _

theorem carrier_injective_even {s t : SlopePair} (hs : s.EvenConfig) (ht : t.EvenConfig)
    (h : s.carrier = t.carrier) : s = t := by
  have ha : s.a = t.a ∨ s.a = t.b := by
    have hp : (Point.mk 1 s.a) ∈ s.carrier := by simp [carrier, slopeLine]
    rw [h] at hp
    simpa [carrier, slopeLine] using hp
  have hb : s.b = t.a ∨ s.b = t.b := by
    have hp : (Point.mk 1 s.b) ∈ s.carrier := by simp [carrier, slopeLine]
    rw [h] at hp
    simpa [carrier, slopeLine] using hp
  ext
  · rcases ha with ha | ha
    · exact ha
    · linarith [hs.1, ht.2.2]
  · rcases hb with hb | hb
    · linarith [hs.2.2, ht.1]
    · exact hb

theorem carrier_injective_odd {s t : SlopePair} (hs : s.OddConfig) (ht : t.OddConfig)
    (h : s.carrier = t.carrier) : s = t := by
  have ha : s.a = t.a ∨ s.a = t.b := by
    have hp : (Point.mk 1 s.a) ∈ s.carrier := by simp [carrier, slopeLine]
    rw [h] at hp
    simpa [carrier, slopeLine] using hp
  have hb : s.b = t.a ∨ s.b = t.b := by
    have hp : (Point.mk 1 s.b) ∈ s.carrier := by simp [carrier, slopeLine]
    rw [h] at hp
    simpa [carrier, slopeLine] using hp
  ext
  · rcases ha with ha | ha
    · exact ha
    · linarith [hs.2.1, ht.2.2]
  · rcases hb with hb | hb
    · linarith [hs.2.2, ht.2.1]
    · exact hb

theorem even_odd_carriers_ne {s t : SlopePair} (hs : s.EvenConfig) (ht : t.OddConfig) :
    s.carrier ≠ t.carrier := by
  intro he
  have hp : (Point.mk 1 s.a) ∈ s.carrier := by simp [carrier, slopeLine]
  rw [he] at hp
  have hm : s.a = t.a ∨ s.a = t.b := by simpa [carrier, slopeLine] using hp
  rcases hm with hm | hm
  · linarith [hs.1, ht.2.1]
  · linarith [hs.2.1, ht.2.2]

/-- Theorem 2 as an equality of geometric sets, in the even orientation. -/
theorem midset_midset_eq_self_iff_even {s : SlopePair} (h : s.EvenConfig) :
    midset (slopeLine s.toOdd.a) (slopeLine s.toOdd.b) = s.carrier ↔ s.Orthogonal := by
  rw [midset_eq_toEven (toOdd_config h)]
  change s.twoStep.carrier = s.carrier ↔ s.Orthogonal
  exact ⟨fun he => (twoStep_eq_self_iff h).mp (carrier_injective_even (twoStep_config h) h he),
    fun ho => congrArg carrier ((twoStep_eq_self_iff h).mpr ho)⟩

/-- Theorem 2 as an equality of geometric sets, in the odd orientation. -/
theorem midset_midset_eq_self_iff_odd {s : SlopePair} (h : s.OddConfig) :
    midset (slopeLine s.toEven.a) (slopeLine s.toEven.b) = s.carrier ↔ s.Orthogonal := by
  rw [midset_eq_toOdd (toEven_config h)]
  change s.toEven.toOdd.carrier = s.carrier ↔ s.Orthogonal
  exact ⟨fun he => (toEven_toOdd_eq_self_iff h).mp
      (carrier_injective_odd (toOdd_config (toEven_config h)) h he),
    fun ho => congrArg carrier ((toEven_toOdd_eq_self_iff h).mpr ho)⟩

/-- The angular hypotheses in Theorem 8 are exactly reciprocal slopes. -/
theorem reciprocal_angle_identities {s : SlopePair} (h : s.EvenConfig) :
    Real.arctan s.reciprocal.a = (Real.pi + Real.arctan s.b) - Real.pi / 2 ∧
      Real.pi + Real.arctan s.reciprocal.b = Real.arctan s.a + Real.pi / 2 := by
  dsimp [reciprocal]
  rw [neg_div, neg_div, one_div, one_div, Real.arctan_neg, Real.arctan_neg,
    Real.arctan_inv_of_neg (by linarith [h.2.2] : s.b < 0), Real.arctan_inv_of_pos h.1]
  constructor <;> ring

/-- The angle between the upper-half-plane rays of a canonical even pair.
It is expressed in Euclidean radians, not in a taxicab angle convention. -/
noncomputable def evenOpening (s : SlopePair) : ℝ :=
  Real.pi + Real.arctan s.b - Real.arctan s.a

theorem arctan_neg_reciprocal {a : ℝ} (ha : 0 < a) :
    Real.arctan (-1 / a) = Real.arctan a - Real.pi / 2 := by
  rw [neg_div, one_div, Real.arctan_neg, Real.arctan_inv_of_pos ha]
  ring

theorem evenOpening_eq_rightAngle_iff {s : SlopePair} (ha : 0 < s.a) :
    s.evenOpening = Real.pi / 2 ↔ s.Orthogonal := by
  rw [orthogonal_iff]
  have harc := arctan_neg_reciprocal ha
  constructor
  · intro h
    have heq : Real.arctan s.b = Real.arctan (-1 / s.a) := by
      dsimp [evenOpening] at h
      linarith
    have hb := Real.arctan_injective heq
    have hm := (eq_div_iff (ne_of_gt ha)).mp hb
    nlinarith
  · intro h
    have hb : s.b = -1 / s.a := (eq_div_iff (ne_of_gt ha)).mpr (by nlinarith)
    simp only [evenOpening, hb, harc]
    ring

theorem evenOpening_lt_rightAngle_iff {s : SlopePair} (ha : 0 < s.a) :
    s.evenOpening < Real.pi / 2 ↔ s.a * s.b < -1 := by
  have harc := arctan_neg_reciprocal ha
  have hc : s.evenOpening < Real.pi / 2 ↔
      Real.arctan s.b < Real.arctan (-1 / s.a) := by
    dsimp [evenOpening]
    constructor <;> intro h <;> linarith
  rw [hc, Real.arctan_lt_arctan_iff, lt_div_iff₀ ha, mul_comm s.b s.a]

theorem rightAngle_lt_evenOpening_iff {s : SlopePair} (ha : 0 < s.a) :
    Real.pi / 2 < s.evenOpening ↔ -1 < s.a * s.b := by
  have harc := arctan_neg_reciprocal ha
  have hc : Real.pi / 2 < s.evenOpening ↔
      Real.arctan (-1 / s.a) < Real.arctan s.b := by
    dsimp [evenOpening]
    constructor <;> intro h <;> linarith
  rw [hc, Real.arctan_lt_arctan_iff, div_lt_iff₀ ha, mul_comm s.b s.a]

theorem evenOpening_le_of_slopes {s t : SlopePair} (ha : s.a ≤ t.a) (hb : t.b ≤ s.b) :
    t.evenOpening ≤ s.evenOpening := by
  dsimp [evenOpening]
  linarith [Real.arctan_mono ha, Real.arctan_mono hb]

theorem evenOpening_lt_of_slopes {s t : SlopePair} (ha : s.a < t.a) (hb : t.b < s.b) :
    t.evenOpening < s.evenOpening := by
  dsimp [evenOpening]
  linarith [Real.arctan_strictMono ha, Real.arctan_strictMono hb]

end SlopePair
end FitzhughFarnsworth
