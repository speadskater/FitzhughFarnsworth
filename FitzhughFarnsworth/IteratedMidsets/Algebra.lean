/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.IteratedMidsets

/-!
# Algebra of the canonical midset iteration

Closed two-step formulas, fixed points, and reciprocal symmetry from
Fitzhugh–Farnsworth (2014), Theorems 2 and 8.
-/

@[expose] public section

namespace FitzhughFarnsworth
namespace SlopePair

theorem EvenConfig.denominator_a_pos {s : SlopePair} (h : s.EvenConfig) :
    0 < (s.b - 1) * (s.a * s.b + 1 + 2 * s.b) := by
  apply mul_pos_of_neg_of_neg <;> linarith [h.2.2, h.product_neg]

theorem EvenConfig.denominator_b_pos {s : SlopePair} (h : s.EvenConfig) :
    0 < (s.b - 1) * (s.a * s.b - 1) := by
  apply mul_pos_of_neg_of_neg <;> linarith [h.2.2, h.product_neg]

/-- Equation (13), also equation (3) in the canonical proof of Theorem 1. -/
theorem twoStep_a {s : SlopePair} (h : s.EvenConfig) :
    s.twoStep.a = s.b * (s.a + 1) * (s.a * s.b - 1) /
      ((s.b - 1) * (s.a * s.b + 1 + 2 * s.b)) := by
  have hb1 := h.b_sub_one_ne_zero
  have hbp := h.b_add_one_ne_zero
  have hd : s.a * s.b + 1 + 2 * s.b ≠ 0 := by linarith [h.2.2, h.product_neg]
  dsimp [twoStep, toOdd, toEven]
  field_simp
  ring

/-- Equation (14), also equation (4) in the canonical proof of Theorem 1. -/
theorem twoStep_b {s : SlopePair} (h : s.EvenConfig) :
    s.twoStep.b = s.b * (s.a + 1) * (s.a * s.b + 1 - 2 * s.b) /
      ((s.b - 1) * (s.a * s.b - 1)) := by
  have hb1 := h.b_sub_one_ne_zero
  have hbp := h.b_add_one_ne_zero
  have hd : s.a * s.b - 1 ≠ 0 := by linarith [h.product_neg]
  dsimp [twoStep, toOdd, toEven]
  field_simp
  ring

theorem twoStep_a_sub_a {s : SlopePair} (h : s.EvenConfig) :
    s.twoStep.a - s.a = (s.a - s.b) * (s.a * s.b + 1) /
      ((s.b - 1) * (s.a * s.b + 1 + 2 * s.b)) := by
  have hd := ne_of_gt h.denominator_a_pos
  rw [twoStep_a h]
  rw [div_sub' hd]
  congr 1
  ring

theorem twoStep_b_sub_b {s : SlopePair} (h : s.EvenConfig) :
    s.twoStep.b - s.b = s.b * (s.a - s.b) * (s.a * s.b + 1) /
      ((s.b - 1) * (s.a * s.b - 1)) := by
  have hd := ne_of_gt h.denominator_b_pos
  rw [twoStep_b h]
  rw [div_sub' hd]
  congr 1
  ring

theorem twoStep_product_add_one {s : SlopePair} (h : s.EvenConfig) :
    s.twoStep.a * s.twoStep.b + 1 =
      (s.a * s.b + 1) * ((s.a * s.b) ^ 2 + 1 - 2 * s.b ^ 2) /
        ((s.b - 1) ^ 2 * (s.a * s.b + 1 + 2 * s.b)) := by
  have hb1 := h.b_sub_one_ne_zero
  have hd1 : s.a * s.b - 1 ≠ 0 := by linarith [h.product_neg]
  have hd2 : s.a * s.b + 1 + 2 * s.b ≠ 0 := by linarith [h.2.2, h.product_neg]
  rw [twoStep_a h, twoStep_b h]
  have hn1 : s.a * s.b - 1 < 0 := by linarith [h.product_neg]
  have hn2 : s.a * s.b + 1 + 2 * s.b < 0 := by linarith [h.2.2, h.product_neg]
  have hprod := mul_pos_of_neg_of_neg hn1 hn2
  field_simp (disch := nlinarith [hprod, hn1, hn2, sq_pos_of_ne_zero hb1])
  ring

/-- In the canonical region either one of the two slope fixed-point equations
already forces Euclidean orthogonality. -/
theorem twoStep_a_eq_iff {s : SlopePair} (h : s.EvenConfig) :
    s.twoStep.a = s.a ↔ s.Orthogonal := by
  rw [← sub_eq_zero, twoStep_a_sub_a h, div_eq_zero_iff]
  have hd := ne_of_gt h.denominator_a_pos
  have hab := sub_ne_zero.mpr h.distinct
  simp only [hd, or_false, mul_eq_zero, hab, false_or]
  unfold Orthogonal
  constructor <;> intro he <;> linarith

theorem twoStep_eq_self_iff {s : SlopePair} (h : s.EvenConfig) :
    s.twoStep = s ↔ s.Orthogonal := by
  constructor
  · intro he
    exact (twoStep_a_eq_iff h).mp (congrArg SlopePair.a he)
  · intro ho
    apply SlopePair.ext
    · exact (twoStep_a_eq_iff h).mpr ho
    · apply sub_eq_zero.mp
      rw [twoStep_b_sub_b h]
      have hp : s.a * s.b + 1 = 0 := by linarith [(orthogonal_iff s).mp ho]
      rw [hp, mul_zero, zero_div]

/-- Replace both lines by their Euclidean perpendiculars, preserving the
canonical ordering of shallow and steep slopes. -/
noncomputable def reciprocal (s : SlopePair) : SlopePair := ⟨-1 / s.b, -1 / s.a⟩

@[simp] theorem reciprocal_reciprocal (s : SlopePair) : s.reciprocal.reciprocal = s := by
  ext <;> simp [reciprocal]

theorem reciprocal_evenConfig {s : SlopePair} (h : s.EvenConfig) :
    s.reciprocal.EvenConfig := by
  have hb := h.b_neg
  change 0 < -1 / s.b ∧ -1 / s.b < 1 ∧ -1 / s.a < -1
  refine ⟨div_pos_of_neg_of_neg (by norm_num) hb,
    (div_lt_iff_of_neg hb).mpr ?_, (div_lt_iff₀ h.1).mpr ?_⟩
  · linarith [h.2.2]
  · linarith [h.2.1]

theorem reciprocal_oddConfig {s : SlopePair} (h : s.OddConfig) :
    s.reciprocal.OddConfig := by
  have hb := h.b_pos
  change -1 < -1 / s.b ∧ -1 / s.b < 0 ∧ 1 < -1 / s.a
  refine ⟨(lt_div_iff₀ hb).mpr ?_, div_neg_of_neg_of_pos (by norm_num) hb,
    (lt_div_iff_of_neg h.2.1).mpr ?_⟩
  · linarith [h.2.2]
  · linarith [h.1]

theorem toOdd_reciprocal {s : SlopePair} (ha : s.a ≠ 0) (hb : s.b ≠ 0) :
    s.reciprocal.toOdd = s.toOdd.reciprocal := by
  ext <;> dsimp [reciprocal, toOdd] <;> field_simp <;> ring_nf
  rw [show -1 - s.a = -(1 + s.a) by ring, inv_neg]
  ring

theorem toEven_reciprocal {s : SlopePair} (ha : s.a ≠ 0) (hb : s.b ≠ 0) :
    s.reciprocal.toEven = s.toEven.reciprocal := by
  ext <;> dsimp [reciprocal, toEven] <;> field_simp <;> ring_nf
  rw [show -1 - s.a = -(1 + s.a) by ring, inv_neg]
  ring

theorem twoStep_reciprocal {s : SlopePair} (h : s.EvenConfig) :
    s.reciprocal.twoStep = s.twoStep.reciprocal := by
  have ha := ne_of_gt h.1
  have hb := h.b_ne_zero
  have ho := toOdd_config h
  have hoa : s.toOdd.a ≠ 0 := ne_of_lt ho.2.1
  have hob := ho.b_ne_zero
  unfold twoStep
  rw [toOdd_reciprocal ha hb, toEven_reciprocal hoa hob]

/-- Theorem 8 in slope form, for every even index of Algorithm 6. -/
theorem evenIterate_reciprocal {s : SlopePair} (h : s.EvenConfig) (n : ℕ) :
    s.reciprocal.evenIterate n = (s.evenIterate n).reciprocal := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [evenIterate, ih] using twoStep_reciprocal (evenIterate_config h n)

theorem oddIterate_reciprocal {s : SlopePair} (h : s.EvenConfig) (n : ℕ) :
    s.reciprocal.oddIterate n = (s.oddIterate n).reciprocal := by
  have hn := evenIterate_config h n
  unfold oddIterate
  rw [evenIterate_reciprocal h]
  exact toOdd_reciprocal (ne_of_gt hn.1) hn.b_ne_zero

theorem Orthogonal.b_eq {s : SlopePair} (h : s.Orthogonal) : s.b = -1 / s.a := by
  have hp := (orthogonal_iff s).mp h
  have ha : s.a ≠ 0 := by intro he; simp [he] at hp
  apply (eq_div_iff ha).mpr
  nlinarith [hp]

theorem Orthogonal.reciprocal_eq {s : SlopePair} (h : s.Orthogonal) :
    s.reciprocal = s := by
  have hp := (orthogonal_iff s).mp h
  have hb : s.b ≠ 0 := by intro he; simp [he] at hp
  apply SlopePair.ext
  · change -1 / s.b = s.a
    apply (div_eq_iff hb).mpr
    nlinarith [hp]
  · exact h.b_eq.symm

theorem toOdd_a_of_orthogonal {s : SlopePair} (h : s.EvenConfig) (ho : s.Orthogonal) :
    s.toOdd.a = (s.a - 1) / (s.a + 1) := by
  have hb1 := h.b_sub_one_ne_zero
  have ha1 : s.a + 1 ≠ 0 := by linarith [h.1]
  have hp := (orthogonal_iff s).mp ho
  change s.b * (s.a - 1) / (s.b - 1) = _
  apply (div_eq_div_iff hb1 ha1).mpr
  calc
    s.b * (s.a - 1) * (s.a + 1) = (s.a - 1) * (s.a * s.b + s.b) := by ring
    _ = (s.a - 1) * (s.b - 1) := by rw [hp]; ring

theorem toOdd_b_of_orthogonal {s : SlopePair} (h : s.EvenConfig) (ho : s.Orthogonal) :
    s.toOdd.b = -(s.a + 1) / (s.a - 1) := by
  have hb1 := h.b_add_one_ne_zero
  have ha1 : s.a - 1 ≠ 0 := by linarith [h.2.1]
  have hp := (orthogonal_iff s).mp ho
  change s.b * (s.a + 1) / (s.b + 1) = _
  apply (div_eq_div_iff hb1 ha1).mpr
  calc
    s.b * (s.a + 1) * (s.a - 1) = (s.a + 1) * (s.a * s.b - s.b) := by ring
    _ = -(s.a + 1) * (s.b + 1) := by rw [hp]; ring

theorem toOdd_orthogonal {s : SlopePair} (h : s.EvenConfig) (ho : s.Orthogonal) :
    s.toOdd.Orthogonal := by
  rw [orthogonal_iff, toOdd_a_of_orthogonal h ho, toOdd_b_of_orthogonal h ho,
    div_mul_div_comm]
  apply (div_eq_iff (mul_ne_zero (by linarith [h.1]) (by linarith [h.2.1]))).mpr
  ring

/-- Reflection across the horizontal axis exchanges the canonical orientations. -/
noncomputable def negateSlopes (s : SlopePair) : SlopePair := ⟨-s.a, -s.b⟩

@[simp] theorem negateSlopes_negateSlopes (s : SlopePair) :
    s.negateSlopes.negateSlopes = s := by ext <;> simp [negateSlopes]

theorem negateSlopes_evenConfig {s : SlopePair} (h : s.OddConfig) :
    s.negateSlopes.EvenConfig := by
  rcases h with ⟨h1, h2, h3⟩
  dsimp [EvenConfig, negateSlopes]
  exact ⟨by linarith, by linarith, by linarith⟩

theorem negateSlopes_oddConfig {s : SlopePair} (h : s.EvenConfig) :
    s.negateSlopes.OddConfig := by
  rcases h with ⟨h1, h2, h3⟩
  dsimp [OddConfig, negateSlopes]
  exact ⟨by linarith, by linarith, by linarith⟩

@[simp] theorem negateSlopes_orthogonal_iff (s : SlopePair) :
    s.negateSlopes.Orthogonal ↔ s.Orthogonal := by simp [Orthogonal, negateSlopes]

theorem toOdd_negateSlopes (s : SlopePair) :
    s.negateSlopes.toOdd = s.toEven.negateSlopes := by
  ext <;> dsimp [negateSlopes, toOdd, toEven] <;> field_simp <;> ring_nf
  all_goals
    simp only [show -1 - s.b = -(1 + s.b) by ring,
      show 1 - s.b = -(-1 + s.b) by ring, inv_neg]
    ring

theorem toEven_negateSlopes (s : SlopePair) :
    s.negateSlopes.toEven = s.toOdd.negateSlopes := by
  ext <;> dsimp [negateSlopes, toOdd, toEven] <;> field_simp <;> ring_nf
  all_goals
    simp only [show -1 - s.b = -(1 + s.b) by ring,
      show 1 - s.b = -(-1 + s.b) by ring, inv_neg]
    ring

theorem toEven_orthogonal {s : SlopePair} (h : s.OddConfig) (ho : s.Orthogonal) :
    s.toEven.Orthogonal := by
  have hr := toOdd_orthogonal (negateSlopes_evenConfig h)
    ((negateSlopes_orthogonal_iff s).mpr ho)
  rw [toOdd_negateSlopes, negateSlopes_orthogonal_iff] at hr
  exact hr

/-- Theorem 2 for the other canonical orientation. -/
theorem toEven_toOdd_eq_self_iff {s : SlopePair} (h : s.OddConfig) :
    s.toEven.toOdd = s ↔ s.Orthogonal := by
  have he := twoStep_eq_self_iff (negateSlopes_evenConfig h)
  change s.negateSlopes.toOdd.toEven = s.negateSlopes ↔ _ at he
  rw [toOdd_negateSlopes, toEven_negateSlopes, negateSlopes_orthogonal_iff] at he
  constructor
  · intro hs
    exact he.mp (congrArg negateSlopes hs)
  · intro ho
    have hs := congrArg negateSlopes (he.mpr ho)
    simpa using hs

theorem toEven_a_of_orthogonal {s : SlopePair} (h : s.OddConfig) (ho : s.Orthogonal) :
    s.toEven.a = -(s.a + 1) / (s.a - 1) := by
  have hb1 := h.b_add_one_ne_zero
  have ha1 : s.a - 1 ≠ 0 := by linarith [h.2.1]
  have hp := (orthogonal_iff s).mp ho
  change s.b * (s.a + 1) / (s.b + 1) = _
  apply (div_eq_div_iff hb1 ha1).mpr
  calc
    s.b * (s.a + 1) * (s.a - 1) = (s.a + 1) * (s.a * s.b - s.b) := by ring
    _ = -(s.a + 1) * (s.b + 1) := by rw [hp]; ring

theorem toEven_b_of_orthogonal {s : SlopePair} (h : s.OddConfig) (ho : s.Orthogonal) :
    s.toEven.b = (s.a - 1) / (s.a + 1) := by
  have hb1 := h.b_sub_one_ne_zero
  have ha1 : s.a + 1 ≠ 0 := by linarith [h.1]
  have hp := (orthogonal_iff s).mp ho
  change s.b * (s.a - 1) / (s.b - 1) = _
  apply (div_eq_div_iff hb1 ha1).mpr
  calc
    s.b * (s.a - 1) * (s.a + 1) = (s.a - 1) * (s.a * s.b + s.b) := by ring
    _ = (s.a - 1) * (s.b - 1) := by rw [hp]; ring

end SlopePair
end FitzhughFarnsworth
