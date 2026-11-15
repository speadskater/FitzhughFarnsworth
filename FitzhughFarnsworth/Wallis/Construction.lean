/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The rectangle construction for Wallis-type formulas

Fitzhugh–Farnsworth (2013), Section 5.1, equations (13)–(20).
One iteration attaches a rectangle of area `A` to the right, then a rectangle
of area `B` above. Index `n` therefore denotes `2 * n` individual attachments.
All four input parameters are strictly positive. The area identities justify
every denominator in the multiplicative recurrence and finite product.
-/

@[expose] public section

namespace FitzhughFarnsworth.Wallis

/-- Positive initial side lengths and positive areas of the attached rectangles. -/
structure Parameters where
  /-- Initial width. -/
  a : ℝ
  /-- Initial height. -/
  b : ℝ
  /-- Area attached to the right. -/
  A : ℝ
  /-- Area attached above. -/
  B : ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  A_pos : 0 < A
  B_pos : 0 < B

namespace Parameters

/-- Dimensions after `n` complete pairs of attachments, starting with `(a, b)`. -/
noncomputable def dimensions (c : Parameters) : ℕ → ℝ × ℝ
  | 0 => (c.a, c.b)
  | n + 1 =>
    let s := c.dimensions n
    let w := s.1 + c.A / s.2
    (w, s.2 + c.B / w)

/-- The paper's `w_n`. -/
noncomputable def width (c : Parameters) (n : ℕ) : ℝ := (c.dimensions n).1

/-- The paper's `h_n`. -/
noncomputable def height (c : Parameters) (n : ℕ) : ℝ := (c.dimensions n).2

/-- Equation (13), initial width. -/
@[simp] theorem width_zero (c : Parameters) : c.width 0 = c.a := rfl

/-- Equation (13), initial height. -/
@[simp] theorem height_zero (c : Parameters) : c.height 0 = c.b := rfl

theorem width_succ (c : Parameters) (n : ℕ) :
    c.width (n + 1) = c.width n + c.A / c.height n := rfl

theorem height_succ (c : Parameters) (n : ℕ) :
    c.height (n + 1) = c.height n + c.B / c.width (n + 1) := rfl

theorem dimensions_pos (c : Parameters) (n : ℕ) :
    0 < c.width n ∧ 0 < c.height n := by
  induction n with
  | zero => exact ⟨c.a_pos, c.b_pos⟩
  | succ n ih =>
    have hw : 0 < c.width (n + 1) := by
      rw [width_succ]
      exact add_pos ih.1 (div_pos c.A_pos ih.2)
    refine ⟨hw, ?_⟩
    rw [height_succ]
    exact add_pos ih.2 (div_pos c.B_pos hw)

theorem width_pos (c : Parameters) (n : ℕ) : 0 < c.width n :=
  (c.dimensions_pos n).1

theorem height_pos (c : Parameters) (n : ℕ) : 0 < c.height n :=
  (c.dimensions_pos n).2

/-- Equation (14): the rectangle attached to the right has area `A`. -/
theorem right_attachment_area (c : Parameters) (n : ℕ) :
    (c.width (n + 1) - c.width n) * c.height n = c.A := by
  rw [width_succ, add_sub_cancel_left, div_mul_cancel₀ _ (c.height_pos n).ne']

/-- Equation (15): the rectangle attached above has area `B`. -/
theorem top_attachment_area (c : Parameters) (n : ℕ) :
    c.width (n + 1) * (c.height (n + 1) - c.height n) = c.B := by
  rw [height_succ, add_sub_cancel_left, mul_div_cancel₀ _ (c.width_pos (n + 1)).ne']

theorem width_strictMono (c : Parameters) : StrictMono c.width := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [width_succ]
  exact lt_add_of_pos_right _ (div_pos c.A_pos (c.height_pos n))

theorem height_strictMono (c : Parameters) : StrictMono c.height := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [height_succ]
  exact lt_add_of_pos_right _ (div_pos c.B_pos (c.width_pos (n + 1)))

/-- Equation (16): area after `2 * n` attachments. -/
theorem area_even (c : Parameters) (n : ℕ) :
    c.width n * c.height n = c.a * c.b + n * (c.A + c.B) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hr := c.right_attachment_area n
    have ht := c.top_attachment_area n
    push_cast
    nlinarith

/-- Equation (17): area after `2 * n + 1` attachments. -/
theorem area_odd (c : Parameters) (n : ℕ) :
    c.width (n + 1) * c.height n = c.a * c.b + n * (c.A + c.B) + c.A := by
  have hr := c.right_attachment_area n
  have he := c.area_even n
  nlinarith

theorem area_even_pos (c : Parameters) (n : ℕ) :
    0 < c.a * c.b + n * (c.A + c.B) := by
  rw [← area_even]
  exact mul_pos (c.width_pos n) (c.height_pos n)

theorem area_odd_pos (c : Parameters) (n : ℕ) :
    0 < c.a * c.b + n * (c.A + c.B) + c.A :=
  add_pos (c.area_even_pos n) c.A_pos

/-- Equation (18), derived from the attachment area and the current total area. -/
theorem width_succ_mul (c : Parameters) (n : ℕ) :
    c.width (n + 1) = c.width n *
      ((c.a * c.b + n * (c.A + c.B) + c.A) /
        (c.a * c.b + n * (c.A + c.B))) := by
  rw [← area_odd, ← area_even]
  field_simp [(c.width_pos n).ne', (c.height_pos n).ne']

/-- Equation (19), using the total area after the right attachment. -/
theorem height_succ_mul (c : Parameters) (n : ℕ) :
    c.height (n + 1) = c.height n *
      ((c.a * c.b + (n + 1 : ℕ) * (c.A + c.B)) /
        (c.a * c.b + n * (c.A + c.B) + c.A)) := by
  rw [← area_even, ← area_odd]
  field_simp [(c.width_pos (n + 1)).ne', (c.height_pos n).ne']

/-- Width divided by height after `2 * n` attachments. -/
noncomputable def ratio (c : Parameters) (n : ℕ) : ℝ := c.width n / c.height n

@[simp] theorem ratio_zero (c : Parameters) : c.ratio 0 = c.a / c.b := rfl

theorem ratio_pos (c : Parameters) (n : ℕ) : 0 < c.ratio n :=
  div_pos (c.width_pos n) (c.height_pos n)

/-- The multiplier of the aspect ratio in equation (20). -/
noncomputable def ratioFactor (c : Parameters) (n : ℕ) : ℝ :=
  ((c.a * c.b + n * (c.A + c.B) + c.A) / (c.a * c.b + n * (c.A + c.B))) *
    ((c.a * c.b + n * (c.A + c.B) + c.A) /
      (c.a * c.b + (n + 1 : ℕ) * (c.A + c.B)))

theorem ratioFactor_pos (c : Parameters) (n : ℕ) : 0 < c.ratioFactor n :=
  mul_pos (div_pos (c.area_odd_pos n) (c.area_even_pos n))
    (div_pos (c.area_odd_pos n) (c.area_even_pos (n + 1)))

/-- Equation (20): the ratio recurrence follows from the actual dimension updates. -/
theorem ratio_succ (c : Parameters) (n : ℕ) :
    c.ratio (n + 1) = c.ratio n * c.ratioFactor n := by
  unfold ratio ratioFactor
  rw [c.width_succ_mul n, c.height_succ_mul n]
  field_simp

/-- Finite product underlying equation (21), with the original zero-based index.
This identity alone makes no infinite-product convergence assertion. -/
theorem ratio_eq_prod (c : Parameters) (n : ℕ) :
    c.ratio n = c.a / c.b * ∏ k ∈ Finset.range n, c.ratioFactor k := by
  induction n with
  | zero => simp
  | succ n ih => rw [ratio_succ, ih, Finset.prod_range_succ, mul_assoc]

/-- The attachment equations uniquely determine the dimension sequences. -/
theorem dimensions_unique (c : Parameters) (w h : ℕ → ℝ)
    (hw : w 0 = c.a) (hh : h 0 = c.b)
    (hr : ∀ n, (w (n + 1) - w n) * h n = c.A)
    (ht : ∀ n, w (n + 1) * (h (n + 1) - h n) = c.B) (n : ℕ) :
    w n = c.width n ∧ h n = c.height n := by
  induction n with
  | zero => exact ⟨hw, hh⟩
  | succ n ih =>
    have hright := hr n
    rw [ih.1, ih.2] at hright
    have hw' : w (n + 1) = c.width (n + 1) := by
      have := c.right_attachment_area n
      have hn := (c.height_pos n).ne'
      have he : w (n + 1) - c.width n = c.width (n + 1) - c.width n :=
        (mul_left_inj' hn).mp (hright.trans this.symm)
      linarith
    refine ⟨hw', ?_⟩
    have htop := ht n
    rw [hw', ih.2] at htop
    have := c.top_attachment_area n
    have hn := (c.width_pos (n + 1)).ne'
    have he : h (n + 1) - c.height n = c.height (n + 1) - c.height n :=
      (mul_right_inj' hn).mp (htop.trans this.symm)
    linarith

end Parameters

end FitzhughFarnsworth.Wallis
