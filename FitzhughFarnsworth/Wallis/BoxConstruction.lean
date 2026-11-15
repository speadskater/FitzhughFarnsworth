/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Wallis.Construction

/-!
# The three-dimensional box construction

Fitzhugh–Farnsworth (2013), Section 5.2, equations (24)–(34).
Each iteration attaches boxes of volumes `A`, `B`, and `C`, in the width,
height, and depth directions, respectively. The intermediate dimensions are
retained in the attachment and volume identities.
-/

@[expose] public section

namespace FitzhughFarnsworth.Wallis

/-- Positive initial sides and positive volumes of the three attached boxes. -/
structure BoxParameters where
  /-- Initial width. -/
  a : ℝ
  /-- Initial height. -/
  b : ℝ
  /-- Initial depth. -/
  c : ℝ
  /-- Volume attached in the width direction. -/
  A : ℝ
  /-- Volume attached in the height direction. -/
  B : ℝ
  /-- Volume attached in the depth direction. -/
  C : ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c
  A_pos : 0 < A
  B_pos : 0 < B
  C_pos : 0 < C

namespace BoxParameters

/-- Dimensions after `3 * n` individual attachments. -/
noncomputable def dimensions (s : BoxParameters) : ℕ → ℝ × ℝ × ℝ
  | 0 => (s.a, s.b, s.c)
  | n + 1 =>
    let q := s.dimensions n
    let w := q.1 + s.A / (q.2.1 * q.2.2)
    let h := q.2.1 + s.B / (w * q.2.2)
    (w, h, q.2.2 + s.C / (w * h))

/-- The paper's `w_n`. -/
noncomputable def width (s : BoxParameters) (n : ℕ) : ℝ := (s.dimensions n).1

/-- The paper's `h_n`. -/
noncomputable def height (s : BoxParameters) (n : ℕ) : ℝ := (s.dimensions n).2.1

/-- The paper's `d_n`. -/
noncomputable def depth (s : BoxParameters) (n : ℕ) : ℝ := (s.dimensions n).2.2

@[simp] theorem width_zero (s : BoxParameters) : s.width 0 = s.a := rfl

@[simp] theorem height_zero (s : BoxParameters) : s.height 0 = s.b := rfl

@[simp] theorem depth_zero (s : BoxParameters) : s.depth 0 = s.c := rfl

theorem width_succ (s : BoxParameters) (n : ℕ) :
    s.width (n + 1) = s.width n + s.A / (s.height n * s.depth n) := rfl

theorem height_succ (s : BoxParameters) (n : ℕ) :
    s.height (n + 1) = s.height n + s.B / (s.width (n + 1) * s.depth n) := rfl

theorem depth_succ (s : BoxParameters) (n : ℕ) :
    s.depth (n + 1) = s.depth n + s.C / (s.width (n + 1) * s.height (n + 1)) := rfl

theorem dimensions_pos (s : BoxParameters) (n : ℕ) :
    0 < s.width n ∧ 0 < s.height n ∧ 0 < s.depth n := by
  induction n with
  | zero => exact ⟨s.a_pos, s.b_pos, s.c_pos⟩
  | succ n ih =>
    have hw : 0 < s.width (n + 1) := by
      rw [width_succ]
      exact add_pos ih.1 (div_pos s.A_pos (mul_pos ih.2.1 ih.2.2))
    have hh : 0 < s.height (n + 1) := by
      rw [height_succ]
      exact add_pos ih.2.1 (div_pos s.B_pos (mul_pos hw ih.2.2))
    refine ⟨hw, hh, ?_⟩
    rw [depth_succ]
    exact add_pos ih.2.2 (div_pos s.C_pos (mul_pos hw hh))

theorem width_pos (s : BoxParameters) (n : ℕ) : 0 < s.width n :=
  (s.dimensions_pos n).1

theorem height_pos (s : BoxParameters) (n : ℕ) : 0 < s.height n :=
  (s.dimensions_pos n).2.1

theorem depth_pos (s : BoxParameters) (n : ℕ) : 0 < s.depth n :=
  (s.dimensions_pos n).2.2

/-- Equation (25). -/
theorem right_attachment_volume (s : BoxParameters) (n : ℕ) :
    (s.width (n + 1) - s.width n) * s.height n * s.depth n = s.A := by
  rw [width_succ, add_sub_cancel_left]
  field_simp [(s.height_pos n).ne', (s.depth_pos n).ne']

/-- Equation (26). -/
theorem top_attachment_volume (s : BoxParameters) (n : ℕ) :
    s.width (n + 1) * (s.height (n + 1) - s.height n) * s.depth n = s.B := by
  rw [height_succ, add_sub_cancel_left]
  field_simp [(s.width_pos (n + 1)).ne', (s.depth_pos n).ne']

/-- Equation (27). -/
theorem depth_attachment_volume (s : BoxParameters) (n : ℕ) :
    s.width (n + 1) * s.height (n + 1) * (s.depth (n + 1) - s.depth n) = s.C := by
  rw [depth_succ, add_sub_cancel_left]
  field_simp [(s.width_pos (n + 1)).ne', (s.height_pos (n + 1)).ne']

/-- Equation (28): volume after `3 * n` attachments. -/
theorem volume_cycle (s : BoxParameters) (n : ℕ) :
    s.width n * s.height n * s.depth n = s.a * s.b * s.c + n * (s.A + s.B + s.C) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hr := s.right_attachment_volume n
    have ht := s.top_attachment_volume n
    have hd := s.depth_attachment_volume n
    push_cast
    nlinarith

/-- Equation (29): volume after `3 * n + 1` attachments. -/
theorem volume_after_right (s : BoxParameters) (n : ℕ) :
    s.width (n + 1) * s.height n * s.depth n =
      s.a * s.b * s.c + n * (s.A + s.B + s.C) + s.A := by
  have hr := s.right_attachment_volume n
  have hv := s.volume_cycle n
  nlinarith

/-- Equation (30): volume after `3 * n + 2` attachments. -/
theorem volume_after_top (s : BoxParameters) (n : ℕ) :
    s.width (n + 1) * s.height (n + 1) * s.depth n =
      s.a * s.b * s.c + n * (s.A + s.B + s.C) + s.A + s.B := by
  have ht := s.top_attachment_volume n
  have hv := s.volume_after_right n
  nlinarith

/-- Equation (31). -/
theorem width_succ_mul (s : BoxParameters) (n : ℕ) :
    s.width (n + 1) = s.width n *
      ((s.a * s.b * s.c + n * (s.A + s.B + s.C) + s.A) /
        (s.a * s.b * s.c + n * (s.A + s.B + s.C))) := by
  rw [← volume_after_right, ← volume_cycle]
  field_simp [(s.width_pos n).ne', (s.height_pos n).ne', (s.depth_pos n).ne']

/-- Equation (32). -/
theorem height_succ_mul (s : BoxParameters) (n : ℕ) :
    s.height (n + 1) = s.height n *
      ((s.a * s.b * s.c + n * (s.A + s.B + s.C) + s.A + s.B) /
        (s.a * s.b * s.c + n * (s.A + s.B + s.C) + s.A)) := by
  rw [← volume_after_top, ← volume_after_right]
  field_simp [(s.width_pos (n + 1)).ne', (s.height_pos n).ne', (s.depth_pos n).ne']

/-- Equation (33). -/
theorem depth_succ_mul (s : BoxParameters) (n : ℕ) :
    s.depth (n + 1) = s.depth n *
      ((s.a * s.b * s.c + (n + 1 : ℕ) * (s.A + s.B + s.C)) /
        (s.a * s.b * s.c + n * (s.A + s.B + s.C) + s.A + s.B)) := by
  rw [← volume_cycle, ← volume_after_top]
  field_simp [(s.width_pos (n + 1)).ne', (s.height_pos (n + 1)).ne', (s.depth_pos n).ne']

/-- The side ratio studied in equations (34)–(40). -/
noncomputable def ratio (s : BoxParameters) (n : ℕ) : ℝ := s.width n / s.depth n

@[simp] theorem ratio_zero (s : BoxParameters) : s.ratio 0 = s.a / s.c := rfl

theorem ratio_pos (s : BoxParameters) (n : ℕ) : 0 < s.ratio n :=
  div_pos (s.width_pos n) (s.depth_pos n)

/-- The two factors of equation (34). -/
noncomputable def ratioFactor (s : BoxParameters) (n : ℕ) : ℝ :=
  ((s.a * s.b * s.c + n * (s.A + s.B + s.C) + s.A) /
    (s.a * s.b * s.c + n * (s.A + s.B + s.C))) *
  ((s.a * s.b * s.c + n * (s.A + s.B + s.C) + s.A + s.B) /
    (s.a * s.b * s.c + (n + 1 : ℕ) * (s.A + s.B + s.C)))

/-- Equation (34), for the actual box dimensions. -/
theorem ratio_succ (s : BoxParameters) (n : ℕ) :
    s.ratio (n + 1) = s.ratio n * s.ratioFactor n := by
  unfold ratio ratioFactor
  rw [s.width_succ_mul n, s.depth_succ_mul n]
  field_simp

/-- Finite version of equation (35), with the original zero-based indexing. -/
theorem ratio_eq_prod (s : BoxParameters) (n : ℕ) :
    s.ratio n = s.a / s.c * ∏ k ∈ Finset.range n, s.ratioFactor k := by
  induction n with
  | zero => simp
  | succ n ih => rw [ratio_succ, ih, Finset.prod_range_succ, mul_assoc]

end BoxParameters

end FitzhughFarnsworth.Wallis
