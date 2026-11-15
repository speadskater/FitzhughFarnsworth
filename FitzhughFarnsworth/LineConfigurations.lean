/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Canonical slope configurations

These predicates describe the two orientations of Configuration 1 used in the
paper. `LineConfigurations.Reduction` treats arbitrary intersecting lines and
proves their reduction to Configuration 1 or 2 using taxicab isometries.
-/

@[expose] public section

namespace FitzhughFarnsworth

/-- The slopes of an ordered pair of nonvertical lines through the origin. -/
@[ext]
structure SlopePair where
  /-- The first line's slope, shallow in the canonical configurations. -/
  a : ℝ
  /-- The second line's slope, steep in the canonical configurations. -/
  b : ℝ

namespace SlopePair

/-- A positive shallow slope and a negative steep slope. -/
def EvenConfig (s : SlopePair) : Prop := 0 < s.a ∧ s.a < 1 ∧ s.b < -1

/-- A negative shallow slope and a positive steep slope. -/
def OddConfig (s : SlopePair) : Prop := -1 < s.a ∧ s.a < 0 ∧ 1 < s.b

/-- Orthogonality of the direction vectors `(1, a)` and `(1, b)`. -/
def Orthogonal (s : SlopePair) : Prop := 1 + s.a * s.b = 0

theorem orthogonal_iff (s : SlopePair) : s.Orthogonal ↔ s.a * s.b = -1 := by
  unfold Orthogonal
  constructor <;> intro h <;> linarith

theorem EvenConfig.distinct {s : SlopePair} (h : s.EvenConfig) : s.a ≠ s.b := by
  rcases h with ⟨ha, _, hb⟩
  linarith

theorem OddConfig.distinct {s : SlopePair} (h : s.OddConfig) : s.a ≠ s.b := by
  rcases h with ⟨_, ha, hb⟩
  linarith

theorem EvenConfig.b_neg {s : SlopePair} (h : s.EvenConfig) : s.b < 0 :=
  h.2.2.trans (by norm_num)

theorem EvenConfig.b_ne_zero {s : SlopePair} (h : s.EvenConfig) : s.b ≠ 0 :=
  h.b_neg.ne

theorem EvenConfig.b_sub_one_neg {s : SlopePair} (h : s.EvenConfig) : s.b - 1 < 0 :=
  sub_neg.mpr (h.b_neg.trans zero_lt_one)

theorem EvenConfig.b_add_one_neg {s : SlopePair} (h : s.EvenConfig) : s.b + 1 < 0 :=
  (lt_neg_iff_add_neg).mp h.2.2

theorem EvenConfig.b_sub_one_ne_zero {s : SlopePair} (h : s.EvenConfig) : s.b - 1 ≠ 0 :=
  h.b_sub_one_neg.ne

theorem EvenConfig.b_add_one_ne_zero {s : SlopePair} (h : s.EvenConfig) : s.b + 1 ≠ 0 :=
  h.b_add_one_neg.ne

theorem EvenConfig.product_neg {s : SlopePair} (h : s.EvenConfig) : s.a * s.b < 0 :=
  mul_neg_of_pos_of_neg h.1 h.b_neg

theorem OddConfig.b_pos {s : SlopePair} (h : s.OddConfig) : 0 < s.b :=
  zero_lt_one.trans h.2.2

theorem OddConfig.b_ne_zero {s : SlopePair} (h : s.OddConfig) : s.b ≠ 0 :=
  h.b_pos.ne'

theorem OddConfig.b_sub_one_pos {s : SlopePair} (h : s.OddConfig) : 0 < s.b - 1 :=
  sub_pos.mpr h.2.2

theorem OddConfig.b_add_one_pos {s : SlopePair} (h : s.OddConfig) : 0 < s.b + 1 :=
  add_pos h.b_pos zero_lt_one

theorem OddConfig.b_sub_one_ne_zero {s : SlopePair} (h : s.OddConfig) : s.b - 1 ≠ 0 :=
  h.b_sub_one_pos.ne'

theorem OddConfig.b_add_one_ne_zero {s : SlopePair} (h : s.OddConfig) : s.b + 1 ≠ 0 :=
  h.b_add_one_pos.ne'

theorem OddConfig.product_neg {s : SlopePair} (h : s.OddConfig) : s.a * s.b < 0 :=
  mul_neg_of_neg_of_pos h.2.1 h.b_pos

end SlopePair
end FitzhughFarnsworth
