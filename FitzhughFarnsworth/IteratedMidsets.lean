/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.LineConfigurations
public import FitzhughFarnsworth.LineDistances

/-!
# Algorithm 6

Separate parity maps make the denominators and alternating octants explicit.
`evenIterate s n` denotes the pair at paper index `2*n`.
-/

@[expose] public section

namespace FitzhughFarnsworth
namespace SlopePair

/-- One midset step from the even canonical configuration. -/
noncomputable def toOdd (s : SlopePair) : SlopePair :=
  ⟨s.b * (s.a - 1) / (s.b - 1), s.b * (s.a + 1) / (s.b + 1)⟩

/-- One midset step from the odd canonical configuration. -/
noncomputable def toEven (s : SlopePair) : SlopePair :=
  ⟨s.b * (s.a + 1) / (s.b + 1), s.b * (s.a - 1) / (s.b - 1)⟩

/-- Two successive midset steps, returning to the even configuration. -/
noncomputable def twoStep (s : SlopePair) : SlopePair := s.toOdd.toEven

/-- The even-indexed slope pairs of Algorithm 6; `n` corresponds to paper index `2 * n`. -/
noncomputable def evenIterate (s : SlopePair) : ℕ → SlopePair
  | 0 => s
  | n + 1 => (evenIterate s n).twoStep

/-- The odd-indexed slope pairs of Algorithm 6, following each even iterate. -/
noncomputable def oddIterate (s : SlopePair) (n : ℕ) : SlopePair :=
  (s.evenIterate n).toOdd

theorem midset_eq_toOdd {s : SlopePair} (h : s.EvenConfig) :
    midset (slopeLine s.a) (slopeLine s.b) =
      slopeLine s.toOdd.a ∪ slopeLine s.toOdd.b := by
  apply midset_shallow_steep
  · exact abs_le.mpr ⟨by linarith [h.1], h.2.1.le⟩
  · rw [abs_of_neg h.b_neg]
    linarith [h.2.2]

theorem midset_eq_toEven {s : SlopePair} (h : s.OddConfig) :
    midset (slopeLine s.a) (slopeLine s.b) =
      slopeLine s.toEven.a ∪ slopeLine s.toEven.b := by
  rw [midset_shallow_steep s.a s.b (abs_le.mpr ⟨h.1.le, by linarith [h.2.1]⟩)
    (by rw [abs_of_pos h.b_pos]; exact h.2.2)]
  exact Set.union_comm _ _

theorem toOdd_config {s : SlopePair} (h : s.EvenConfig) : s.toOdd.OddConfig := by
  have hb0 := h.b_neg
  have hbsub := h.b_sub_one_neg
  have hbadd := h.b_add_one_neg
  have hab := h.product_neg
  rcases h with ⟨ha0, ha1, hb⟩
  change -1 < s.b * (s.a - 1) / (s.b - 1) ∧
    s.b * (s.a - 1) / (s.b - 1) < 0 ∧ 1 < s.b * (s.a + 1) / (s.b + 1)
  refine ⟨(lt_div_iff_of_neg hbsub).mpr ?_, ?_, (lt_div_iff_of_neg hbadd).mpr ?_⟩
  · nlinarith
  · exact div_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hb0 (by linarith)) hbsub
  · nlinarith

theorem toEven_config {s : SlopePair} (h : s.OddConfig) : s.toEven.EvenConfig := by
  have hb0 := h.b_pos
  have hbsub := h.b_sub_one_pos
  have hbadd := h.b_add_one_pos
  have hab := h.product_neg
  rcases h with ⟨ha1, ha0, hb⟩
  change 0 < s.b * (s.a + 1) / (s.b + 1) ∧
    s.b * (s.a + 1) / (s.b + 1) < 1 ∧ s.b * (s.a - 1) / (s.b - 1) < -1
  refine ⟨div_pos (mul_pos hb0 (by linarith)) hbadd,
    (div_lt_iff₀ hbadd).mpr ?_, (div_lt_iff₀ hbsub).mpr ?_⟩ <;> nlinarith

theorem twoStep_config {s : SlopePair} (h : s.EvenConfig) : s.twoStep.EvenConfig :=
  toEven_config (toOdd_config h)

theorem evenIterate_config {s : SlopePair} (h : s.EvenConfig) (n : ℕ) :
    (s.evenIterate n).EvenConfig := by
  induction n with
  | zero => exact h
  | succ n ih => exact twoStep_config ih

theorem oddIterate_config {s : SlopePair} (h : s.EvenConfig) (n : ℕ) :
    (s.oddIterate n).OddConfig := toOdd_config (evenIterate_config h n)

theorem evenIterate_midset {s : SlopePair} (h : s.EvenConfig) (n : ℕ) :
    midset (slopeLine (s.evenIterate n).a) (slopeLine (s.evenIterate n).b) =
      slopeLine (s.oddIterate n).a ∪ slopeLine (s.oddIterate n).b :=
  midset_eq_toOdd (evenIterate_config h n)

theorem oddIterate_midset {s : SlopePair} (h : s.EvenConfig) (n : ℕ) :
    midset (slopeLine (s.oddIterate n).a) (slopeLine (s.oddIterate n).b) =
      slopeLine (s.evenIterate (n + 1)).a ∪ slopeLine (s.evenIterate (n + 1)).b :=
  midset_eq_toEven (oddIterate_config h n)

end SlopePair
end FitzhughFarnsworth
