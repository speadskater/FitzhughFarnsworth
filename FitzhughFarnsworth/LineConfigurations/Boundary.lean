/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.LineConfigurations.Reduction

/-!
# Axis/diagonal boundary configurations

Theorem 4 is proved for all four choices of an axis and a diagonal, in either
order. The witnesses retain the two component lines at both midset steps.
-/

@[expose] public section

namespace FitzhughFarnsworth

/-- An axis paired with a diagonal, allowing every axis, diagonal, and input order. -/
inductive ConfigurationThreePair : Set Point → Set Point → Prop where
  /-- The horizontal axis paired with the positive-slope diagonal. -/
  | horizontal_pos : ConfigurationThreePair horizontalAxis (slopeLine 1)
  /-- The horizontal axis paired with the negative-slope diagonal. -/
  | horizontal_neg : ConfigurationThreePair horizontalAxis (slopeLine (-1))
  /-- The vertical axis paired with the positive-slope diagonal. -/
  | vertical_pos : ConfigurationThreePair verticalAxis (slopeLine 1)
  /-- The vertical axis paired with the negative-slope diagonal. -/
  | vertical_neg : ConfigurationThreePair verticalAxis (slopeLine (-1))
  /-- Exchanging the two lines preserves Configuration 3. -/
  | comm {A B : Set Point} : ConfigurationThreePair A B → ConfigurationThreePair B A

/-- Two genuine midset steps whose final pair is specifically Configuration 1. -/
def TwoStepsToOne (A B : Set Point) : Prop :=
  ∃ C D : Set Point, IsOriginLine C ∧ IsOriginLine D ∧ C ≠ D ∧
    midset A B = C ∪ D ∧
    ∃ s : SlopePair, (s.EvenConfig ∨ s.OddConfig) ∧
      midset C D = slopeLine s.a ∪ slopeLine s.b

/-- Theorem 4: every axis/diagonal pair has a Configuration 1 pair as its
second midset, including every choice of axis, sign, and input ordering. -/
theorem configuration_three_two_steps {A B : Set Point} (h : ConfigurationThreePair A B) :
    TwoStepsToOne A B := by
  induction h with
  | horizontal_pos =>
    refine ⟨slopeLine (1 / 2), verticalAxis, isOriginLine_slope _, isOriginLine_vertical,
      slopeLine_ne_vertical _, ?_, ⟨-1 / 2, 3 / 2⟩, Or.inr ?_, ?_⟩
    · simpa only [horizontalAxis, zero_add] using
        midset_two_shallow 0 1 (by norm_num) (by norm_num) (by norm_num)
    · norm_num [SlopePair.OddConfig]
    · convert midset_shallow_vertical (1 / 2) (by norm_num) using 1; norm_num
  | horizontal_neg =>
    refine ⟨slopeLine (-1 / 2), verticalAxis, isOriginLine_slope _, isOriginLine_vertical,
      slopeLine_ne_vertical _, ?_, ⟨1 / 2, -3 / 2⟩, Or.inl ?_, ?_⟩
    · simpa only [horizontalAxis, zero_add] using
        midset_two_shallow 0 (-1) (by norm_num) (by norm_num) (by norm_num)
    · norm_num [SlopePair.EvenConfig]
    · rw [Set.union_comm]
      convert midset_shallow_vertical (-1 / 2) (by norm_num) using 1; norm_num
  | vertical_pos =>
    refine ⟨slopeLine 0, slopeLine 2, isOriginLine_slope _, isOriginLine_slope _,
      slopeLine_ne_of_ne (by norm_num), ?_, ⟨2 / 3, -2⟩, Or.inl ?_, ?_⟩
    · rw [midset_comm]
      convert midset_shallow_vertical 1 (by norm_num) using 1; norm_num
    · norm_num [SlopePair.EvenConfig]
    · rw [Set.union_comm]
      convert midset_shallow_steep 0 2 (by norm_num) (by norm_num) using 1; norm_num
  | vertical_neg =>
    refine ⟨slopeLine 0, slopeLine (-2), isOriginLine_slope _, isOriginLine_slope _,
      slopeLine_ne_of_ne (by norm_num), ?_, ⟨-2 / 3, 2⟩, Or.inr ?_, ?_⟩
    · rw [midset_comm, Set.union_comm]
      convert midset_shallow_vertical (-1) (by norm_num) using 1; norm_num
    · norm_num [SlopePair.OddConfig]
    · convert midset_shallow_steep 0 (-2) (by norm_num) (by norm_num) using 1; norm_num
  | comm h ih =>
    obtain ⟨C, D, hC, hD, hne, hm, s, hs, hnext⟩ := ih
    exact ⟨C, D, hC, hD, hne, by rw [midset_comm]; exact hm, s, hs, hnext⟩

theorem configuration_three_reduces {A B : Set Point} (h : ConfigurationThreePair A B) :
    ReducesIn 2 A B := by
  obtain ⟨C, D, hC, hD, hne, hm, s, hs, hnext⟩ := configuration_three_two_steps h
  apply ReducesIn.step hC hD hne hm
  rcases hs with hs | hs
  · exact .step (isOriginLine_slope _) (isOriginLine_slope _)
      (slopeLine_ne_of_ne hs.distinct) hnext (.done (.even s hs))
  · exact .step (isOriginLine_slope _) (isOriginLine_slope _)
      (slopeLine_ne_of_ne hs.distinct) hnext (.done (.odd s hs))

end FitzhughFarnsworth
