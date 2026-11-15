module

public import FitzhughFarnsworth.LineConfigurations.Reduction

/-!
# Axis/diagonal boundary configurations

Theorem 4 is proved for all four choices of an axis and a diagonal, in either
order. The witnesses retain the two component lines at both midset steps.
-/

@[expose] public section

namespace FitzhughFarnsworth

inductive ConfigurationThreePair : Set Point → Set Point → Prop where
  | horizontal_pos : ConfigurationThreePair horizontalAxis (slopeLine 1)
  | horizontal_neg : ConfigurationThreePair horizontalAxis (slopeLine (-1))
  | vertical_pos : ConfigurationThreePair verticalAxis (slopeLine 1)
  | vertical_neg : ConfigurationThreePair verticalAxis (slopeLine (-1))
  | comm {A B : Set Point} : ConfigurationThreePair A B → ConfigurationThreePair B A

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
