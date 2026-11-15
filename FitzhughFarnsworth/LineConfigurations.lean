module

public import FitzhughFarnsworth.LineDistances

/-!
# Canonical slope configurations

These predicates describe the two orientations of Configuration 1 used in the
paper. Reduction of all ten configurations by taxicab isometries is future work.
-/

@[expose] public section

namespace FitzhughFarnsworth

@[ext]
structure SlopePair where
  a : ℝ
  b : ℝ

namespace SlopePair

def EvenConfig (s : SlopePair) : Prop := 0 < s.a ∧ s.a < 1 ∧ s.b < -1

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

end SlopePair
end FitzhughFarnsworth
