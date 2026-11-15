module

public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Tactic

/-!
# The taxicab plane

A separate point type prevents accidentally using the default product metric
on `ℝ × ℝ`, which is the maximum metric rather than the taxicab metric.
-/

@[expose] public section

namespace FitzhughFarnsworth

@[ext]
structure Point where
  x : ℝ
  y : ℝ

noncomputable def taxicabDist (p q : Point) : ℝ :=
  |p.x - q.x| + |p.y - q.y|

noncomputable instance : MetricSpace Point where
  dist := taxicabDist
  dist_self p := by simp [taxicabDist]
  dist_comm p q := by simp only [taxicabDist, abs_sub_comm]
  dist_triangle p q r := by
    dsimp [taxicabDist]
    have hx := abs_sub_le p.x q.x r.x
    have hy := abs_sub_le p.y q.y r.y
    linarith
  eq_of_dist_eq_zero := by
    intro p q h
    change |p.x - q.x| + |p.y - q.y| = 0 at h
    have hx : |p.x - q.x| = 0 := by linarith [abs_nonneg (p.x - q.x), abs_nonneg (p.y - q.y)]
    have hy : |p.y - q.y| = 0 := by linarith [abs_nonneg (p.x - q.x), abs_nonneg (p.y - q.y)]
    ext
    · exact sub_eq_zero.mp (abs_eq_zero.mp hx)
    · exact sub_eq_zero.mp (abs_eq_zero.mp hy)

theorem dist_eq (p q : Point) : dist p q = |p.x - q.x| + |p.y - q.y| := rfl

def origin : Point := ⟨0, 0⟩

/-- A finite-slope line through the origin. Vertical lines are defined separately. -/
def slopeLine (m : ℝ) : Set Point := {p | p.y = m * p.x}

def verticalAxis : Set Point := {p | p.x = 0}

def horizontalAxis : Set Point := slopeLine 0

theorem slopeLine_nonempty (m : ℝ) : (slopeLine m).Nonempty :=
  ⟨origin, by simp [slopeLine, origin]⟩

theorem verticalAxis_nonempty : verticalAxis.Nonempty := ⟨origin, rfl⟩

end FitzhughFarnsworth
