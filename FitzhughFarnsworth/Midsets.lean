module

public import FitzhughFarnsworth.MetricGeometry

/-!
# Equidistance sets

Distance to a set is mathlib's metric infimum distance. All lines used in this
project are nonempty. For arbitrary empty sets, `Metric.infDist` uses the value
zero; the geometric results never use that convention.
-/

@[expose] public section

namespace FitzhughFarnsworth

def midset {X : Type*} [PseudoMetricSpace X] (s t : Set X) : Set X :=
  {p | Metric.infDist p s = Metric.infDist p t}

theorem mem_midset {X : Type*} [PseudoMetricSpace X] (p : X) (s t : Set X) :
    p ∈ midset s t ↔ Metric.infDist p s = Metric.infDist p t := Iff.rfl

theorem midset_comm {X : Type*} [PseudoMetricSpace X] (s t : Set X) :
    midset s t = midset t s := by
  ext p
  exact eq_comm

theorem midset_self {X : Type*} [PseudoMetricSpace X] (s : Set X) :
    midset s s = Set.univ := by
  ext p
  simp [midset]

theorem inter_subset_midset {X : Type*} [PseudoMetricSpace X] (s t : Set X) :
    s ∩ t ⊆ midset s t := by
  intro p hp
  change Metric.infDist p s = Metric.infDist p t
  rw [Metric.infDist_zero_of_mem hp.1, Metric.infDist_zero_of_mem hp.2]

theorem isClosed_midset {X : Type*} [PseudoMetricSpace X] (s t : Set X) :
    IsClosed (midset s t) :=
  isClosed_eq (Metric.continuous_infDist_pt s) (Metric.continuous_infDist_pt t)

end FitzhughFarnsworth
