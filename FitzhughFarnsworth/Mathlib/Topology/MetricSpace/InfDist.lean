/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Distance to a union of nonempty sets

The nonemptiness hypotheses are necessary for the real-valued infimum distance:
`Metric.infDist x ∅ = 0`. The extended-distance counterpart, `Metric.infEDist_union`,
already holds without them.
-/

public section

namespace Metric

variable {α : Type*} [PseudoMetricSpace α] {s t : Set α}

/-- The distance to a union of two nonempty sets is the minimum of the two
distances. Nonemptiness avoids the convention `infDist x ∅ = 0`. -/
theorem infDist_union (x : α) (hs : s.Nonempty) (ht : t.Nonempty) :
    infDist x (s ∪ t) = min (infDist x s) (infDist x t) := by
  rw [infDist, infEDist_union]
  exact ENNReal.toReal_min (infEDist_ne_top hs) (infEDist_ne_top ht)

end Metric
