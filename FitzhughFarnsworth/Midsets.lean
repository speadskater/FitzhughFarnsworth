/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Mathlib.Topology.MetricSpace.Midset

/-!
# Paper compatibility names for metric midsets

The definitions and general results live in the paper-independent `Metric`
namespace. These aliases retain the names used throughout the formalization.
-/

@[expose] public section

namespace FitzhughFarnsworth

/-- Compatibility abbreviation for the generic metric midset. -/
abbrev midset {X : Type*} [PseudoMetricSpace X] (s t : Set X) : Set X := Metric.midset s t

theorem mem_midset {X : Type*} [PseudoMetricSpace X] (p : X) (s t : Set X) :
    p ∈ midset s t ↔ Metric.infDist p s = Metric.infDist p t := Metric.mem_midset p s t

theorem midset_comm {X : Type*} [PseudoMetricSpace X] (s t : Set X) :
    midset s t = midset t s := Metric.midset_comm s t

theorem midset_self {X : Type*} [PseudoMetricSpace X] (s : Set X) :
    midset s s = Set.univ := Metric.midset_self s

theorem inter_subset_midset {X : Type*} [PseudoMetricSpace X] (s t : Set X) :
    s ∩ t ⊆ midset s t := Metric.inter_subset_midset s t

theorem isClosed_midset {X : Type*} [PseudoMetricSpace X] (s t : Set X) :
    IsClosed (midset s t) := Metric.isClosed_midset s t

theorem isometryEquiv_image_midset {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (e : X ≃ᵢ Y) (s t : Set X) :
    e '' midset s t = midset (e '' s) (e '' t) := e.image_midset s t

end FitzhughFarnsworth
