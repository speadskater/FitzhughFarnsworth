/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.LineConfigurations.Translated
public import FitzhughFarnsworth.Mathlib.Topology.MetricSpace.InfDist

/-!
# Geometric line-pair dynamics

An evolution retains two distinct line components at every step. Convergence
is pointwise convergence of the distance to their union, rather than global
Hausdorff distance between unbounded sets.
-/

@[expose] public section

namespace FitzhughFarnsworth
namespace Dynamics

/-- An ordered pair of point sets. The sets represent distinct lines when
accompanied by a `LinePair.ValidAt` or `LinePair.ValidOrigin` proof. -/
abbrev LinePair := Set Point × Set Point

theorem originLine_nonempty {A : Set Point} (h : IsOriginLine A) : A.Nonempty := by
  rcases h with rfl | ⟨a, rfl⟩
  · exact verticalAxis_nonempty
  · exact slopeLine_nonempty a

theorem lineThrough_nonempty {v : Point} {A : Set Point} (h : IsLineThrough v A) :
    A.Nonempty := by
  obtain ⟨L, hL, rfl⟩ := h
  exact (originLine_nonempty hL).image _

namespace LinePair

/-- The union of the two component sets of a line pair. -/
def carrier (P : LinePair) : Set Point := P.1 ∪ P.2

/-- Exchange the component labels of a line pair. -/
def swap (P : LinePair) : LinePair := (P.2, P.1)

/-- Apply an isometry equivalence to both component sets. -/
def map (e : Point ≃ᵢ Point) (P : LinePair) : LinePair := (e '' P.1, e '' P.2)

/-- The ordered pair of origin-centered lines with the given finite slopes. -/
def ofSlopes (s : SlopePair) : LinePair := (slopeLine s.a, slopeLine s.b)

/-- Both components are nondegenerate lines through the origin, and they are
distinct as sets. Vertical lines are included. -/
def ValidOrigin (P : LinePair) : Prop := IsOriginLine P.1 ∧ IsOriginLine P.2 ∧ P.1 ≠ P.2

/-- Both components are distinct nondegenerate affine lines through `v`. -/
def ValidAt (v : Point) (P : LinePair) : Prop :=
  IsLineThrough v P.1 ∧ IsLineThrough v P.2 ∧ P.1 ≠ P.2

/-- The union of the target components is the geometric midset of the source
components. Validity of either pair is a separate condition. -/
def Step (P Q : LinePair) : Prop := midset P.1 P.2 = Q.carrier

/-- The minimum of the distances to the two components. For nonempty
components this equals distance to their union, by `profile_eq_infDist_carrier`. -/
noncomputable def profile (P : LinePair) (x : Point) : ℝ :=
  min (Metric.infDist x P.1) (Metric.infDist x P.2)

/-- The profile is exactly the metric distance to the geometric union. -/
theorem profile_eq_infDist_carrier (P : LinePair)
    (hA : P.1.Nonempty) (hB : P.2.Nonempty) (x : Point) :
    P.profile x = Metric.infDist x P.carrier := by
  exact (Metric.infDist_union x hA hB).symm

theorem profile_eq_infDist_of_valid {v : Point} {P : LinePair}
    (h : P.ValidAt v) (x : Point) : P.profile x = Metric.infDist x P.carrier :=
  profile_eq_infDist_carrier P (lineThrough_nonempty h.1) (lineThrough_nonempty h.2.1) x

/-- Euclidean-orthogonal origin-centered line pairs, including the coordinate
axes and either ordering of the components. -/
inductive OrthogonalOrigin : LinePair → Prop where
  /-- The finite-slope directions `(1, s.a)` and `(1, s.b)` are orthogonal. -/
  | slopes (s : SlopePair) (h : s.Orthogonal) : OrthogonalOrigin (ofSlopes s)
  /-- The horizontal and vertical coordinate axes are orthogonal. -/
  | axes : OrthogonalOrigin (horizontalAxis, verticalAxis)
  /-- Exchanging component labels preserves orthogonality. -/
  | swap {P : LinePair} : OrthogonalOrigin P → OrthogonalOrigin P.swap

/-- A Euclidean-orthogonal pair through `v`, represented as the translation
of an orthogonal origin-centered pair. -/
def OrthogonalAt (v : Point) (P : LinePair) : Prop :=
  ∃ Q : LinePair, Q.OrthogonalOrigin ∧ P = Q.map (translateBy v)

@[simp] theorem carrier_swap (P : LinePair) : P.swap.carrier = P.carrier := Set.union_comm _ _

@[simp] theorem profile_swap (P : LinePair) (x : Point) : P.swap.profile x = P.profile x :=
  min_comm _ _

theorem Step.swap_left {P Q : LinePair} (h : P.Step Q) : P.swap.Step Q := by
  change midset P.2 P.1 = Q.carrier
  rw [midset_comm]
  exact h

theorem Step.swap_right {P Q : LinePair} (h : P.Step Q) : P.Step Q.swap := by
  simpa only [Step, carrier_swap] using h

theorem Step.map {P Q : LinePair} (h : P.Step Q) (e : Point ≃ᵢ Point) :
    (P.map e).Step (Q.map e) := by
  change midset (e '' P.1) (e '' P.2) = (e '' Q.1) ∪ (e '' Q.2)
  rw [← isometryEquiv_image_midset, ← Set.image_union, h]
  rfl

theorem profile_map (P : LinePair) (e : Point ≃ᵢ Point) (x : Point) :
    (P.map e).profile (e x) = P.profile x := by
  simp only [profile, map, Metric.infDist_image e.isometry]

end LinePair

/-- Every state consists of distinct lines through `v`, and the union at each
successor index is the geometric midset of the preceding component lines. -/
def IsEvolution (v : Point) (u : ℕ → LinePair) : Prop :=
  (∀ n, (u n).ValidAt v) ∧ (∀ n, (u n).Step (u (n + 1)))

/-- Every state of a geometric evolution is a valid pair of lines. -/
theorem IsEvolution.valid {v : Point} {u : ℕ → LinePair} (h : IsEvolution v u) (n : ℕ) :
    (u n).ValidAt v := h.1 n

/-- Every transition of a geometric evolution is a genuine midset step. -/
theorem IsEvolution.step {v : Point} {u : ℕ → LinePair} (h : IsEvolution v u) (n : ℕ) :
    (u n).Step (u (n + 1)) := h.2 n

open Filter Topology

/-- Pointwise convergence of even and odd distance profiles to the profiles
of `P` and `Q`, respectively. Genuine cycle conditions are supplied separately
by `TwoCycleAt`; this is not global Hausdorff convergence of unbounded sets. -/
def ConvergesToCycle (u : ℕ → LinePair) (P Q : LinePair) : Prop :=
  (∀ x, Tendsto (fun n => (u (2 * n)).profile x) atTop (𝓝 (P.profile x))) ∧
  (∀ x, Tendsto (fun n => (u (2 * n + 1)).profile x) atTop (𝓝 (Q.profile x)))

/-- A genuine geometric two-cycle of Euclidean-orthogonal line pairs through
`v`. Distinct carriers make its period exactly two. -/
structure TwoCycleAt (v : Point) (P Q : LinePair) : Prop where
  /-- The first pair consists of distinct nondegenerate lines through `v`. -/
  valid_left : P.ValidAt v
  /-- The second pair consists of distinct nondegenerate lines through `v`. -/
  valid_right : Q.ValidAt v
  /-- Taking the midset of the first pair produces the second carrier. -/
  step_left : P.Step Q
  /-- Taking the midset of the second pair produces the first carrier. -/
  step_right : Q.Step P
  /-- The two geometric carriers are different, independently of component labels. -/
  distinct : P.carrier ≠ Q.carrier
  /-- The first pair is Euclidean-orthogonal. -/
  orthogonal_left : P.OrthogonalAt v
  /-- The second pair is Euclidean-orthogonal. -/
  orthogonal_right : Q.OrthogonalAt v

/-- A sequence approaches a genuine orthogonal geometric two-cycle through
`v` along its parity subsequences. Validity of the sequence itself is separate. -/
def HasLimitCycle (v : Point) (u : ℕ → LinePair) : Prop :=
  ∃ P Q : LinePair, TwoCycleAt v P Q ∧ ConvergesToCycle u P Q

end Dynamics
end FitzhughFarnsworth
