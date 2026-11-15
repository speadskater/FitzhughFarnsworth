module

public import FitzhughFarnsworth.LineConfigurations.Translated
public import FitzhughFarnsworth.Convergence.Angles

/-!
# Geometric line-pair dynamics

An evolution retains two distinct line components at every step. Convergence
is pointwise convergence of the distance to their union, rather than global
Hausdorff distance between unbounded sets.
-/

@[expose] public section

namespace FitzhughFarnsworth
namespace Dynamics

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

def carrier (P : LinePair) : Set Point := P.1 ∪ P.2

def swap (P : LinePair) : LinePair := (P.2, P.1)

def map (e : Point ≃ᵢ Point) (P : LinePair) : LinePair := (e '' P.1, e '' P.2)

def ofSlopes (s : SlopePair) : LinePair := (slopeLine s.a, slopeLine s.b)

def ValidOrigin (P : LinePair) : Prop := IsOriginLine P.1 ∧ IsOriginLine P.2 ∧ P.1 ≠ P.2

def ValidAt (v : Point) (P : LinePair) : Prop :=
  IsLineThrough v P.1 ∧ IsLineThrough v P.2 ∧ P.1 ≠ P.2

def Step (P Q : LinePair) : Prop := midset P.1 P.2 = Q.carrier

noncomputable def profile (P : LinePair) (x : Point) : ℝ :=
  min (Metric.infDist x P.1) (Metric.infDist x P.2)

/-- The profile is exactly the metric distance to the geometric union. -/
theorem profile_eq_infDist_carrier (P : LinePair)
    (hA : P.1.Nonempty) (hB : P.2.Nonempty) (x : Point) :
    P.profile x = Metric.infDist x P.carrier := by
  unfold profile carrier
  apply le_antisymm
  · apply (Metric.le_infDist (hA.mono Set.subset_union_left)).mpr
    rintro y (hy | hy)
    · exact (min_le_left _ _).trans (Metric.infDist_le_dist_of_mem hy)
    · exact (min_le_right _ _).trans (Metric.infDist_le_dist_of_mem hy)
  · exact le_min (Metric.infDist_le_infDist_of_subset Set.subset_union_left hA)
      (Metric.infDist_le_infDist_of_subset Set.subset_union_right hB)

theorem profile_eq_infDist_of_valid {v : Point} {P : LinePair}
    (h : P.ValidAt v) (x : Point) : P.profile x = Metric.infDist x P.carrier :=
  profile_eq_infDist_carrier P (lineThrough_nonempty h.1) (lineThrough_nonempty h.2.1) x

inductive OrthogonalOrigin : LinePair → Prop where
  | slopes (s : SlopePair) (h : s.Orthogonal) : OrthogonalOrigin (ofSlopes s)
  | axes : OrthogonalOrigin (horizontalAxis, verticalAxis)
  | swap {P : LinePair} : OrthogonalOrigin P → OrthogonalOrigin P.swap

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

def IsEvolution (v : Point) (u : ℕ → LinePair) : Prop :=
  (∀ n, (u n).ValidAt v) ∧ (∀ n, (u n).Step (u (n + 1)))

open Filter Topology

def ConvergesToCycle (u : ℕ → LinePair) (P Q : LinePair) : Prop :=
  (∀ x, Tendsto (fun n => (u (2 * n)).profile x) atTop (𝓝 (P.profile x))) ∧
  (∀ x, Tendsto (fun n => (u (2 * n + 1)).profile x) atTop (𝓝 (Q.profile x)))

structure TwoCycleAt (v : Point) (P Q : LinePair) : Prop where
  valid_left : P.ValidAt v
  valid_right : Q.ValidAt v
  step_left : P.Step Q
  step_right : Q.Step P
  distinct : P.carrier ≠ Q.carrier
  orthogonal_left : P.OrthogonalAt v
  orthogonal_right : Q.OrthogonalAt v

def HasLimitCycle (v : Point) (u : ℕ → LinePair) : Prop :=
  ∃ P Q : LinePair, TwoCycleAt v P Q ∧ ConvergesToCycle u P Q

end Dynamics
end FitzhughFarnsworth
