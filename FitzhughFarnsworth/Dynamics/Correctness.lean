/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Dynamics.Iteration
public import FitzhughFarnsworth.Dynamics.Global
public import FitzhughFarnsworth.Dynamics.Uniqueness
public import FitzhughFarnsworth.Dynamics.Rotation
public import FitzhughFarnsworth.Dynamics.Reduction

/-!
# End-to-end correctness of geometric midset iteration

The final theorems start from arbitrary distinct intersecting lines. Every
iterate is a genuine geometric midset, and the complete sequence converges
along its two parity subsequences to an orthogonal geometric two-cycle.
Uniqueness of line decomposition makes the result independent of component
ordering at every step.
-/

@[expose] public section

namespace FitzhughFarnsworth.Dynamics

open Filter Topology

/-- Every genuine iteration converges, not just the particular one constructed
by splicing a finite reduction into a canonical slope sequence. -/
theorem every_evolution_converges {v : Point} {u : ℕ → LinePair}
    (hu : IsEvolution v u) : HasLimitCycle v u := by
  obtain ⟨w, hw0, hw, hc⟩ := validPair_exists_evolution (hu.valid 0)
  exact hc.congr hw hu (congrArg LinePair.carrier hw0)

theorem evolution_hasLimitCycle {v : Point} (P : State v) :
    HasLimitCycle v (evolution P) := every_evolution_converges (evolution_isEvolution P)

theorem evolution_reaches_attractor_within_two {v : Point} (P : State v) :
    ∃ n ≤ 2, AttractorPairAt v (evolution P n).1 (evolution P n).2 :=
  (evolution_isEvolution P).reachesAttractorWithinTwo

/-- The defined iteration agrees with every other valid iteration from the
same geometric input, even when their component labels differ at each step. -/
theorem evolution_agrees_with_every_valid_iteration {v : Point} (P : State v)
    {u : ℕ → LinePair} (hu : IsEvolution v u)
    (h0 : P.val.carrier = (u 0).carrier) (n : ℕ) :
    (evolution P n).carrier = (u n).carrier :=
  (evolution_isEvolution P).carrier_eq hu h0 n

/-- A canonical slope pair as an input to the general geometric iteration. -/
def canonicalState (s : SlopePair) (h : s.EvenConfig) : State origin :=
  ⟨LinePair.ofSlopes s, valid_ofSlopes_even h⟩

@[simp] theorem canonicalState_val (s : SlopePair) (h : s.EvenConfig) :
    (canonicalState s h).val = LinePair.ofSlopes s := rfl

/-- The general iteration extends the already verified slope algorithm. -/
theorem evolution_agrees_with_canonical (s : SlopePair) (h : s.EvenConfig) (n : ℕ) :
    (evolution (canonicalState s h) n).carrier = (canonicalEvolution s n).carrier := by
  apply evolution_agrees_with_every_valid_iteration _ (canonicalEvolution_isEvolution h)
  simp only [canonicalState_val, canonicalEvolution_zero]

theorem evolution_even_agrees_with_slopes (s : SlopePair) (h : s.EvenConfig) (n : ℕ) :
    (evolution (canonicalState s h) (2 * n)).carrier =
      slopeLine (s.evenIterate n).a ∪ slopeLine (s.evenIterate n).b := by
  simpa only [canonicalEvolution_even, LinePair.carrier, LinePair.ofSlopes] using
    evolution_agrees_with_canonical s h (2 * n)

theorem evolution_odd_agrees_with_slopes (s : SlopePair) (h : s.EvenConfig) (n : ℕ) :
    (evolution (canonicalState s h) (2 * n + 1)).carrier =
      slopeLine (s.oddIterate n).a ∪ slopeLine (s.oddIterate n).b := by
  simpa only [canonicalEvolution_odd, LinePair.carrier, LinePair.ofSlopes] using
    evolution_agrees_with_canonical s h (2 * n + 1)

/-- The even distance profiles converge to the distance from the left limiting
union. Only validity of that limit pair is needed for this parity. -/
theorem ConvergesToCycle.infDist_even {v : Point} {u : ℕ → LinePair} {P Q : LinePair}
    (h : ConvergesToCycle u P Q) (hu : IsEvolution v u) (hP : P.ValidAt v) (x : Point) :
    Tendsto (fun n => Metric.infDist x (u (2 * n)).carrier) atTop
      (𝓝 (Metric.infDist x P.carrier)) := by
  have hsource (n : ℕ) := LinePair.profile_eq_infDist_of_valid (hu.valid (2 * n)) x
  simpa only [hsource, LinePair.profile_eq_infDist_of_valid hP x] using h.1 x

/-- The odd distance profiles converge to the distance from the right limiting
union. Only validity of that limit pair is needed for this parity. -/
theorem ConvergesToCycle.infDist_odd {v : Point} {u : ℕ → LinePair} {P Q : LinePair}
    (h : ConvergesToCycle u P Q) (hu : IsEvolution v u) (hQ : Q.ValidAt v) (x : Point) :
    Tendsto (fun n => Metric.infDist x (u (2 * n + 1)).carrier) atTop
      (𝓝 (Metric.infDist x Q.carrier)) := by
  have hsource (n : ℕ) := LinePair.profile_eq_infDist_of_valid (hu.valid (2 * n + 1)) x
  simpa only [hsource, LinePair.profile_eq_infDist_of_valid hQ x] using h.2 x

/-- Both parity limits expressed as metric distances to the geometric unions.
The individual statements are `ConvergesToCycle.infDist_even` and
`ConvergesToCycle.infDist_odd`. -/
theorem ConvergesToCycle.infDist {v : Point} {u : ℕ → LinePair} {P Q : LinePair}
    (h : ConvergesToCycle u P Q) (hu : IsEvolution v u)
    (hP : P.ValidAt v) (hQ : Q.ValidAt v) :
    (∀ x, Tendsto (fun n => Metric.infDist x (u (2 * n)).carrier) atTop
      (𝓝 (Metric.infDist x P.carrier))) ∧
    (∀ x, Tendsto (fun n => Metric.infDist x (u (2 * n + 1)).carrier) atTop
      (𝓝 (Metric.infDist x Q.carrier))) :=
  ⟨h.infDist_even hu hP, h.infDist_odd hu hQ⟩

/-- Any valid evolution has an orthogonal geometric limit cycle with the
paper's rotation relation and pointwise distance limits. -/
theorem IsEvolution.exists_geometric_limit {v : Point} {u : ℕ → LinePair}
    (hu : IsEvolution v u) :
    ∃ L R : LinePair, TwoCycleAt v L R ∧
      R.carrier = rotateAbout v (Real.pi / 4) '' L.carrier ∧
      (∀ x, Tendsto (fun n => Metric.infDist x (u (2 * n)).carrier) atTop
        (𝓝 (Metric.infDist x L.carrier))) ∧
      (∀ x, Tendsto (fun n => Metric.infDist x (u (2 * n + 1)).carrier) atTop
        (𝓝 (Metric.infDist x R.carrier))) := by
  obtain ⟨L, R, hcycle, hconv⟩ := every_evolution_converges hu
  exact ⟨L, R, hcycle, hcycle.rotate,
    hconv.infDist hu hcycle.valid_left hcycle.valid_right⟩

/-- The geometric limit conclusions for the defined iteration, independently
of its initial-state and finite-reduction assertions. -/
theorem evolution_geometric_limit {v : Point} (P : State v) :
    ∃ L R : LinePair, TwoCycleAt v L R ∧
      R.carrier = rotateAbout v (Real.pi / 4) '' L.carrier ∧
      (∀ x, Tendsto (fun n => Metric.infDist x (evolution P (2 * n)).carrier) atTop
        (𝓝 (Metric.infDist x L.carrier))) ∧
      (∀ x, Tendsto (fun n => Metric.infDist x (evolution P (2 * n + 1)).carrier) atTop
        (𝓝 (Metric.infDist x R.carrier))) :=
  (evolution_isEvolution P).exists_geometric_limit

/-- Complete correctness of the defined general iteration. -/
theorem evolution_end_to_end {v : Point} (P : State v) :
    evolution P 0 = P.val ∧ IsEvolution v (evolution P) ∧
      (∃ n ≤ 2, AttractorPairAt v (evolution P n).1 (evolution P n).2) ∧
      ∃ L R : LinePair, TwoCycleAt v L R ∧
        R.carrier = rotateAbout v (Real.pi / 4) '' L.carrier ∧
        (∀ x, Tendsto (fun n => Metric.infDist x (evolution P (2 * n)).carrier) atTop
          (𝓝 (Metric.infDist x L.carrier))) ∧
        (∀ x, Tendsto (fun n => Metric.infDist x (evolution P (2 * n + 1)).carrier) atTop
          (𝓝 (Metric.infDist x R.carrier))) :=
  ⟨evolution_zero P, evolution_isEvolution P, evolution_reaches_attractor_within_two P,
    evolution_geometric_limit P⟩

/-- A coordinate-facing entry point: distinct nondegenerate affine equations
with a common point generate a valid iteration converging to a genuine
orthogonal geometric two-cycle. -/
theorem intersecting_affine_lines_end_to_end
    (a b c d e f : ℝ) (v : Point)
    (h₁ : a ≠ 0 ∨ b ≠ 0) (h₂ : d ≠ 0 ∨ e ≠ 0)
    (hv₁ : v ∈ affineLine a b c) (hv₂ : v ∈ affineLine d e f)
    (hne : affineLine a b c ≠ affineLine d e f) :
    let P := affineState a b c d e f v h₁ h₂ hv₁ hv₂ hne
    evolution P 0 = (affineLine a b c, affineLine d e f) ∧
      IsEvolution v (evolution P) ∧ HasLimitCycle v (evolution P) := by
  dsimp only
  refine ⟨?_, evolution_isEvolution _, evolution_hasLimitCycle _⟩
  simp only [evolution_zero, affineState_val]

end FitzhughFarnsworth.Dynamics
