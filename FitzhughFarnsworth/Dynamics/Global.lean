module

public import FitzhughFarnsworth.Dynamics.Canonical

/-!
# An end-to-end geometric evolution for every valid intersecting pair

The finite reduction chain is concatenated with an actual infinite attracting
evolution. Each prefix step retains its metric-midset equality. Translation
then carries the entire function, and its limiting cycle, to the given common
point of the input lines.
-/

@[expose] public section

namespace FitzhughFarnsworth
namespace Dynamics

theorem reduction_exists_evolution {n : ℕ} {A B : Set Point} (hr : ReducesIn n A B) :
    LinePair.ValidOrigin (A, B) →
      ∃ u : ℕ → LinePair, u 0 = (A, B) ∧ IsEvolution origin u ∧ HasLimitCycle origin u := by
  induction hr with
  | done h =>
    intro _
    exact attractorPair_exists_evolution h
  | @step n A B C D hC hD hne hm hnext ih =>
    intro hAB
    obtain ⟨u, hu, he, hc⟩ := ih ⟨hC, hD, hne⟩
    refine ⟨prepend (A, B) u, rfl,
      isEvolution_prepend he hAB.validAt_origin ?_, hc.prepend (A, B)⟩
    rw [hu]
    exact hm

theorem validOrigin_exists_evolution {P : LinePair} (h : P.ValidOrigin) :
    ∃ u : ℕ → LinePair, u 0 = P ∧ IsEvolution origin u ∧ HasLimitCycle origin u := by
  obtain ⟨n, _, hr⟩ := reduces_origin_lines h.1 h.2.1 h.2.2
  exact reduction_exists_evolution hr h

/-- Every pair of distinct nondegenerate lines through `v` has a complete
geometric evolution converging to an actual orthogonal two-cycle. -/
theorem validPair_exists_evolution {v : Point} {P : LinePair} (h : P.ValidAt v) :
    ∃ u : ℕ → LinePair, u 0 = P ∧ IsEvolution v u ∧ HasLimitCycle v u := by
  obtain ⟨Q, hQ, rfl⟩ := h.exists_origin
  obtain ⟨u, hu, he, hc⟩ := validOrigin_exists_evolution hQ
  refine ⟨fun n => (u n).map (translateBy v), ?_, he.translate v, hc.translate v⟩
  exact congrArg (fun P : LinePair => P.map (translateBy v)) hu

/-- Coordinate-facing form: arbitrary affine equations and their common point
are the inputs; all intermediate objects are genuine line-pair midsets. -/
theorem affinePair_exists_evolution
    (a b c d e f : ℝ) (v : Point)
    (h₁ : a ≠ 0 ∨ b ≠ 0) (h₂ : d ≠ 0 ∨ e ≠ 0)
    (hv₁ : v ∈ affineLine a b c) (hv₂ : v ∈ affineLine d e f)
    (hne : affineLine a b c ≠ affineLine d e f) :
    ∃ u : ℕ → LinePair, u 0 = (affineLine a b c, affineLine d e f) ∧
      IsEvolution v u ∧ HasLimitCycle v u :=
  validPair_exists_evolution
    ⟨affineLine_isLineThrough a b c v h₁ hv₁,
      affineLine_isLineThrough d e f v h₂ hv₂, hne⟩

end Dynamics
end FitzhughFarnsworth
