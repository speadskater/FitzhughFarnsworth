module

public import FitzhughFarnsworth.Dynamics.Uniqueness

/-!
# The finite reduction bound for every actual evolution

Line-component uniqueness transfers the geometric reduction chain to any
valid evolution, regardless of component choices or ordering at each step.
-/

@[expose] public section

namespace FitzhughFarnsworth
namespace Dynamics

theorem attractorPairAt_comm {v : Point} {A B : Set Point} (h : AttractorPairAt v A B) :
    AttractorPairAt v B A := by
  obtain ⟨C, D, hCD, hA, hB⟩ := h
  exact ⟨D, C, AttractorPair.comm hCD, hB, hA⟩

theorem attractorPairAt_of_carrier_eq {v : Point} {P Q : LinePair}
    (hP : P.ValidAt v) (hQ : Q.ValidAt v) (he : P.carrier = Q.carrier)
    (hQattr : AttractorPairAt v Q.1 Q.2) : AttractorPairAt v P.1 P.2 := by
  rcases LinePair.eq_or_eq_swap_of_carrier_eq hP hQ he with rfl | rfl
  · exact hQattr
  · exact attractorPairAt_comm hQattr

theorem IsEvolution.tail {v : Point} {u : ℕ → LinePair} (h : IsEvolution v u) :
    IsEvolution v (fun n => u (n + 1)) :=
  ⟨fun n => h.1 (n + 1), fun n => h.2 (n + 1)⟩

/-- A reduction witness determines the terminal configuration of every valid
evolution whose initial carrier agrees with the witness's input. -/
theorem reductionAt_terminal_of_carrier_eq {v : Point} {n : ℕ} {A B : Set Point}
    (hr : ReducesInAt v n A B) :
    ∀ {u : ℕ → LinePair}, IsEvolution v u → LinePair.ValidAt v (A, B) →
      (u 0).carrier = LinePair.carrier (A, B) → AttractorPairAt v (u n).1 (u n).2 := by
  induction hr with
  | done h =>
    intro u hu hAB h0
    exact attractorPairAt_of_carrier_eq (hu.1 0) hAB h0 h
  | @step n A B C D hC hD hne hm hnext ih =>
    intro u hu hAB h0
    have h1 : (u 1).carrier = LinePair.carrier (C, D) :=
      LinePair.Step.carrier_eq_of_source_eq (hu.1 0) hAB h0 (hu.2 0) hm
    exact ih hu.tail ⟨hC, hD, hne⟩ h1

theorem reductionAt_actual_terminal {v : Point} {n : ℕ} {A B : Set Point}
    (hr : ReducesInAt v n A B) {u : ℕ → LinePair} (hu : IsEvolution v u)
    (h0 : u 0 = (A, B)) : AttractorPairAt v (u n).1 (u n).2 := by
  apply reductionAt_terminal_of_carrier_eq hr hu
  · simpa only [h0] using hu.1 0
  · exact congrArg LinePair.carrier h0

/-- The strengthened two-step bound applies to every actual evolution,
including any implementation that chooses valid line components at each step. -/
theorem IsEvolution.reachesAttractorWithinTwo {v : Point} {u : ℕ → LinePair}
    (hu : IsEvolution v u) : ∃ n ≤ 2, AttractorPairAt v (u n).1 (u n).2 := by
  obtain ⟨n, hn, hr⟩ := reduces_lines_through v (hu.1 0).1 (hu.1 0).2.1 (hu.1 0).2.2
  exact ⟨n, hn, reductionAt_actual_terminal hr hu rfl⟩

end Dynamics
end FitzhughFarnsworth
