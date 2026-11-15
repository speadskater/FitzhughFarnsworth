module

public import FitzhughFarnsworth.Dynamics.Basic

/-!
# Independence of the choice and ordering of line components

A union of two distinct nondegenerate lines through a common point determines
its components up to exchange. Consequently, every valid midset evolution from
the same initial carrier has the same carriers and distance profiles at every
time. Limit-cycle correctness therefore transfers between all such evolutions.
-/

@[expose] public section

namespace FitzhughFarnsworth
namespace Dynamics

theorem originLine_eq_slope_of_mem {A : Set Point} (hA : IsOriginLine A) (m : ℝ)
    (hp : (⟨1, m⟩ : Point) ∈ A) : A = slopeLine m := by
  rcases hA with rfl | ⟨a, rfl⟩
  · norm_num [verticalAxis] at hp
  · have ha : m = a := by simpa [slopeLine] using hp
    rw [ha]

theorem originLine_eq_vertical_of_mem {A : Set Point} (hA : IsOriginLine A)
    (hp : (⟨0, 1⟩ : Point) ∈ A) : A = verticalAxis := by
  rcases hA with rfl | ⟨a, rfl⟩
  · rfl
  · norm_num [slopeLine] at hp

/-- A nondegenerate origin line contained in the union of two origin lines
must be one of them. A point away from the common origin identifies the line. -/
theorem originLine_subset_union {A B C : Set Point}
    (hA : IsOriginLine A) (hB : IsOriginLine B) (hC : IsOriginLine C)
    (hsub : A ⊆ B ∪ C) : A = B ∨ A = C := by
  rcases hA with rfl | ⟨a, rfl⟩
  · have hp := hsub (show (⟨0, 1⟩ : Point) ∈ verticalAxis from rfl)
    rcases hp with hp | hp
    · exact Or.inl (originLine_eq_vertical_of_mem hB hp).symm
    · exact Or.inr (originLine_eq_vertical_of_mem hC hp).symm
  · have hp := hsub (show (⟨1, a⟩ : Point) ∈ slopeLine a by simp [slopeLine])
    rcases hp with hp | hp
    · exact Or.inl (originLine_eq_slope_of_mem hB a hp).symm
    · exact Or.inr (originLine_eq_slope_of_mem hC a hp).symm

namespace LinePair

theorem carrier_decomposition_origin {P Q : LinePair}
    (hP : P.ValidOrigin) (hQ : Q.ValidOrigin) (h : P.carrier = Q.carrier) :
    (P.1 = Q.1 ∧ P.2 = Q.2) ∨ (P.1 = Q.2 ∧ P.2 = Q.1) := by
  have hfirst : P.1 = Q.1 ∨ P.1 = Q.2 :=
    originLine_subset_union hP.1 hQ.1 hQ.2.1 (by
      intro p hp
      have : p ∈ P.carrier := Or.inl hp
      rwa [h] at this)
  have hsecond : P.2 = Q.1 ∨ P.2 = Q.2 :=
    originLine_subset_union hP.2.1 hQ.1 hQ.2.1 (by
      intro p hp
      have : p ∈ P.carrier := Or.inr hp
      rwa [h] at this)
  rcases hfirst with hfirst | hfirst
  · rcases hsecond with hsecond | hsecond
    · exact (hP.2.2 (hfirst.trans hsecond.symm)).elim
    · exact Or.inl ⟨hfirst, hsecond⟩
  · rcases hsecond with hsecond | hsecond
    · exact Or.inr ⟨hfirst, hsecond⟩
    · exact (hP.2.2 (hfirst.trans hsecond.symm)).elim

/-- The line components of a valid carrier are unique up to exchange.
Validity excludes coincident and degenerate components on both sides. -/
theorem carrier_decomposition {v : Point} {P Q : LinePair}
    (hP : P.ValidAt v) (hQ : Q.ValidAt v) (h : P.carrier = Q.carrier) :
    (P.1 = Q.1 ∧ P.2 = Q.2) ∨ (P.1 = Q.2 ∧ P.2 = Q.1) := by
  rcases P with ⟨A, B⟩
  rcases Q with ⟨C, D⟩
  rcases hP with ⟨hA, hB, hAB⟩
  rcases hQ with ⟨hC, hD, hCD⟩
  obtain ⟨A₀, hA₀, rfl⟩ := hA
  obtain ⟨B₀, hB₀, rfl⟩ := hB
  obtain ⟨C₀, hC₀, rfl⟩ := hC
  obtain ⟨D₀, hD₀, rfl⟩ := hD
  have hAB₀ : A₀ ≠ B₀ := by
    intro he
    exact hAB (congrArg (fun S => translateBy v '' S) he)
  have hCD₀ : C₀ ≠ D₀ := by
    intro he
    exact hCD (congrArg (fun S => translateBy v '' S) he)
  have h₀ : carrier (A₀, B₀) = carrier (C₀, D₀) := by
    apply (translateBy v).injective.image_injective
    simpa only [carrier, Set.image_union] using h
  have he := carrier_decomposition_origin
    (P := (A₀, B₀)) (Q := (C₀, D₀)) ⟨hA₀, hB₀, hAB₀⟩ ⟨hC₀, hD₀, hCD₀⟩ h₀
  rcases he with ⟨hAC, hBD⟩ | ⟨hAD, hBC⟩
  · exact Or.inl ⟨congrArg (fun S => translateBy v '' S) hAC,
      congrArg (fun S => translateBy v '' S) hBD⟩
  · exact Or.inr ⟨congrArg (fun S => translateBy v '' S) hAD,
      congrArg (fun S => translateBy v '' S) hBC⟩

theorem eq_or_eq_swap_of_carrier_eq {v : Point} {P Q : LinePair}
    (hP : P.ValidAt v) (hQ : Q.ValidAt v) (h : P.carrier = Q.carrier) :
    P = Q ∨ P = Q.swap := by
  rcases carrier_decomposition hP hQ h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl (Prod.ext h₁ h₂)
  · exact Or.inr (Prod.ext h₁ h₂)

theorem profile_eq_of_carrier_eq {v : Point} {P Q : LinePair}
    (hP : P.ValidAt v) (hQ : Q.ValidAt v) (h : P.carrier = Q.carrier) :
    P.profile = Q.profile := by
  rcases eq_or_eq_swap_of_carrier_eq hP hQ h with rfl | rfl
  · rfl
  · funext x
    exact profile_swap Q x

theorem midset_eq_of_carrier_eq {v : Point} {P Q : LinePair}
    (hP : P.ValidAt v) (hQ : Q.ValidAt v) (h : P.carrier = Q.carrier) :
    midset P.1 P.2 = midset Q.1 Q.2 := by
  rcases eq_or_eq_swap_of_carrier_eq hP hQ h with rfl | rfl
  · rfl
  · exact midset_comm _ _

theorem Step.carrier_eq_of_source_eq {v : Point} {P Q P' Q' : LinePair}
    (hP : P.ValidAt v) (hQ : Q.ValidAt v) (h : P.carrier = Q.carrier)
    (hP' : P.Step P') (hQ' : Q.Step Q') : P'.carrier = Q'.carrier :=
  hP'.symm.trans ((midset_eq_of_carrier_eq hP hQ h).trans hQ')

end LinePair

/-- The carrier at each time is determined by the initial carrier, independently
of which valid component ordering is selected at any intermediate step. -/
theorem IsEvolution.carrier_eq {v : Point} {u w : ℕ → LinePair}
    (hu : IsEvolution v u) (hw : IsEvolution v w)
    (h₀ : (u 0).carrier = (w 0).carrier) (n : ℕ) : (u n).carrier = (w n).carrier := by
  induction n with
  | zero => exact h₀
  | succ n ih =>
    exact LinePair.Step.carrier_eq_of_source_eq
      (hu.1 n) (hw.1 n) ih (hu.2 n) (hw.2 n)

theorem IsEvolution.components_eq_or_swap {v : Point} {u w : ℕ → LinePair}
    (hu : IsEvolution v u) (hw : IsEvolution v w)
    (h₀ : (u 0).carrier = (w 0).carrier) (n : ℕ) :
    u n = w n ∨ u n = (w n).swap :=
  LinePair.eq_or_eq_swap_of_carrier_eq (hu.1 n) (hw.1 n) (hu.carrier_eq hw h₀ n)

theorem IsEvolution.profile_eq {v : Point} {u w : ℕ → LinePair}
    (hu : IsEvolution v u) (hw : IsEvolution v w)
    (h₀ : (u 0).carrier = (w 0).carrier) (n : ℕ) : (u n).profile = (w n).profile :=
  LinePair.profile_eq_of_carrier_eq (hu.1 n) (hw.1 n) (hu.carrier_eq hw h₀ n)

theorem ConvergesToCycle.congr_profiles {u w : ℕ → LinePair} {P Q : LinePair}
    (h : ConvergesToCycle u P Q) (hprof : ∀ n, (u n).profile = (w n).profile) :
    ConvergesToCycle w P Q := by
  constructor
  · intro x
    simpa only [hprof] using h.1 x
  · intro x
    simpa only [hprof] using h.2 x

/-- A verified limiting cycle of one valid evolution is also the limiting
cycle of every other valid evolution with the same initial carrier. -/
theorem HasLimitCycle.congr {v : Point} {u w : ℕ → LinePair}
    (h : HasLimitCycle v u) (hu : IsEvolution v u) (hw : IsEvolution v w)
    (h₀ : (u 0).carrier = (w 0).carrier) : HasLimitCycle v w := by
  obtain ⟨P, Q, hcycle, hconv⟩ := h
  exact ⟨P, Q, hcycle, hconv.congr_profiles (hu.profile_eq hw h₀)⟩

theorem IsEvolution.hasLimitCycle_iff {v : Point} {u w : ℕ → LinePair}
    (hu : IsEvolution v u) (hw : IsEvolution v w)
    (h₀ : (u 0).carrier = (w 0).carrier) : HasLimitCycle v u ↔ HasLimitCycle v w :=
  ⟨fun h => h.congr hu hw h₀, fun h => h.congr hw hu h₀.symm⟩

end Dynamics
end FitzhughFarnsworth
