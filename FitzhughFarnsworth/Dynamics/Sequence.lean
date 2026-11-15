module

public import FitzhughFarnsworth.Dynamics.Basic

/-! # Prefixes and translations of genuine geometric evolutions -/

@[expose] public section

namespace FitzhughFarnsworth
namespace Dynamics

@[simp] theorem translateBy_origin_apply (p : Point) : translateBy origin p = p := by
  ext <;> simp [translateBy, origin]

@[simp] theorem translateBy_origin_image (A : Set Point) : translateBy origin '' A = A := by
  simpa only [Set.image_id] using
    (show translateBy origin '' A = id '' A from Set.image_congr fun p _ => translateBy_origin_apply p)

namespace LinePair

@[simp] theorem map_translate_origin (P : LinePair) : P.map (translateBy origin) = P := by
  ext <;> simp [map]

theorem validAt_origin_iff {P : LinePair} : P.ValidAt origin ↔ P.ValidOrigin := by
  constructor
  · rintro ⟨⟨A, hA, hAP⟩, ⟨B, hB, hBP⟩, hne⟩
    simp only [translateBy_origin_image] at hAP hBP
    exact ⟨hAP ▸ hA, hBP ▸ hB, hne⟩
  · rintro ⟨hA, hB, hne⟩
    exact ⟨⟨P.1, hA, (translateBy_origin_image P.1).symm⟩,
      ⟨P.2, hB, (translateBy_origin_image P.2).symm⟩, hne⟩

theorem ValidOrigin.validAt_origin {P : LinePair} (h : P.ValidOrigin) : P.ValidAt origin :=
  validAt_origin_iff.mpr h

theorem orthogonalAt_origin_iff {P : LinePair} : P.OrthogonalAt origin ↔ P.OrthogonalOrigin := by
  constructor
  · rintro ⟨Q, hQ, he⟩
    simp only [map_translate_origin] at he
    exact he ▸ hQ
  · intro h
    exact ⟨P, h, (map_translate_origin P).symm⟩

theorem OrthogonalOrigin.orthogonalAt_origin {P : LinePair} (h : P.OrthogonalOrigin) :
    P.OrthogonalAt origin := orthogonalAt_origin_iff.mpr h

theorem ValidOrigin.translate {P : LinePair} (h : P.ValidOrigin) (v : Point) :
    (P.map (translateBy v)).ValidAt v := by
  exact ⟨⟨P.1, h.1, rfl⟩, ⟨P.2, h.2.1, rfl⟩,
    fun he => h.2.2 ((translateBy v).injective.image_injective he)⟩

theorem ValidAt.exists_origin {P : LinePair} {v : Point} (h : P.ValidAt v) :
    ∃ Q : LinePair, Q.ValidOrigin ∧ P = Q.map (translateBy v) := by
  obtain ⟨⟨A, hA, hAP⟩, ⟨B, hB, hBP⟩, hne⟩ := h
  refine ⟨(A, B), ⟨hA, hB, ?_⟩, ?_⟩
  · intro he
    change A = B at he
    apply hne
    rw [hAP, hBP, he]
  · exact Prod.ext hAP hBP

theorem carrier_map (P : LinePair) (e : Point ≃ᵢ Point) :
    (P.map e).carrier = e '' P.carrier := by
  exact (Set.image_union e P.1 P.2).symm

end LinePair

def prepend (P : LinePair) (u : ℕ → LinePair) : ℕ → LinePair
  | 0 => P
  | n + 1 => u n

@[simp] theorem prepend_zero (P : LinePair) (u : ℕ → LinePair) : prepend P u 0 = P := rfl

@[simp] theorem prepend_succ (P : LinePair) (u : ℕ → LinePair) (n : ℕ) :
    prepend P u (n + 1) = u n := rfl

theorem isEvolution_prepend {v : Point} {u : ℕ → LinePair} {P : LinePair}
    (hu : IsEvolution v u) (hP : P.ValidAt v) (hstep : P.Step (u 0)) :
    IsEvolution v (prepend P u) := by
  constructor
  · intro n
    cases n with
    | zero => exact hP
    | succ n => exact hu.1 n
  · intro n
    cases n with
    | zero => exact hstep
    | succ n => exact hu.2 n

theorem TwoCycleAt.flip {v : Point} {P Q : LinePair} (h : TwoCycleAt v P Q) :
    TwoCycleAt v Q P :=
  ⟨h.valid_right, h.valid_left, h.step_right, h.step_left, Ne.symm h.distinct,
    h.orthogonal_right, h.orthogonal_left⟩

open Filter Topology

theorem ConvergesToCycle.prepend {u : ℕ → LinePair} {P Q : LinePair}
    (h : ConvergesToCycle u P Q) (R : LinePair) :
    ConvergesToCycle (Dynamics.prepend R u) Q P := by
  constructor
  · intro x
    apply (tendsto_add_atTop_iff_nat 1).mp
    have he : (fun n => (Dynamics.prepend R u (2 * (n + 1))).profile x) =
        (fun n => (u (2 * n + 1)).profile x) := by
      funext n
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, prepend_succ]
    rw [he]
    exact h.2 x
  · intro x
    exact h.1 x

theorem HasLimitCycle.prepend {v : Point} {u : ℕ → LinePair}
    (h : HasLimitCycle v u) (P : LinePair) : HasLimitCycle v (prepend P u) := by
  obtain ⟨Q, R, hcycle, hlim⟩ := h
  exact ⟨R, Q, hcycle.flip, hlim.prepend P⟩

theorem ConvergesToCycle.map {u : ℕ → LinePair} {P Q : LinePair}
    (h : ConvergesToCycle u P Q) (e : Point ≃ᵢ Point) :
    ConvergesToCycle (fun n => (u n).map e) (P.map e) (Q.map e) := by
  constructor
  · intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    simpa only [LinePair.profile_map] using h.1 y
  · intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    simpa only [LinePair.profile_map] using h.2 y

theorem IsEvolution.translate {u : ℕ → LinePair} (h : IsEvolution origin u) (v : Point) :
    IsEvolution v (fun n => (u n).map (translateBy v)) := by
  constructor
  · intro n
    exact (LinePair.validAt_origin_iff.mp (h.1 n)).translate v
  · intro n
    exact (h.2 n).map (translateBy v)

theorem TwoCycleAt.translate {P Q : LinePair} (h : TwoCycleAt origin P Q) (v : Point) :
    TwoCycleAt v (P.map (translateBy v)) (Q.map (translateBy v)) := by
  refine ⟨(LinePair.validAt_origin_iff.mp h.valid_left).translate v,
    (LinePair.validAt_origin_iff.mp h.valid_right).translate v,
    h.step_left.map _, h.step_right.map _, ?_, ?_, ?_⟩
  · intro he
    rw [LinePair.carrier_map, LinePair.carrier_map] at he
    exact h.distinct ((translateBy v).injective.image_injective he)
  · exact ⟨P, LinePair.orthogonalAt_origin_iff.mp h.orthogonal_left, rfl⟩
  · exact ⟨Q, LinePair.orthogonalAt_origin_iff.mp h.orthogonal_right, rfl⟩

theorem HasLimitCycle.translate {u : ℕ → LinePair} (h : HasLimitCycle origin u) (v : Point) :
    HasLimitCycle v (fun n => (u n).map (translateBy v)) := by
  obtain ⟨P, Q, hcycle, hlim⟩ := h
  exact ⟨P.map (translateBy v), Q.map (translateBy v), hcycle.translate v,
    hlim.map (translateBy v)⟩

end Dynamics
end FitzhughFarnsworth
