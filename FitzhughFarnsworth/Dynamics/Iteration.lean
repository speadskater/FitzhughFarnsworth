/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Dynamics.Basic

/-!
# An iteration function for arbitrary intersecting lines

Each state contains two distinct lines through the intersection point. The
next-state function chooses a proved decomposition of their geometric midset.
Its only arbitrary feature is component order; `Dynamics.Uniqueness` proves
that the underlying line union is independent of that choice.
-/

@[expose] public section

namespace FitzhughFarnsworth.Dynamics

/-- An ordered pair of distinct nondegenerate lines through the fixed common
point `v`, together with the proof of those geometric conditions. -/
abbrev State (v : Point) := {P : LinePair // P.ValidAt v}

/-- A valid input always admits a valid pair of components for its metric midset. -/
theorem exists_next {v : Point} {P : LinePair} (h : P.ValidAt v) :
    ∃ Q : LinePair, Q.ValidAt v ∧ P.Step Q := by
  obtain ⟨n, _, hr⟩ := reduces_lines_through v h.1 h.2.1 h.2.2
  cases hr with
  | done ht =>
    obtain ⟨A, B, hab, hA, hB⟩ := ht
    obtain ⟨C, D, hC, hD, hne, hm, _⟩ := hab.next
    refine ⟨(translateBy v '' C, translateBy v '' D),
      ⟨⟨C, hC, rfl⟩, ⟨D, hD, rfl⟩, ?_⟩, ?_⟩
    · exact fun he => hne ((translateBy v).injective.image_injective he)
    · change midset P.1 P.2 = (translateBy v '' C) ∪ (translateBy v '' D)
      rw [hA, hB, ← isometryEquiv_image_midset, hm, Set.image_union]
  | step hC hD hne hm _ => exact ⟨(_, _), ⟨hC, hD, hne⟩, hm⟩

/-- Select the next pair of component lines by classical choice from the
proved existence theorem. Its geometric correctness is `next_spec`. -/
noncomputable def next {v : Point} (P : State v) : State v :=
  ⟨Classical.choose (exists_next P.property),
    (Classical.choose_spec (exists_next P.property)).1⟩

/-- The chosen successor has exactly the input lines' metric midset as its union. -/
theorem next_spec {v : Point} (P : State v) : P.val.Step (next P).val :=
  (Classical.choose_spec (exists_next P.property)).2

/-- Apply the geometric midset transition `n` times, retaining validity in the
state type. The index zero is the supplied input pair. -/
noncomputable def iterate {v : Point} (P : State v) : ℕ → State v
  | 0 => P
  | n + 1 => next (iterate P n)

/-- The line components of `iterate`, with their validity proofs erased. -/
noncomputable def evolution {v : Point} (P : State v) (n : ℕ) : LinePair :=
  (iterate P n).val

@[simp] theorem iterate_zero {v : Point} (P : State v) : iterate P 0 = P := rfl

@[simp] theorem iterate_succ {v : Point} (P : State v) (n : ℕ) :
    iterate P (n + 1) = next (iterate P n) := rfl

/-- Restarting the iteration at a finite iterate gives the corresponding tail. -/
theorem iterate_add {v : Point} (P : State v) (m n : ℕ) :
    iterate P (m + n) = iterate (iterate P m) n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Nat.add_succ, iterate_succ, ih]

theorem iterate_succ_eq_iterate_next {v : Point} (P : State v) (n : ℕ) :
    iterate P (n + 1) = iterate (next P) n := by
  simpa only [Nat.add_comm 1 n, iterate_succ, iterate_zero] using iterate_add P 1 n

@[simp] theorem evolution_zero {v : Point} (P : State v) : evolution P 0 = P.val := rfl

@[simp] theorem evolution_succ {v : Point} (P : State v) (n : ℕ) :
    evolution P (n + 1) = (next (iterate P n)).val := rfl

theorem evolution_add {v : Point} (P : State v) (m n : ℕ) :
    evolution P (m + n) = evolution (iterate P m) n :=
  congrArg Subtype.val (iterate_add P m n)

theorem evolution_succ_eq_evolution_next {v : Point} (P : State v) (n : ℕ) :
    evolution P (n + 1) = evolution (next P) n :=
  congrArg Subtype.val (iterate_succ_eq_iterate_next P n)

/-- Every pair produced by the function consists of valid input lines. -/
theorem evolution_valid {v : Point} (P : State v) (n : ℕ) :
    (evolution P n).ValidAt v := (iterate P n).property

/-- Each function transition has the actual metric midset as its output union. -/
theorem evolution_step {v : Point} (P : State v) (n : ℕ) :
    (evolution P n).Step (evolution P (n + 1)) := next_spec (iterate P n)

theorem evolution_isEvolution {v : Point} (P : State v) : IsEvolution v (evolution P) :=
  ⟨evolution_valid P, evolution_step P⟩

/-- Build an initial state directly from two implicit affine equations. -/
def affineState (a b c d e f : ℝ) (v : Point)
    (h₁ : a ≠ 0 ∨ b ≠ 0) (h₂ : d ≠ 0 ∨ e ≠ 0)
    (hv₁ : v ∈ affineLine a b c) (hv₂ : v ∈ affineLine d e f)
    (hne : affineLine a b c ≠ affineLine d e f) : State v :=
  ⟨(affineLine a b c, affineLine d e f),
    affineLine_isLineThrough a b c v h₁ hv₁,
    affineLine_isLineThrough d e f v h₂ hv₂, hne⟩

@[simp] theorem affineState_val (a b c d e f : ℝ) (v : Point)
    (h₁ : a ≠ 0 ∨ b ≠ 0) (h₂ : d ≠ 0 ∨ e ≠ 0)
    (hv₁ : v ∈ affineLine a b c) (hv₂ : v ∈ affineLine d e f)
    (hne : affineLine a b c ≠ affineLine d e f) :
    (affineState a b c d e f v h₁ h₂ hv₁ hv₂ hne).val =
      (affineLine a b c, affineLine d e f) := rfl

end FitzhughFarnsworth.Dynamics
