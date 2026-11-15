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

abbrev State (v : Point) := {P : LinePair // P.ValidAt v}

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

theorem next_spec {v : Point} (P : State v) : P.val.Step (next P).val :=
  (Classical.choose_spec (exists_next P.property)).2

noncomputable def iterate {v : Point} (P : State v) : ℕ → State v
  | 0 => P
  | n + 1 => next (iterate P n)

noncomputable def evolution {v : Point} (P : State v) (n : ℕ) : LinePair :=
  (iterate P n).val

@[simp] theorem evolution_zero {v : Point} (P : State v) : evolution P 0 = P.val := rfl

theorem evolution_valid {v : Point} (P : State v) (n : ℕ) :
    (evolution P n).ValidAt v := (iterate P n).property

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

end FitzhughFarnsworth.Dynamics
