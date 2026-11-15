module

public import FitzhughFarnsworth.IteratedMidsets
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Convergence specification

Convergence means convergence of both parity subsequences, not convergence of
the full alternating sequence. Theorems 7–9 remain proof obligations; this
module deliberately introduces no axioms or placeholder proofs for them.
-/

@[expose] public section

namespace FitzhughFarnsworth
namespace SlopePair

open Filter Topology

def ConvergesToCycle (s evenLimit oddLimit : SlopePair) : Prop :=
  Tendsto (fun n => (s.evenIterate n).a) atTop (𝓝 evenLimit.a) ∧
  Tendsto (fun n => (s.evenIterate n).b) atTop (𝓝 evenLimit.b) ∧
  Tendsto (fun n => (s.oddIterate n).a) atTop (𝓝 oddLimit.a) ∧
  Tendsto (fun n => (s.oddIterate n).b) atTop (𝓝 oddLimit.b)

theorem evenIterate_eq_of_fixed (s : SlopePair) (h : s.twoStep = s) (n : ℕ) :
    s.evenIterate n = s := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [evenIterate, ih] using h

/-- A fixed point of the two-step map gives constant parity subsequences.
This does not assert existence of a limit for arbitrary initial lines. -/
theorem convergesToCycle_of_fixed (s : SlopePair) (h : s.twoStep = s) :
    s.ConvergesToCycle s s.toOdd := by
  have he : s.evenIterate = fun _ => s := funext (evenIterate_eq_of_fixed s h)
  simp only [ConvergesToCycle, oddIterate, he]
  exact ⟨tendsto_const_nhds, tendsto_const_nhds, tendsto_const_nhds, tendsto_const_nhds⟩

end SlopePair
end FitzhughFarnsworth
