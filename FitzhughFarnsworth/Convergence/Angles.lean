/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Convergence
public import FitzhughFarnsworth.LineConfigurations.Euclidean

/-! # Geometric limiting cycles and convergence of the Euclidean angle -/

@[expose] public section

namespace FitzhughFarnsworth
namespace SlopePair

open Filter Topology

/-- Theorems 7 and 9 with an actual geometric cycle of period two:
the limit pairs are distinct, both are orthogonal, and differ by a π/4 rotation. -/
theorem exists_geometric_limit_cycle {s : SlopePair} (h : s.EvenConfig) :
    ∃ l : SlopePair, l.EvenConfig ∧ l.Orthogonal ∧ l.toOdd.Orthogonal ∧
      s.ConvergesToCycle l l.toOdd ∧
      midset (slopeLine l.a) (slopeLine l.b) = l.toOdd.carrier ∧
      midset (slopeLine l.toOdd.a) (slopeLine l.toOdd.b) = l.carrier ∧
      l.carrier ≠ l.toOdd.carrier ∧
      rotate (Real.pi / 4) '' l.carrier = l.toOdd.carrier := by
  obtain ⟨l, hl, ho, hc⟩ := exists_orthogonal_limit_cycle h
  refine ⟨l, hl, ho, toOdd_orthogonal hl ho, hc, midset_eq_toOdd hl,
    (midset_midset_eq_self_iff_even hl).mpr ho, even_odd_carriers_ne hl (toOdd_config hl), ?_⟩
  have ha : |l.a| < 1 := by rw [abs_of_pos hl.1]; exact hl.2.1
  have hb : 1 < |l.b| := by rw [abs_of_neg (by linarith [hl.2.2] : l.b < 0)]; linarith [hl.2.2]
  exact (midset_eq_rotate_of_orthogonal ha hb ho).symm.trans (midset_eq_toOdd hl)

theorem evenOpening_tendsto_of_cycle {s l o : SlopePair} (ha : 0 < l.a)
    (ho : l.Orthogonal) (hc : s.ConvergesToCycle l o) :
    Tendsto (fun n => (s.evenIterate n).evenOpening) atTop (𝓝 (Real.pi / 2)) := by
  have hθ := (Real.continuous_arctan.tendsto l.a).comp hc.1
  have hφ := (Real.continuous_arctan.tendsto l.b).comp hc.2.1
  have hlim : Tendsto (fun n => (s.evenIterate n).evenOpening) atTop (𝓝 l.evenOpening) :=
    (tendsto_const_nhds.add hφ).sub hθ
  rwa [(evenOpening_eq_rightAngle_iff ha).mpr ho] at hlim

theorem evenOpening_tendsto {s : SlopePair} (h : s.EvenConfig) :
    Tendsto (fun n => (s.evenIterate n).evenOpening) atTop (𝓝 (Real.pi / 2)) := by
  obtain ⟨l, hl, ho, hc⟩ := exists_orthogonal_limit_cycle h
  exact evenOpening_tendsto_of_cycle hl.1 ho hc

theorem evenOpening_antitone_of_product_ge {s : SlopePair} (h : s.EvenConfig)
    (hp : -1 ≤ s.a * s.b) : Antitone (fun n => (s.evenIterate n).evenOpening) := by
  intro m n hmn
  exact evenOpening_le_of_slopes (evenIterate_a_monotone_of_product_ge h hp hmn)
    (evenIterate_b_antitone_of_product_ge h hp hmn)

theorem evenOpening_monotone_of_product_le {s : SlopePair} (h : s.EvenConfig)
    (hp : s.a * s.b ≤ -1) : Monotone (fun n => (s.evenIterate n).evenOpening) := by
  intro m n hmn
  exact evenOpening_le_of_slopes (evenIterate_a_antitone_of_product_le h hp hmn)
    (evenIterate_b_monotone_of_product_le h hp hmn)

theorem evenOpening_strictAnti_of_product_gt {s : SlopePair} (h : s.EvenConfig)
    (hp : -1 < s.a * s.b) : StrictAnti (fun n => (s.evenIterate n).evenOpening) := by
  intro m n hmn
  exact evenOpening_lt_of_slopes (evenIterate_a_strictMono_of_product_gt h hp hmn)
    (evenIterate_b_strictAnti_of_product_gt h hp hmn)

theorem evenOpening_strictMono_of_product_lt {s : SlopePair} (h : s.EvenConfig)
    (hp : s.a * s.b < -1) : StrictMono (fun n => (s.evenIterate n).evenOpening) := by
  intro m n hmn
  exact evenOpening_lt_of_slopes (evenIterate_a_strictAnti_of_product_lt h hp hmn)
    (evenIterate_b_strictMono_of_product_lt h hp hmn)

/-- Theorem 8 with precisely the paper's angle relations (in radians). -/
theorem evenIterate_of_angle_symmetry {s t : SlopePair} (h : s.EvenConfig)
    (hθ : Real.arctan t.a = (Real.pi + Real.arctan s.b) - Real.pi / 2)
    (hφ : Real.pi + Real.arctan t.b = Real.arctan s.a + Real.pi / 2) (n : ℕ) :
    t.evenIterate n = (s.evenIterate n).reciprocal := by
  obtain ⟨hθr, hφr⟩ := reciprocal_angle_identities h
  have heq : t = s.reciprocal := by
    ext
    · apply Real.arctan_injective
      exact hθ.trans hθr.symm
    · apply Real.arctan_injective
      linarith
  rw [heq]
  exact evenIterate_reciprocal h n

end SlopePair
end FitzhughFarnsworth
