/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.IteratedMidsets
public import FitzhughFarnsworth.Convergence.Monotonicity
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Convergence of the canonical iteration

Convergence means convergence of both parity subsequences, not convergence of
the full alternating sequence. Both even slope sequences are proved bounded
and monotone, their limits remain inside the canonical region, and the rational
recurrence identifies the limiting orthogonal two-cycle.
-/

@[expose] public section

namespace FitzhughFarnsworth
namespace SlopePair

open Filter Topology

/-- Convergence of both coordinates along each parity subsequence of Algorithm 6. -/
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

theorem tendsto_toOdd {u : ℕ → SlopePair} {l : SlopePair}
    (ha : Tendsto (fun n => (u n).a) atTop (𝓝 l.a))
    (hb : Tendsto (fun n => (u n).b) atTop (𝓝 l.b))
    (hm : l.b - 1 ≠ 0) (hp : l.b + 1 ≠ 0) :
    Tendsto (fun n => (u n).toOdd.a) atTop (𝓝 l.toOdd.a) ∧
    Tendsto (fun n => (u n).toOdd.b) atTop (𝓝 l.toOdd.b) := by
  exact ⟨(hb.mul (ha.sub tendsto_const_nhds)).div (hb.sub tendsto_const_nhds) hm,
    (hb.mul (ha.add tendsto_const_nhds)).div (hb.add tendsto_const_nhds) hp⟩

theorem tendsto_toEven {u : ℕ → SlopePair} {l : SlopePair}
    (ha : Tendsto (fun n => (u n).a) atTop (𝓝 l.a))
    (hb : Tendsto (fun n => (u n).b) atTop (𝓝 l.b))
    (hm : l.b - 1 ≠ 0) (hp : l.b + 1 ≠ 0) :
    Tendsto (fun n => (u n).toEven.a) atTop (𝓝 l.toEven.a) ∧
    Tendsto (fun n => (u n).toEven.b) atTop (𝓝 l.toEven.b) := by
  exact ⟨(hb.mul (ha.add tendsto_const_nhds)).div (hb.add tendsto_const_nhds) hp,
    (hb.mul (ha.sub tendsto_const_nhds)).div (hb.sub tendsto_const_nhds) hm⟩

/-- Passing the actual recurrence to an interior even-subsequence limit. -/
theorem twoStep_eq_of_tendsto {s l : SlopePair} (hl : l.EvenConfig)
    (ha : Tendsto (fun n => (s.evenIterate n).a) atTop (𝓝 l.a))
    (hb : Tendsto (fun n => (s.evenIterate n).b) atTop (𝓝 l.b)) : l.twoStep = l := by
  obtain ⟨hoa, hob⟩ := tendsto_toOdd ha hb hl.b_sub_one_ne_zero hl.b_add_one_ne_zero
  have ho := toOdd_config hl
  obtain ⟨hea, heb⟩ := tendsto_toEven hoa hob ho.b_sub_one_ne_zero ho.b_add_one_ne_zero
  ext
  · exact tendsto_nhds_unique hea (ha.comp (tendsto_add_atTop_nat 1))
  · exact tendsto_nhds_unique heb (hb.comp (tendsto_add_atTop_nat 1))

theorem convergesToCycle_of_even_tendsto {s l : SlopePair} (hl : l.EvenConfig)
    (ha : Tendsto (fun n => (s.evenIterate n).a) atTop (𝓝 l.a))
    (hb : Tendsto (fun n => (s.evenIterate n).b) atTop (𝓝 l.b)) :
    s.ConvergesToCycle l l.toOdd := by
  obtain ⟨hoa, hob⟩ := tendsto_toOdd ha hb hl.b_sub_one_ne_zero hl.b_add_one_ne_zero
  exact ⟨ha, hb, hoa, hob⟩

/-- Both even slope sequences converge above the orthogonality locus. -/
theorem exists_even_limit_of_product_ge {s : SlopePair} (h : s.EvenConfig)
    (hp : -1 ≤ s.a * s.b) :
    ∃ l : SlopePair, l.EvenConfig ∧
      Tendsto (fun n => (s.evenIterate n).a) atTop (𝓝 l.a) ∧
      Tendsto (fun n => (s.evenIterate n).b) atTop (𝓝 l.b) := by
  have haBound : BddAbove (Set.range (fun n => (s.evenIterate n).a)) := by
    refine ⟨-1 / s.b, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (evenIterate_bounds_of_product_ge h hp n).2.1
  have hbBound : BddBelow (Set.range (fun n => (s.evenIterate n).b)) := by
    refine ⟨-1 / s.a, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (evenIterate_bounds_of_product_ge h hp n).2.2.1
  let a := ⨆ n, (s.evenIterate n).a
  let b := ⨅ n, (s.evenIterate n).b
  have ha : Tendsto (fun n => (s.evenIterate n).a) atTop (𝓝 a) :=
    tendsto_atTop_ciSup (evenIterate_a_monotone_of_product_ge h hp) haBound
  have hb : Tendsto (fun n => (s.evenIterate n).b) atTop (𝓝 b) :=
    tendsto_atTop_ciInf (evenIterate_b_antitone_of_product_ge h hp) hbBound
  have ha0 : s.a ≤ a := ge_of_tendsto' ha fun n => (evenIterate_bounds_of_product_ge h hp n).1
  have ha1 : a ≤ -1 / s.b := le_of_tendsto' ha fun n =>
    (evenIterate_bounds_of_product_ge h hp n).2.1
  have hb1 : b ≤ s.b := le_of_tendsto' hb fun n =>
    (evenIterate_bounds_of_product_ge h hp n).2.2.2
  have hu : -1 / s.b < 1 :=
    (div_lt_iff_of_neg h.b_neg).mpr (by linarith [h.2.2])
  exact ⟨⟨a, b⟩, ⟨by dsimp; linarith [h.1], by dsimp; linarith, by dsimp; linarith [h.2.2]⟩, ha, hb⟩

/-- Both even slope sequences converge below the orthogonality locus. -/
theorem exists_even_limit_of_product_le {s : SlopePair} (h : s.EvenConfig)
    (hp : s.a * s.b ≤ -1) :
    ∃ l : SlopePair, l.EvenConfig ∧
      Tendsto (fun n => (s.evenIterate n).a) atTop (𝓝 l.a) ∧
      Tendsto (fun n => (s.evenIterate n).b) atTop (𝓝 l.b) := by
  have haBound : BddBelow (Set.range (fun n => (s.evenIterate n).a)) := by
    refine ⟨-1 / s.b, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (evenIterate_bounds_of_product_le h hp n).1
  have hbBound : BddAbove (Set.range (fun n => (s.evenIterate n).b)) := by
    refine ⟨-1 / s.a, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (evenIterate_bounds_of_product_le h hp n).2.2.2
  let a := ⨅ n, (s.evenIterate n).a
  let b := ⨆ n, (s.evenIterate n).b
  have ha : Tendsto (fun n => (s.evenIterate n).a) atTop (𝓝 a) :=
    tendsto_atTop_ciInf (evenIterate_a_antitone_of_product_le h hp) haBound
  have hb : Tendsto (fun n => (s.evenIterate n).b) atTop (𝓝 b) :=
    tendsto_atTop_ciSup (evenIterate_b_monotone_of_product_le h hp) hbBound
  have ha0 : -1 / s.b ≤ a := ge_of_tendsto' ha fun n =>
    (evenIterate_bounds_of_product_le h hp n).1
  have ha1 : a ≤ s.a := le_of_tendsto' ha fun n =>
    (evenIterate_bounds_of_product_le h hp n).2.1
  have hb1 : b ≤ -1 / s.a := le_of_tendsto' hb fun n =>
    (evenIterate_bounds_of_product_le h hp n).2.2.2
  have hl : 0 < -1 / s.b := div_pos_of_neg_of_neg (by norm_num) h.b_neg
  have hu : -1 / s.a < -1 := (div_lt_iff₀ h.1).mpr (by linarith [h.2.1])
  exact ⟨⟨a, b⟩, ⟨by dsimp; linarith, by dsimp; linarith [h.2.1], by dsimp; linarith⟩, ha, hb⟩

/-- Theorem 9: existence of the orthogonal limiting cycle for every canonical
Configuration 1 input. Both finite slope limits and their interior bounds are proved. -/
theorem exists_orthogonal_limit_cycle {s : SlopePair} (h : s.EvenConfig) :
    ∃ l : SlopePair, l.EvenConfig ∧ l.Orthogonal ∧ s.ConvergesToCycle l l.toOdd := by
  have hex : ∃ l : SlopePair, l.EvenConfig ∧
      Tendsto (fun n => (s.evenIterate n).a) atTop (𝓝 l.a) ∧
      Tendsto (fun n => (s.evenIterate n).b) atTop (𝓝 l.b) := by
    rcases le_total (-1) (s.a * s.b) with hp | hp
    · exact exists_even_limit_of_product_ge h hp
    · exact exists_even_limit_of_product_le h hp
  obtain ⟨l, hl, ha, hb⟩ := hex
  exact ⟨l, hl, (twoStep_eq_self_iff hl).mp (twoStep_eq_of_tendsto hl ha hb),
    convergesToCycle_of_even_tendsto hl ha hb⟩

theorem convergesToCycle_unique {s l m l' m' : SlopePair}
    (h : s.ConvergesToCycle l m) (h' : s.ConvergesToCycle l' m') :
    l = l' ∧ m = m' := by
  constructor
  · exact SlopePair.ext (tendsto_nhds_unique h.1 h'.1)
      (tendsto_nhds_unique h.2.1 h'.2.1)
  · exact SlopePair.ext (tendsto_nhds_unique h.2.2.1 h'.2.2.1)
      (tendsto_nhds_unique h.2.2.2 h'.2.2.2)

/-- Theorem 7: every limiting cycle is genuinely of period two, with both
pairs orthogonal. Existence supplies the interior bounds needed at the limit. -/
theorem convergesToCycle_characterization {s l m : SlopePair} (h : s.EvenConfig)
    (hc : s.ConvergesToCycle l m) :
    l.EvenConfig ∧ m.OddConfig ∧ l.Orthogonal ∧ m.Orthogonal ∧
      m = l.toOdd ∧ m.toEven = l ∧ l ≠ m := by
  obtain ⟨l', hl, ho, hc'⟩ := exists_orthogonal_limit_cycle h
  obtain ⟨rfl, rfl⟩ := convergesToCycle_unique hc hc'
  refine ⟨hl, toOdd_config hl, ho, toOdd_orthogonal hl ho, rfl,
    (twoStep_eq_self_iff hl).mpr ho, ?_⟩
  intro he
  have hea := congrArg SlopePair.a he
  linarith [hl.1, (toOdd_config hl).2.1]

theorem tendsto_even_product_neg_one {s : SlopePair} (h : s.EvenConfig) :
    Tendsto (fun n => (s.evenIterate n).a * (s.evenIterate n).b) atTop (𝓝 (-1)) := by
  obtain ⟨l, _, ho, hc⟩ := exists_orthogonal_limit_cycle h
  simpa only [(orthogonal_iff l).mp ho] using hc.1.mul hc.2.1

/-- Reciprocal initial data have exactly the same limiting cycle. -/
theorem convergesToCycle_reciprocal {s l : SlopePair} (h : s.EvenConfig)
    (hl : l.EvenConfig) (ho : l.Orthogonal) (hc : s.ConvergesToCycle l l.toOdd) :
    s.reciprocal.ConvergesToCycle l l.toOdd := by
  have ha0 : l.a ≠ 0 := ne_of_gt hl.1
  have hb0 := hl.b_ne_zero
  have hr := ho.reciprocal_eq
  have ha : Tendsto (fun n => (s.reciprocal.evenIterate n).a) atTop (𝓝 l.a) := by
    have he := congrArg SlopePair.a hr
    change -1 / l.b = l.a at he
    simp_rw [evenIterate_reciprocal h]
    change Tendsto (fun n => (-1 : ℝ) / (s.evenIterate n).b) atTop (𝓝 l.a)
    rw [← he]
    exact tendsto_const_nhds.div hc.2.1 hb0
  have hb : Tendsto (fun n => (s.reciprocal.evenIterate n).b) atTop (𝓝 l.b) := by
    have he := congrArg SlopePair.b hr
    change -1 / l.a = l.b at he
    simp_rw [evenIterate_reciprocal h]
    change Tendsto (fun n => (-1 : ℝ) / (s.evenIterate n).a) atTop (𝓝 l.b)
    rw [← he]
    exact tendsto_const_nhds.div hc.1 ha0
  exact convergesToCycle_of_even_tendsto hl ha hb

theorem exists_shared_orthogonal_limit_cycle {s : SlopePair} (h : s.EvenConfig) :
    ∃ l : SlopePair, l.EvenConfig ∧ l.Orthogonal ∧
      s.ConvergesToCycle l l.toOdd ∧ s.reciprocal.ConvergesToCycle l l.toOdd := by
  obtain ⟨l, hl, ho, hc⟩ := exists_orthogonal_limit_cycle h
  exact ⟨l, hl, ho, hc, convergesToCycle_reciprocal h hl ho hc⟩

end SlopePair
end FitzhughFarnsworth
