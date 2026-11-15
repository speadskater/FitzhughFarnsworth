module

public import FitzhughFarnsworth.Dynamics.Sequence

/-!
# Genuine geometric evolutions in the attracting configurations

Canonical slope sequences are interleaved into sequences of actual line pairs.
Every transition is a geometric midset equality, and slope limits imply
pointwise convergence of the distance profiles of the corresponding pairs.
-/

@[expose] public section

namespace FitzhughFarnsworth
namespace Dynamics

open Filter Topology

noncomputable def interleave (f g : ℕ → LinePair) (n : ℕ) : LinePair :=
  if n % 2 = 0 then f (n / 2) else g (n / 2)

@[simp] theorem interleave_even (f g : ℕ → LinePair) (n : ℕ) :
    interleave f g (2 * n) = f n := by simp [interleave]

@[simp] theorem interleave_odd (f g : ℕ → LinePair) (n : ℕ) :
    interleave f g (2 * n + 1) = g n := by
  have hd : (2 * n + 1) / 2 = n := by omega
  simp [interleave, hd]

theorem interleave_isEvolution {v : Point} {f g : ℕ → LinePair}
    (hf : ∀ n, (f n).ValidAt v) (hg : ∀ n, (g n).ValidAt v)
    (hfg : ∀ n, (f n).Step (g n)) (hgf : ∀ n, (g n).Step (f (n + 1))) :
    IsEvolution v (interleave f g) := by
  constructor
  · intro n
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hn : n = 2 * k := by omega
      rw [hn, interleave_even]
      exact hf k
    · have hn : n = 2 * k + 1 := by omega
      rw [hn, interleave_odd]
      exact hg k
  · intro n
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hn : n = 2 * k := by omega
      rw [hn, interleave_even, interleave_odd]
      exact hfg k
    · have hn : n = 2 * k + 1 := by omega
      rw [hn, show 2 * k + 1 + 1 = 2 * (k + 1) by omega,
        interleave_odd, interleave_even]
      exact hgf k

theorem continuous_infDist_slopeLine (p : Point) :
    Continuous (fun m : ℝ => Metric.infDist p (slopeLine m)) := by
  have hd : ∀ m : ℝ, max 1 |m| ≠ 0 := fun m =>
    ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left 1 |m|))
  have hc : Continuous (fun m : ℝ => |p.y - m * p.x| / max 1 |m|) :=
    ((continuous_const.sub (continuous_id.mul continuous_const)).abs).div
      (continuous_const.max continuous_abs) hd
  simpa only [infDist_slopeLine] using hc

theorem profile_ofSlopes_tendsto {s : ℕ → SlopePair} {l : SlopePair}
    (ha : Tendsto (fun n => (s n).a) atTop (𝓝 l.a))
    (hb : Tendsto (fun n => (s n).b) atTop (𝓝 l.b)) (p : Point) :
    Tendsto (fun n => (LinePair.ofSlopes (s n)).profile p) atTop
      (𝓝 ((LinePair.ofSlopes l).profile p)) := by
  exact ((continuous_infDist_slopeLine p).tendsto l.a |>.comp ha).min
    ((continuous_infDist_slopeLine p).tendsto l.b |>.comp hb)

theorem valid_ofSlopes_even {s : SlopePair} (h : s.EvenConfig) :
    (LinePair.ofSlopes s).ValidAt origin := by
  apply LinePair.ValidOrigin.validAt_origin
  exact ⟨isOriginLine_slope _, isOriginLine_slope _, slopeLine_ne_of_ne h.distinct⟩

theorem valid_ofSlopes_odd {s : SlopePair} (h : s.OddConfig) :
    (LinePair.ofSlopes s).ValidAt origin := by
  apply LinePair.ValidOrigin.validAt_origin
  exact ⟨isOriginLine_slope _, isOriginLine_slope _, slopeLine_ne_of_ne h.distinct⟩

noncomputable def canonicalEvolution (s : SlopePair) : ℕ → LinePair :=
  interleave (fun n => LinePair.ofSlopes (s.evenIterate n))
    (fun n => LinePair.ofSlopes (s.oddIterate n))

@[simp] theorem canonicalEvolution_even (s : SlopePair) (n : ℕ) :
    canonicalEvolution s (2 * n) = LinePair.ofSlopes (s.evenIterate n) :=
  interleave_even _ _ n

@[simp] theorem canonicalEvolution_odd (s : SlopePair) (n : ℕ) :
    canonicalEvolution s (2 * n + 1) = LinePair.ofSlopes (s.oddIterate n) :=
  interleave_odd _ _ n

@[simp] theorem canonicalEvolution_zero (s : SlopePair) :
    canonicalEvolution s 0 = LinePair.ofSlopes s := by
  simpa only [mul_zero, SlopePair.evenIterate] using canonicalEvolution_even s 0

theorem canonicalEvolution_isEvolution {s : SlopePair} (h : s.EvenConfig) :
    IsEvolution origin (canonicalEvolution s) := by
  apply interleave_isEvolution
  · intro n
    exact valid_ofSlopes_even (SlopePair.evenIterate_config h n)
  · intro n
    exact valid_ofSlopes_odd (SlopePair.oddIterate_config h n)
  · intro n
    exact SlopePair.evenIterate_midset h n
  · intro n
    exact SlopePair.oddIterate_midset h n

theorem canonicalEvolution_converges {s l o : SlopePair}
    (h : s.ConvergesToCycle l o) :
    ConvergesToCycle (canonicalEvolution s) (LinePair.ofSlopes l) (LinePair.ofSlopes o) := by
  constructor
  · intro p
    simpa only [canonicalEvolution_even] using profile_ofSlopes_tendsto h.1 h.2.1 p
  · intro p
    simpa only [canonicalEvolution_odd] using profile_ofSlopes_tendsto h.2.2.1 h.2.2.2 p

theorem canonical_twoCycle {l : SlopePair} (hl : l.EvenConfig) (ho : l.Orthogonal) :
    TwoCycleAt origin (LinePair.ofSlopes l) (LinePair.ofSlopes l.toOdd) where
  valid_left := valid_ofSlopes_even hl
  valid_right := valid_ofSlopes_odd (SlopePair.toOdd_config hl)
  step_left := SlopePair.midset_eq_toOdd hl
  step_right := (SlopePair.midset_midset_eq_self_iff_even hl).mpr ho
  distinct := SlopePair.even_odd_carriers_ne hl (SlopePair.toOdd_config hl)
  orthogonal_left := (LinePair.OrthogonalOrigin.slopes l ho).orthogonalAt_origin
  orthogonal_right := (LinePair.OrthogonalOrigin.slopes l.toOdd
    (SlopePair.toOdd_orthogonal hl ho)).orthogonalAt_origin

theorem canonicalEvolution_hasLimitCycle {s : SlopePair} (h : s.EvenConfig) :
    HasLimitCycle origin (canonicalEvolution s) := by
  obtain ⟨l, hl, ho, hc⟩ := SlopePair.exists_orthogonal_limit_cycle h
  exact ⟨LinePair.ofSlopes l, LinePair.ofSlopes l.toOdd, canonical_twoCycle hl ho,
    canonicalEvolution_converges hc⟩

def axesPair : LinePair := (horizontalAxis, verticalAxis)

def diagonalsPair : LinePair := (slopeLine 1, slopeLine (-1))

theorem valid_axesPair : axesPair.ValidAt origin := by
  apply LinePair.ValidOrigin.validAt_origin
  exact ⟨isOriginLine_slope 0, isOriginLine_vertical, slopeLine_ne_vertical 0⟩

theorem valid_diagonalsPair : diagonalsPair.ValidAt origin := by
  apply LinePair.ValidOrigin.validAt_origin
  exact ⟨isOriginLine_slope 1, isOriginLine_slope (-1), slopeLine_ne_of_ne (by norm_num)⟩

theorem axes_diagonals_twoCycle : TwoCycleAt origin axesPair diagonalsPair where
  valid_left := valid_axesPair
  valid_right := valid_diagonalsPair
  step_left := midset_axes
  step_right := midset_diagonals
  distinct := by
    intro he
    have hp : (⟨1, 0⟩ : Point) ∈ axesPair.carrier := by
      simp [axesPair, LinePair.carrier, horizontalAxis, slopeLine]
    rw [he] at hp
    norm_num [diagonalsPair, LinePair.carrier, slopeLine] at hp
  orthogonal_left := LinePair.OrthogonalOrigin.axes.orthogonalAt_origin
  orthogonal_right := (LinePair.OrthogonalOrigin.slopes (⟨1, -1⟩ : SlopePair)
    (by norm_num [SlopePair.Orthogonal])).orthogonalAt_origin

noncomputable def axesEvolution : ℕ → LinePair :=
  interleave (fun _ => axesPair) (fun _ => diagonalsPair)

theorem axesEvolution_isEvolution : IsEvolution origin axesEvolution :=
  interleave_isEvolution (fun _ => valid_axesPair) (fun _ => valid_diagonalsPair)
    (fun _ => midset_axes) (fun _ => midset_diagonals)

theorem axesEvolution_hasLimitCycle : HasLimitCycle origin axesEvolution := by
  refine ⟨axesPair, diagonalsPair, axes_diagonals_twoCycle, ?_⟩
  constructor <;> intro p
  · simpa only [axesEvolution, interleave_even] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => axesPair.profile p) atTop (𝓝 (axesPair.profile p)))
  · simpa only [axesEvolution, interleave_odd] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => diagonalsPair.profile p) atTop (𝓝 (diagonalsPair.profile p)))

theorem isEvolution_swap {v : Point} {u : ℕ → LinePair} (h : IsEvolution v u) :
    IsEvolution v (fun n => (u n).swap) := by
  constructor
  · intro n
    exact ⟨(h.1 n).2.1, (h.1 n).1, (h.1 n).2.2.symm⟩
  · intro n
    exact (h.2 n).swap_left.swap_right

theorem HasLimitCycle.swap_inputs {v : Point} {u : ℕ → LinePair} (h : HasLimitCycle v u) :
    HasLimitCycle v (fun n => (u n).swap) := by
  obtain ⟨P, Q, hc, hl⟩ := h
  refine ⟨P, Q, hc, ?_⟩
  simpa only [ConvergesToCycle, LinePair.profile_swap] using hl

/-- Every attracting pair starts an actual infinite geometric midset evolution
that converges to a genuine orthogonal two-cycle. -/
theorem attractorPair_exists_evolution {A B : Set Point} (h : AttractorPair A B) :
    ∃ u : ℕ → LinePair, u 0 = (A, B) ∧ IsEvolution origin u ∧ HasLimitCycle origin u := by
  induction h with
  | even s hs =>
    exact ⟨canonicalEvolution s, canonicalEvolution_zero s,
      canonicalEvolution_isEvolution hs, canonicalEvolution_hasLimitCycle hs⟩
  | odd s hs =>
    let u := canonicalEvolution s.toEven
    have hu : u 0 = LinePair.ofSlopes s.toEven := canonicalEvolution_zero _
    have he := canonicalEvolution_isEvolution (SlopePair.toEven_config hs)
    have hc := canonicalEvolution_hasLimitCycle (SlopePair.toEven_config hs)
    refine ⟨prepend (LinePair.ofSlopes s) u, rfl,
      isEvolution_prepend he (valid_ofSlopes_odd hs) ?_, hc.prepend _⟩
    rw [hu]
    exact SlopePair.midset_eq_toEven hs
  | axes =>
    exact ⟨axesEvolution, by simp [axesEvolution, interleave, axesPair],
      axesEvolution_isEvolution, axesEvolution_hasLimitCycle⟩
  | diagonals =>
    refine ⟨prepend diagonalsPair axesEvolution, rfl,
      isEvolution_prepend axesEvolution_isEvolution valid_diagonalsPair ?_,
      axesEvolution_hasLimitCycle.prepend _⟩
    change midset (slopeLine 1) (slopeLine (-1)) = (axesEvolution 0).carrier
    simpa [axesEvolution, interleave, axesPair, LinePair.carrier] using midset_diagonals
  | comm _ ih =>
    obtain ⟨u, hu, he, hc⟩ := ih
    refine ⟨fun n => (u n).swap, ?_, isEvolution_swap he, hc.swap_inputs⟩
    change (u 0).swap = _
    rw [hu]
    rfl

end Dynamics
end FitzhughFarnsworth
