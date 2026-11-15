/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import FitzhughFarnsworth.Convergence

/-!
# Rigorous enclosures for the limiting slope

Every even iterate supplies an interval with endpoints `a_n` and `-1 / b_n`
containing the limiting shallow slope. Its width tends to zero. These are exact
real statements; certifying numerical output additionally requires certified
initial slopes and arithmetic bounds.
-/

@[expose] public section

namespace FitzhughFarnsworth
namespace SlopePair

open Filter Topology

theorem neg_one_div_le_neg_one_div {x y : ℝ} (hy : y < 0) (hxy : x ≤ y) :
    -1 / x ≤ -1 / y := by
  simpa only [neg_div] using neg_le_neg (one_div_le_one_div_of_neg_of_le hy hxy)

theorem limit_enclosure_of_product_ge {s l o : SlopePair} (hs : s.EvenConfig)
    (hp : -1 ≤ s.a * s.b) (hc : s.ConvergesToCycle l o) (n : ℕ) :
    (s.evenIterate n).a ≤ l.a ∧ l.a ≤ -1 / (s.evenIterate n).b := by
  have hchar := convergesToCycle_characterization hs hc
  have he := congrArg SlopePair.a hchar.2.2.1.reciprocal_eq
  change -1 / l.b = l.a at he
  have ha := (evenIterate_a_monotone_of_product_ge hs hp).ge_of_tendsto hc.1 n
  have hb := (evenIterate_b_antitone_of_product_ge hs hp).le_of_tendsto hc.2.1 n
  have hr := neg_one_div_le_neg_one_div
    (by linarith [(evenIterate_config hs n).2.2] : (s.evenIterate n).b < 0) hb
  rw [he] at hr
  exact ⟨ha, hr⟩

theorem limit_enclosure_of_product_le {s l o : SlopePair} (hs : s.EvenConfig)
    (hp : s.a * s.b ≤ -1) (hc : s.ConvergesToCycle l o) (n : ℕ) :
    -1 / (s.evenIterate n).b ≤ l.a ∧ l.a ≤ (s.evenIterate n).a := by
  have hchar := convergesToCycle_characterization hs hc
  have he := congrArg SlopePair.a hchar.2.2.1.reciprocal_eq
  change -1 / l.b = l.a at he
  have ha := (evenIterate_a_antitone_of_product_le hs hp).le_of_tendsto hc.1 n
  have hb := (evenIterate_b_monotone_of_product_le hs hp).ge_of_tendsto hc.2.1 n
  have hr := neg_one_div_le_neg_one_div (by linarith [hchar.1.2.2] : l.b < 0) hb
  rw [he] at hr
  exact ⟨hr, ha⟩

/-- Both endpoints are determined by a finite iterate; no unknown limit
appears in the interval itself. -/
theorem limit_enclosure {s l o : SlopePair} (hs : s.EvenConfig)
    (hc : s.ConvergesToCycle l o) (n : ℕ) :
    min (s.evenIterate n).a (-1 / (s.evenIterate n).b) ≤ l.a ∧
      l.a ≤ max (s.evenIterate n).a (-1 / (s.evenIterate n).b) := by
  rcases le_total (-1) (s.a * s.b) with hp | hp
  · obtain ⟨ha, hb⟩ := limit_enclosure_of_product_ge hs hp hc n
    exact ⟨(min_le_left _ _).trans ha, hb.trans (le_max_right _ _)⟩
  · obtain ⟨ha, hb⟩ := limit_enclosure_of_product_le hs hp hc n
    exact ⟨(min_le_right _ _).trans ha, hb.trans (le_max_left _ _)⟩

/-- A rigorous absolute error bound for the shallow slope at any even iterate. -/
theorem limit_error_le_enclosure_width {s l o : SlopePair} (hs : s.EvenConfig)
    (hc : s.ConvergesToCycle l o) (n : ℕ) :
    |l.a - (s.evenIterate n).a| ≤
      |(s.evenIterate n).a - (-1 / (s.evenIterate n).b)| := by
  obtain ⟨hlo, hhi⟩ := limit_enclosure hs hc n
  rcases le_total (s.evenIterate n).a (-1 / (s.evenIterate n).b) with he | he
  · rw [min_eq_left he] at hlo
    rw [max_eq_right he] at hhi
    rw [abs_of_nonneg (sub_nonneg.mpr hlo), abs_of_nonpos (sub_nonpos.mpr he)]
    linarith
  · rw [min_eq_right he] at hlo
    rw [max_eq_left he] at hhi
    rw [abs_of_nonpos (sub_nonpos.mpr hhi), abs_of_nonneg (sub_nonneg.mpr he)]
    linarith

theorem tendsto_enclosure_width_zero {s l o : SlopePair} (hs : s.EvenConfig)
    (hc : s.ConvergesToCycle l o) :
    Tendsto (fun n => |(s.evenIterate n).a - (-1 / (s.evenIterate n).b)|)
      atTop (𝓝 0) := by
  have hchar := convergesToCycle_characterization hs hc
  have he := congrArg SlopePair.a hchar.2.2.1.reciprocal_eq
  change -1 / l.b = l.a at he
  have hb0 : l.b ≠ 0 := by linarith [hchar.1.2.2]
  have hr : Tendsto (fun n => -1 / (s.evenIterate n).b) atTop (𝓝 l.a) := by
    rw [← he]
    exact tendsto_const_nhds.div hc.2.1 hb0
  simpa only [sub_self, abs_zero] using (hc.1.sub hr).abs

end SlopePair
end FitzhughFarnsworth
