module

public import FitzhughFarnsworth.IteratedMidsets.Algebra

/-! # Monotonicity and invariant regions for the two-step map -/

@[expose] public section

namespace FitzhughFarnsworth
namespace SlopePair

theorem EvenConfig.product_factor_neg {s : SlopePair} (h : s.EvenConfig) :
    (s.a * s.b) ^ 2 + 1 - 2 * s.b ^ 2 < 0 := by
  have ha : s.a ^ 2 < 1 := by nlinarith [h.1, h.2.1]
  have hb : 1 < s.b ^ 2 := by nlinarith [h.2.2]
  have hab := mul_lt_mul_of_pos_right ha (show 0 < s.b ^ 2 by linarith)
  nlinarith

theorem EvenConfig.product_denominator_neg {s : SlopePair} (h : s.EvenConfig) :
    (s.b - 1) ^ 2 * (s.a * s.b + 1 + 2 * s.b) < 0 := by
  exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (by linarith [h.2.2]))
    (by linarith [h.product_neg, h.2.2])

theorem twoStep_of_product_ge {s : SlopePair} (h : s.EvenConfig)
    (hp : -1 ≤ s.a * s.b) :
    s.a ≤ s.twoStep.a ∧ s.twoStep.b ≤ s.b ∧ -1 ≤ s.twoStep.a * s.twoStep.b := by
  have hab : 0 < s.a - s.b := by linarith [h.1, h.2.2]
  have hp' : 0 ≤ s.a * s.b + 1 := by linarith
  have ha : 0 ≤ s.twoStep.a - s.a := by
    rw [twoStep_a_sub_a h]
    exact div_nonneg (mul_nonneg hab.le hp') h.denominator_a_pos.le
  have hb : s.twoStep.b - s.b ≤ 0 := by
    rw [twoStep_b_sub_b h]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith [h.2.2]) hab.le) hp')
      h.denominator_b_pos.le
  have hpnext : 0 ≤ s.twoStep.a * s.twoStep.b + 1 := by
    rw [twoStep_product_add_one h]
    exact div_nonneg_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos hp' h.product_factor_neg.le)
      h.product_denominator_neg.le
  exact ⟨by linarith, by linarith, by linarith⟩

theorem twoStep_of_product_le {s : SlopePair} (h : s.EvenConfig)
    (hp : s.a * s.b ≤ -1) :
    s.twoStep.a ≤ s.a ∧ s.b ≤ s.twoStep.b ∧ s.twoStep.a * s.twoStep.b ≤ -1 := by
  have hab : 0 < s.a - s.b := by linarith [h.1, h.2.2]
  have hp' : s.a * s.b + 1 ≤ 0 := by linarith
  have ha : s.twoStep.a - s.a ≤ 0 := by
    rw [twoStep_a_sub_a h]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hab.le hp') h.denominator_a_pos.le
  have hb : 0 ≤ s.twoStep.b - s.b := by
    rw [twoStep_b_sub_b h]
    exact div_nonneg
      (mul_nonneg_of_nonpos_of_nonpos
        (mul_nonpos_of_nonpos_of_nonneg (by linarith [h.2.2]) hab.le) hp')
      h.denominator_b_pos.le
  have hpnext : s.twoStep.a * s.twoStep.b + 1 ≤ 0 := by
    rw [twoStep_product_add_one h]
    exact div_nonpos_of_nonneg_of_nonpos
      (mul_nonneg_of_nonpos_of_nonpos hp' h.product_factor_neg.le)
      h.product_denominator_neg.le
  exact ⟨by linarith, by linarith, by linarith⟩

theorem evenIterate_product_ge {s : SlopePair} (h : s.EvenConfig)
    (hp : -1 ≤ s.a * s.b) (n : ℕ) :
    -1 ≤ (s.evenIterate n).a * (s.evenIterate n).b := by
  induction n with
  | zero => exact hp
  | succ n ih => exact (twoStep_of_product_ge (evenIterate_config h n) ih).2.2

theorem evenIterate_product_le {s : SlopePair} (h : s.EvenConfig)
    (hp : s.a * s.b ≤ -1) (n : ℕ) :
    (s.evenIterate n).a * (s.evenIterate n).b ≤ -1 := by
  induction n with
  | zero => exact hp
  | succ n ih => exact (twoStep_of_product_le (evenIterate_config h n) ih).2.2

theorem evenIterate_a_monotone_of_product_ge {s : SlopePair} (h : s.EvenConfig)
    (hp : -1 ≤ s.a * s.b) : Monotone (fun n => (s.evenIterate n).a) := by
  apply monotone_nat_of_le_succ
  intro n
  exact (twoStep_of_product_ge (evenIterate_config h n) (evenIterate_product_ge h hp n)).1

theorem evenIterate_b_antitone_of_product_ge {s : SlopePair} (h : s.EvenConfig)
    (hp : -1 ≤ s.a * s.b) : Antitone (fun n => (s.evenIterate n).b) := by
  apply antitone_nat_of_succ_le
  intro n
  exact (twoStep_of_product_ge (evenIterate_config h n) (evenIterate_product_ge h hp n)).2.1

theorem evenIterate_a_antitone_of_product_le {s : SlopePair} (h : s.EvenConfig)
    (hp : s.a * s.b ≤ -1) : Antitone (fun n => (s.evenIterate n).a) := by
  apply antitone_nat_of_succ_le
  intro n
  exact (twoStep_of_product_le (evenIterate_config h n) (evenIterate_product_le h hp n)).1

theorem evenIterate_b_monotone_of_product_le {s : SlopePair} (h : s.EvenConfig)
    (hp : s.a * s.b ≤ -1) : Monotone (fun n => (s.evenIterate n).b) := by
  apply monotone_nat_of_le_succ
  intro n
  exact (twoStep_of_product_le (evenIterate_config h n) (evenIterate_product_le h hp n)).2.1

/-- Uniform bounds that keep both limits in the open canonical region. -/
theorem evenIterate_bounds_of_product_ge {s : SlopePair} (h : s.EvenConfig)
    (hp : -1 ≤ s.a * s.b) (n : ℕ) :
    s.a ≤ (s.evenIterate n).a ∧ (s.evenIterate n).a ≤ -1 / s.b ∧
      -1 / s.a ≤ (s.evenIterate n).b ∧ (s.evenIterate n).b ≤ s.b := by
  have hn := evenIterate_config h n
  have hpn := evenIterate_product_ge h hp n
  have ha : s.a ≤ (s.evenIterate n).a :=
    evenIterate_a_monotone_of_product_ge h hp (Nat.zero_le n)
  have hb : (s.evenIterate n).b ≤ s.b :=
    evenIterate_b_antitone_of_product_ge h hp (Nat.zero_le n)
  refine ⟨ha, ?_, ?_, hb⟩
  · apply (le_div_iff_of_neg (by linarith [h.2.2] : s.b < 0)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hb hn.1.le]
  · apply (div_le_iff₀ h.1).mpr
    nlinarith [mul_le_mul_of_nonpos_right ha (by linarith [hn.2.2] : (s.evenIterate n).b ≤ 0)]

theorem evenIterate_bounds_of_product_le {s : SlopePair} (h : s.EvenConfig)
    (hp : s.a * s.b ≤ -1) (n : ℕ) :
    -1 / s.b ≤ (s.evenIterate n).a ∧ (s.evenIterate n).a ≤ s.a ∧
      s.b ≤ (s.evenIterate n).b ∧ (s.evenIterate n).b ≤ -1 / s.a := by
  have hn := evenIterate_config h n
  have hpn := evenIterate_product_le h hp n
  have ha : (s.evenIterate n).a ≤ s.a :=
    evenIterate_a_antitone_of_product_le h hp (Nat.zero_le n)
  have hb : s.b ≤ (s.evenIterate n).b :=
    evenIterate_b_monotone_of_product_le h hp (Nat.zero_le n)
  refine ⟨?_, ha, hb, ?_⟩
  · apply (div_le_iff_of_neg (by linarith [h.2.2] : s.b < 0)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hb hn.1.le]
  · apply (le_div_iff₀ h.1).mpr
    nlinarith [mul_le_mul_of_nonpos_right ha (by linarith [hn.2.2] : (s.evenIterate n).b ≤ 0)]

/-- The strict inequalities in Theorem 9 above the orthogonality locus. -/
theorem twoStep_of_product_gt {s : SlopePair} (h : s.EvenConfig)
    (hp : -1 < s.a * s.b) :
    s.a < s.twoStep.a ∧ s.twoStep.b < s.b ∧
      -1 < s.twoStep.a * s.twoStep.b ∧ s.twoStep.a * s.twoStep.b < s.a * s.b := by
  have hab : 0 < s.a - s.b := by linarith [h.1, h.2.2]
  have hp' : 0 < s.a * s.b + 1 := by linarith
  have ha : s.a < s.twoStep.a := by
    apply sub_pos.mp
    rw [twoStep_a_sub_a h]
    exact div_pos (mul_pos hab hp') h.denominator_a_pos
  have hb : s.twoStep.b < s.b := by
    apply sub_neg.mp
    rw [twoStep_b_sub_b h]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith [h.2.2]) hab) hp')
      h.denominator_b_pos
  have hprod : -1 < s.twoStep.a * s.twoStep.b := by
    have : 0 < s.twoStep.a * s.twoStep.b + 1 := by
      rw [twoStep_product_add_one h]
      exact div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hp' h.product_factor_neg)
        h.product_denominator_neg
    linarith
  refine ⟨ha, hb, hprod, ?_⟩
  calc
    s.twoStep.a * s.twoStep.b < s.a * s.twoStep.b :=
      mul_lt_mul_of_neg_right ha (by linarith [hb, h.2.2])
    _ < s.a * s.b := mul_lt_mul_of_pos_left hb h.1

/-- The strict inequalities in Theorem 9 below the orthogonality locus. -/
theorem twoStep_of_product_lt {s : SlopePair} (h : s.EvenConfig)
    (hp : s.a * s.b < -1) :
    s.twoStep.a < s.a ∧ s.b < s.twoStep.b ∧
      s.twoStep.a * s.twoStep.b < -1 ∧ s.a * s.b < s.twoStep.a * s.twoStep.b := by
  have hab : 0 < s.a - s.b := by linarith [h.1, h.2.2]
  have hp' : s.a * s.b + 1 < 0 := by linarith
  have ha : s.twoStep.a < s.a := by
    apply sub_neg.mp
    rw [twoStep_a_sub_a h]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hab hp') h.denominator_a_pos
  have hb : s.b < s.twoStep.b := by
    apply sub_pos.mp
    rw [twoStep_b_sub_b h]
    exact div_pos
      (mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (by linarith [h.2.2]) hab) hp')
      h.denominator_b_pos
  have hprod : s.twoStep.a * s.twoStep.b < -1 := by
    have : s.twoStep.a * s.twoStep.b + 1 < 0 := by
      rw [twoStep_product_add_one h]
      exact div_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hp' h.product_factor_neg)
        h.product_denominator_neg
    linarith
  refine ⟨ha, hb, hprod, ?_⟩
  calc
    s.a * s.b < s.twoStep.a * s.b := mul_lt_mul_of_neg_right ha (by linarith [h.2.2])
    _ < s.twoStep.a * s.twoStep.b := mul_lt_mul_of_pos_left hb (twoStep_config h).1

theorem evenIterate_product_gt {s : SlopePair} (h : s.EvenConfig)
    (hp : -1 < s.a * s.b) (n : ℕ) :
    -1 < (s.evenIterate n).a * (s.evenIterate n).b := by
  induction n with
  | zero => exact hp
  | succ n ih => exact (twoStep_of_product_gt (evenIterate_config h n) ih).2.2.1

theorem evenIterate_product_lt {s : SlopePair} (h : s.EvenConfig)
    (hp : s.a * s.b < -1) (n : ℕ) :
    (s.evenIterate n).a * (s.evenIterate n).b < -1 := by
  induction n with
  | zero => exact hp
  | succ n ih => exact (twoStep_of_product_lt (evenIterate_config h n) ih).2.2.1

theorem evenIterate_a_strictMono_of_product_gt {s : SlopePair} (h : s.EvenConfig)
    (hp : -1 < s.a * s.b) : StrictMono (fun n => (s.evenIterate n).a) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (twoStep_of_product_gt (evenIterate_config h n) (evenIterate_product_gt h hp n)).1

theorem evenIterate_b_strictAnti_of_product_gt {s : SlopePair} (h : s.EvenConfig)
    (hp : -1 < s.a * s.b) : StrictAnti (fun n => (s.evenIterate n).b) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  exact (twoStep_of_product_gt (evenIterate_config h n) (evenIterate_product_gt h hp n)).2.1

theorem evenIterate_a_strictAnti_of_product_lt {s : SlopePair} (h : s.EvenConfig)
    (hp : s.a * s.b < -1) : StrictAnti (fun n => (s.evenIterate n).a) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  exact (twoStep_of_product_lt (evenIterate_config h n) (evenIterate_product_lt h hp n)).1

theorem evenIterate_b_strictMono_of_product_lt {s : SlopePair} (h : s.EvenConfig)
    (hp : s.a * s.b < -1) : StrictMono (fun n => (s.evenIterate n).b) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (twoStep_of_product_lt (evenIterate_config h n) (evenIterate_product_lt h hp n)).2.1

theorem evenIterate_product_strictAnti {s : SlopePair} (h : s.EvenConfig)
    (hp : -1 < s.a * s.b) :
    StrictAnti (fun n => (s.evenIterate n).a * (s.evenIterate n).b) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  exact (twoStep_of_product_gt (evenIterate_config h n) (evenIterate_product_gt h hp n)).2.2.2

theorem evenIterate_product_strictMono {s : SlopePair} (h : s.EvenConfig)
    (hp : s.a * s.b < -1) :
    StrictMono (fun n => (s.evenIterate n).a * (s.evenIterate n).b) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (twoStep_of_product_lt (evenIterate_config h n) (evenIterate_product_lt h hp n)).2.2.2

end SlopePair
end FitzhughFarnsworth
