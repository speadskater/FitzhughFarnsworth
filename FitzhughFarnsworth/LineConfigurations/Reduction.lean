module

public import FitzhughFarnsworth.IteratedMidsets

/-!
# Reduction to the attracting configurations

All geometric transitions below are equalities of midsets defined by metric
infimum distance. Coordinate exchange and reflection are taxicab isometries.
-/

@[expose] public section

namespace FitzhughFarnsworth

/-- Two distinct shallow lines have their average-slope line and the vertical
axis as their midset. This includes the diagonal boundary slopes. -/
theorem midset_two_shallow (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hab : a ≠ b) :
    midset (slopeLine a) (slopeLine b) = slopeLine ((a + b) / 2) ∪ verticalAxis := by
  ext p
  rw [mem_midset, infDist_slopeLine_of_abs_le_one p a ha,
    infDist_slopeLine_of_abs_le_one p b hb, abs_eq_abs]
  change (_ = _ ∨ _ = _) ↔ (p.y = (a + b) / 2 * p.x ∨ p.x = 0)
  constructor
  · rintro (h | h)
    · right
      have : (a - b) * p.x = 0 := by nlinarith
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hab)
    · left
      linarith
  · rintro (h | h)
    · right
      linarith
    · left
      simp [h]

theorem midset_shallow_vertical (a : ℝ) (ha : |a| ≤ 1) :
    midset (slopeLine a) verticalAxis = slopeLine (a - 1) ∪ slopeLine (a + 1) := by
  ext p
  rw [mem_midset, infDist_slopeLine_of_abs_le_one p a ha,
    infDist_verticalAxis, abs_eq_abs]
  change (_ = _ ∨ _ = _) ↔ (p.y = (a - 1) * p.x ∨ p.y = (a + 1) * p.x)
  constructor
  · rintro (h | h)
    · right; nlinarith
    · left; nlinarith
  · rintro (h | h)
    · right; nlinarith
    · left; nlinarith

theorem average_mem_open_unit {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hab : a ≠ b) : -1 < (a + b) / 2 ∧ (a + b) / 2 < 1 := by
  rcases abs_le.mp ha with ⟨hal, hau⟩
  rcases abs_le.mp hb with ⟨hbl, hbu⟩
  constructor <;> by_contra h
  · have : a = b := by push Not at h; linarith
    exact hab this
  · have : a = b := by push Not at h; linarith
    exact hab this

noncomputable def swapCoordinates : Point ≃ᵢ Point where
  toFun p := ⟨p.y, p.x⟩
  invFun p := ⟨p.y, p.x⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro p q
    simp [dist_eq, add_comm]

noncomputable def reflectY : Point ≃ᵢ Point where
  toFun p := ⟨p.x, -p.y⟩
  invFun p := ⟨p.x, -p.y⟩
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro p q
    change |p.x - q.x| + |-p.y - -q.y| = |p.x - q.x| + |p.y - q.y|
    rw [neg_sub_neg, abs_sub_comm q.y p.y]

theorem isometryEquiv_image_midset (e : Point ≃ᵢ Point) (s t : Set Point) :
    e '' midset s t = midset (e '' s) (e '' t) := by
  ext p
  obtain ⟨q, rfl⟩ := e.surjective p
  constructor
  · rintro ⟨r, hr, he⟩
    have : r = q := e.injective he
    subst r
    rwa [mem_midset, Metric.infDist_image e.isometry, Metric.infDist_image e.isometry]
  · intro hq
    refine ⟨q, ?_, rfl⟩
    rwa [mem_midset, Metric.infDist_image e.isometry, Metric.infDist_image e.isometry] at hq

theorem swapCoordinates_image_vertical :
    swapCoordinates '' verticalAxis = horizontalAxis := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [swapCoordinates, horizontalAxis, slopeLine, verticalAxis] using hq
  · intro hp
    refine ⟨⟨p.y, p.x⟩, ?_, rfl⟩
    simpa [horizontalAxis, slopeLine, verticalAxis] using hp

theorem swapCoordinates_image_slope (a : ℝ) (ha : a ≠ 0) :
    swapCoordinates '' slopeLine a = slopeLine (1 / a) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change q.x = 1 / a * q.y
    change q.y = a * q.x at hq
    rw [hq]
    field_simp
  · intro hp
    refine ⟨⟨p.y, p.x⟩, ?_, rfl⟩
    change p.x = a * p.y
    change p.y = 1 / a * p.x at hp
    field_simp at hp
    nlinarith

theorem reflectY_image_slope (a : ℝ) :
    reflectY '' slopeLine a = slopeLine (-a) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change -q.y = -a * q.x
    change q.y = a * q.x at hq
    rw [hq]
    ring
  · intro hp
    refine ⟨⟨p.x, -p.y⟩, ?_, ?_⟩
    · change -p.y = a * p.x
      change p.y = -a * p.x at hp
      nlinarith
    · ext <;> simp [reflectY]

theorem swapCoordinates_image_horizontal :
    swapCoordinates '' horizontalAxis = verticalAxis := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [swapCoordinates, horizontalAxis, slopeLine, verticalAxis] using hq
  · intro hp
    refine ⟨⟨p.y, p.x⟩, ?_, rfl⟩
    simpa [horizontalAxis, slopeLine, verticalAxis] using hp

theorem reflectY_image_vertical : reflectY '' verticalAxis = verticalAxis := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hp
    refine ⟨⟨p.x, -p.y⟩, hp, ?_⟩
    ext <;> simp [reflectY]

theorem swapCoordinates_image_image (A : Set Point) :
    swapCoordinates '' (swapCoordinates '' A) = A := by
  simp [Set.image_image, swapCoordinates]

theorem reflectY_image_image (A : Set Point) : reflectY '' (reflectY '' A) = A := by
  simp [Set.image_image, reflectY]

/-- The full family of nondegenerate origin-centered lines, including vertical. -/
def IsOriginLine (A : Set Point) : Prop := A = verticalAxis ∨ ∃ a : ℝ, A = slopeLine a

theorem isOriginLine_slope (a : ℝ) : IsOriginLine (slopeLine a) := .inr ⟨a, rfl⟩

theorem isOriginLine_vertical : IsOriginLine verticalAxis := .inl rfl

theorem slopeLine_ne_vertical (a : ℝ) : slopeLine a ≠ verticalAxis := by
  intro h
  have hp : (⟨1, a⟩ : Point) ∈ slopeLine a := by simp [slopeLine]
  rw [h] at hp
  norm_num [verticalAxis] at hp

theorem slopeLine_ne_of_ne {a b : ℝ} (hab : a ≠ b) : slopeLine a ≠ slopeLine b := by
  intro h
  have hp : (⟨1, a⟩ : Point) ∈ slopeLine a := by simp [slopeLine]
  rw [h] at hp
  exact hab (by simpa [slopeLine] using hp)

theorem IsOriginLine.swap {A : Set Point} (h : IsOriginLine A) :
    IsOriginLine (swapCoordinates '' A) := by
  rcases h with rfl | ⟨a, rfl⟩
  · rw [swapCoordinates_image_vertical]
    exact isOriginLine_slope 0
  · by_cases ha : a = 0
    · subst a
      change IsOriginLine (swapCoordinates '' horizontalAxis)
      rw [swapCoordinates_image_horizontal]
      exact isOriginLine_vertical
    · rw [swapCoordinates_image_slope a ha]
      exact isOriginLine_slope _

theorem IsOriginLine.reflect {A : Set Point} (h : IsOriginLine A) :
    IsOriginLine (reflectY '' A) := by
  rcases h with rfl | ⟨a, rfl⟩
  · rw [reflectY_image_vertical]
    exact isOriginLine_vertical
  · rw [reflectY_image_slope]
    exact isOriginLine_slope _

/-- Configurations 1 and 2, allowing either ordering of the component lines. -/
inductive AttractorPair : Set Point → Set Point → Prop where
  | even (s : SlopePair) (h : s.EvenConfig) : AttractorPair (slopeLine s.a) (slopeLine s.b)
  | odd (s : SlopePair) (h : s.OddConfig) : AttractorPair (slopeLine s.a) (slopeLine s.b)
  | axes : AttractorPair horizontalAxis verticalAxis
  | diagonals : AttractorPair (slopeLine 1) (slopeLine (-1))
  | comm {A B : Set Point} : AttractorPair A B → AttractorPair B A

theorem AttractorPair.swap {A B : Set Point} (h : AttractorPair A B) :
    AttractorPair (swapCoordinates '' A) (swapCoordinates '' B) := by
  induction h with
  | even s h =>
    have ha : 0 < s.a := h.1
    have hb : s.b < 0 := by linarith [h.2.2]
    rw [swapCoordinates_image_slope s.a (ne_of_gt ha),
      swapCoordinates_image_slope s.b (ne_of_lt hb)]
    apply AttractorPair.comm
    apply AttractorPair.odd ⟨1 / s.b, 1 / s.a⟩
    change -1 < 1 / s.b ∧ 1 / s.b < 0 ∧ 1 < 1 / s.a
    exact ⟨(lt_div_iff_of_neg hb).mpr (by linarith [h.2.2]),
      div_neg_of_pos_of_neg (by norm_num) hb, (lt_div_iff₀ ha).mpr (by linarith [h.2.1])⟩
  | odd s h =>
    have ha : s.a < 0 := h.2.1
    have hb : 0 < s.b := by linarith [h.2.2]
    rw [swapCoordinates_image_slope s.a (ne_of_lt ha),
      swapCoordinates_image_slope s.b (ne_of_gt hb)]
    apply AttractorPair.comm
    apply AttractorPair.even ⟨1 / s.b, 1 / s.a⟩
    change 0 < 1 / s.b ∧ 1 / s.b < 1 ∧ 1 / s.a < -1
    exact ⟨div_pos (by norm_num) hb, (div_lt_iff₀ hb).mpr (by linarith [h.2.2]),
      (div_lt_iff_of_neg ha).mpr (by linarith [h.1])⟩
  | axes =>
    rw [swapCoordinates_image_horizontal, swapCoordinates_image_vertical]
    exact .comm .axes
  | diagonals =>
    rw [swapCoordinates_image_slope 1 (by norm_num),
      swapCoordinates_image_slope (-1) (by norm_num)]
    norm_num
    exact .diagonals
  | comm h ih => exact .comm ih

theorem AttractorPair.reflect {A B : Set Point} (h : AttractorPair A B) :
    AttractorPair (reflectY '' A) (reflectY '' B) := by
  induction h with
  | even s h =>
    rw [reflectY_image_slope, reflectY_image_slope]
    apply AttractorPair.odd ⟨-s.a, -s.b⟩
    rcases h with ⟨ha, ha', hb⟩
    constructor
    · change -1 < -s.a; linarith
    constructor
    · change -s.a < 0; linarith
    · change 1 < -s.b; linarith
  | odd s h =>
    rw [reflectY_image_slope, reflectY_image_slope]
    apply AttractorPair.even ⟨-s.a, -s.b⟩
    rcases h with ⟨ha, ha', hb⟩
    constructor
    · change 0 < -s.a; linarith
    constructor
    · change -s.a < 1; linarith
    · change -s.b < -1; linarith
  | axes =>
    change AttractorPair (reflectY '' slopeLine 0) (reflectY '' verticalAxis)
    rw [reflectY_image_slope, reflectY_image_vertical, neg_zero]
    exact .axes
  | diagonals =>
    rw [reflectY_image_slope, reflectY_image_slope, neg_neg]
    exact .comm .diagonals
  | comm h ih => exact .comm ih

/-- A chain of exactly `n` genuine two-line midset steps, ending in Configuration
1 or 2. Intermediate pairs must be distinct nondegenerate origin lines. -/
inductive ReducesIn : ℕ → Set Point → Set Point → Prop where
  | done {A B : Set Point} : AttractorPair A B → ReducesIn 0 A B
  | step {n : ℕ} {A B C D : Set Point}
      (hC : IsOriginLine C) (hD : IsOriginLine D) (hne : C ≠ D)
      (hmid : midset A B = C ∪ D) (hnext : ReducesIn n C D) : ReducesIn (n + 1) A B

def ReducesWithin (N : ℕ) (A B : Set Point) : Prop := ∃ n ≤ N, ReducesIn n A B

theorem ReducesIn.comm {n : ℕ} {A B : Set Point} (h : ReducesIn n A B) :
    ReducesIn n B A := by
  cases h with
  | done h => exact .done (.comm h)
  | step hC hD hne hm hn => exact .step hC hD hne (by rw [midset_comm]; exact hm) hn

theorem ReducesIn.map {n : ℕ} {A B : Set Point} (h : ReducesIn n A B)
    (e : Point ≃ᵢ Point)
    (hl : ∀ C, IsOriginLine C → IsOriginLine (e '' C))
    (ha : ∀ C D, AttractorPair C D → AttractorPair (e '' C) (e '' D)) :
    ReducesIn n (e '' A) (e '' B) := by
  induction h with
  | done h => exact .done (ha _ _ h)
  | step hC hD hne hm hn ih =>
    apply ReducesIn.step (hl _ hC) (hl _ hD) (fun he => hne (e.injective.image_injective he))
    · rw [← isometryEquiv_image_midset, hm, Set.image_union]
    · exact ih

theorem ReducesWithin.comm {n : ℕ} {A B : Set Point} (h : ReducesWithin n A B) :
    ReducesWithin n B A := by
  obtain ⟨k, hk, h⟩ := h
  exact ⟨k, hk, h.comm⟩

theorem ReducesWithin.swap {n : ℕ} {A B : Set Point} (h : ReducesWithin n A B) :
    ReducesWithin n (swapCoordinates '' A) (swapCoordinates '' B) := by
  obtain ⟨k, hk, h⟩ := h
  exact ⟨k, hk, h.map swapCoordinates (fun _ h => h.swap) (fun _ _ h => h.swap)⟩

theorem ReducesWithin.reflect {n : ℕ} {A B : Set Point} (h : ReducesWithin n A B) :
    ReducesWithin n (reflectY '' A) (reflectY '' B) := by
  obtain ⟨k, hk, h⟩ := h
  exact ⟨k, hk, h.map reflectY (fun _ h => h.reflect) (fun _ _ h => h.reflect)⟩

theorem attractor_shifted {a : ℝ} (ha : -1 < a ∧ a < 1) :
    AttractorPair (slopeLine (a - 1)) (slopeLine (a + 1)) := by
  rcases lt_trichotomy a 0 with hneg | rfl | hpos
  · apply AttractorPair.comm
    apply AttractorPair.even ⟨a + 1, a - 1⟩
    change 0 < a + 1 ∧ a + 1 < 1 ∧ a - 1 < -1
    constructor
    · linarith [ha.1]
    constructor <;> linarith
  · norm_num
    exact .comm .diagonals
  · apply AttractorPair.odd ⟨a - 1, a + 1⟩
    change -1 < a - 1 ∧ a - 1 < 0 ∧ 1 < a + 1
    constructor
    · linarith
    constructor
    · linarith [ha.2]
    · linarith

/-- Covers both the same-octant and opposite-shallow cases, including zero
average (where the terminal pair is the diagonals). -/
theorem reduces_two_shallow {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hab : a ≠ b) :
    ReducesIn 2 (slopeLine a) (slopeLine b) := by
  let c := (a + b) / 2
  have hc : -1 < c ∧ c < 1 := average_mem_open_unit ha hb hab
  apply ReducesIn.step (isOriginLine_slope c) isOriginLine_vertical
    (slopeLine_ne_vertical c) (midset_two_shallow a b ha hb hab)
  apply ReducesIn.step (isOriginLine_slope (c - 1)) (isOriginLine_slope (c + 1))
    (slopeLine_ne_of_ne (by linarith : c - 1 ≠ c + 1))
    (midset_shallow_vertical c (abs_le.mpr ⟨hc.1.le, hc.2.le⟩))
  exact .done (attractor_shifted hc)

theorem attractor_nonneg_shallow_pos_steep {a b : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hb : 1 < b) :
    AttractorPair (slopeLine (b * (a - 1) / (b - 1)))
      (slopeLine (b * (a + 1) / (b + 1))) := by
  have hb0 : 0 < b := by linarith
  have hbm : 0 < b - 1 := by linarith
  have hbp : 0 < b + 1 := by linarith
  have hd : b * (a - 1) / (b - 1) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hb0 (by linarith)) hbm
  have he : 0 < b * (a + 1) / (b + 1) :=
    div_pos (mul_pos hb0 (by linarith)) hbp
  rcases lt_trichotomy (a * b) 1 with hab | hab | hab
  · apply AttractorPair.comm
    apply AttractorPair.even ⟨b * (a + 1) / (b + 1), b * (a - 1) / (b - 1)⟩
    exact ⟨he, (div_lt_iff₀ hbp).mpr (by nlinarith), (div_lt_iff₀ hbm).mpr (by nlinarith)⟩
  · have hd' : b * (a - 1) / (b - 1) = -1 :=
      (div_eq_iff (ne_of_gt hbm)).mpr (by nlinarith)
    have he' : b * (a + 1) / (b + 1) = 1 :=
      (div_eq_iff (ne_of_gt hbp)).mpr (by nlinarith)
    rw [hd', he']
    exact .comm .diagonals
  · apply AttractorPair.odd ⟨b * (a - 1) / (b - 1), b * (a + 1) / (b + 1)⟩
    exact ⟨(lt_div_iff₀ hbm).mpr (by nlinarith), hd, (lt_div_iff₀ hbp).mpr (by nlinarith)⟩

theorem reduces_nonneg_shallow_pos_steep {a b : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hb : 1 < b) :
    ReducesIn 1 (slopeLine a) (slopeLine b) := by
  have hb0 : 0 < b := by linarith
  have hd : b * (a - 1) / (b - 1) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hb0 (by linarith)) (by linarith)
  have he : 0 < b * (a + 1) / (b + 1) :=
    div_pos (mul_pos hb0 (by linarith)) (by linarith)
  apply ReducesIn.step (isOriginLine_slope _) (isOriginLine_slope _)
    (slopeLine_ne_of_ne (by linarith))
    (midset_shallow_steep a b (abs_le.mpr ⟨by linarith, ha1.le⟩)
      (by rwa [abs_of_pos hb0]))
  exact .done (attractor_nonneg_shallow_pos_steep ha0 ha1 hb)

theorem reduces_axis_steep {b : ℝ} (hb : 1 < |b|) :
    ReducesIn 1 (slopeLine 0) (slopeLine b) := by
  rcases lt_abs.mp hb with hb | hb
  · exact reduces_nonneg_shallow_pos_steep (le_refl 0) (by norm_num) hb
  · have h := reduces_nonneg_shallow_pos_steep (a := 0) (b := -b)
      (le_refl 0) (by norm_num) (by linarith)
    have h' := h.map reflectY (fun _ h => h.reflect) (fun _ _ h => h.reflect)
    simpa only [reflectY_image_slope, neg_zero, neg_neg] using h'

theorem reduces_shallow_pos_steep {a b : ℝ} (ha : |a| ≤ 1) (hb : 1 < b) :
    ReducesWithin 2 (slopeLine a) (slopeLine b) := by
  have hb0 : 0 < b := by linarith
  have hbm : 0 < b - 1 := by linarith
  have hbp : 0 < b + 1 := by linarith
  have habs : 1 < |b| := by rwa [abs_of_pos hb0]
  rcases abs_le.mp ha with ⟨hal, hau⟩
  by_cases ha1 : a = 1
  · subst a
    let e := b * (1 + 1) / (b + 1)
    have he : 1 < e := (lt_div_iff₀ hbp).mpr (by nlinarith)
    have hm : midset (slopeLine 1) (slopeLine b) = slopeLine 0 ∪ slopeLine e := by
      simpa only [sub_self, mul_zero, zero_div] using
        midset_shallow_steep 1 b (by norm_num) habs
    refine ⟨2, le_refl 2, .step (isOriginLine_slope 0) (isOriginLine_slope e)
      (slopeLine_ne_of_ne (by linarith)) hm ?_⟩
    exact reduces_axis_steep (by rwa [abs_of_pos (by linarith : 0 < e)])
  by_cases han : a = -1
  · subst a
    let d := b * (-1 - 1) / (b - 1)
    have hd : d < -1 := (div_lt_iff₀ hbm).mpr (by nlinarith)
    have hm : midset (slopeLine (-1)) (slopeLine b) = slopeLine d ∪ slopeLine 0 := by
      simpa only [neg_add_cancel, mul_zero, zero_div] using
        midset_shallow_steep (-1) b (by norm_num) habs
    refine ⟨2, le_refl 2, .step (isOriginLine_slope d) (isOriginLine_slope 0)
      (slopeLine_ne_of_ne (by linarith)) hm ?_⟩
    apply ReducesIn.comm
    exact reduces_axis_steep (by rw [abs_of_neg (by linarith : d < 0)]; linarith)
  by_cases ha0 : a < 0
  · exact ⟨0, by omega, .done (.odd ⟨a, b⟩ ⟨lt_of_le_of_ne hal (Ne.symm han), ha0, hb⟩)⟩
  · exact ⟨1, by omega, reduces_nonneg_shallow_pos_steep (le_of_not_gt ha0)
      (lt_of_le_of_ne hau ha1) hb⟩

theorem reduces_shallow_steep {a b : ℝ} (ha : |a| ≤ 1) (hb : 1 < |b|) :
    ReducesWithin 2 (slopeLine a) (slopeLine b) := by
  rcases lt_abs.mp hb with hb | hb
  · exact reduces_shallow_pos_steep ha hb
  · have h := reduces_shallow_pos_steep (a := -a) (b := -b)
      (by simpa only [abs_neg] using ha) (by linarith)
    simpa only [reflectY_image_slope, neg_neg] using h.reflect

theorem reduces_two_steep {a b : ℝ} (ha : 1 < |a|) (hb : 1 < |b|) (hab : a ≠ b) :
    ReducesWithin 2 (slopeLine a) (slopeLine b) := by
  have ha0 : a ≠ 0 := by intro h; norm_num [h] at ha
  have hb0 : b ≠ 0 := by intro h; norm_num [h] at hb
  have hai : |1 / a| ≤ 1 := by
    rw [abs_div, abs_one]
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) ha.le
  have hbi : |1 / b| ≤ 1 := by
    rw [abs_div, abs_one]
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hb.le
  have habi : 1 / a ≠ 1 / b := by
    intro h
    exact hab (by simpa only [one_div, inv_inj] using h)
  have h : ReducesWithin 2 (swapCoordinates '' slopeLine a) (swapCoordinates '' slopeLine b) := by
    rw [swapCoordinates_image_slope a ha0, swapCoordinates_image_slope b hb0]
    exact ⟨2, le_refl 2, reduces_two_shallow hai hbi habi⟩
  simpa only [swapCoordinates_image_image] using h.swap

theorem reduces_finite_slopes (a b : ℝ) (hab : a ≠ b) :
    ReducesWithin 2 (slopeLine a) (slopeLine b) := by
  by_cases ha : |a| ≤ 1
  · by_cases hb : |b| ≤ 1
    · exact ⟨2, le_refl 2, reduces_two_shallow ha hb hab⟩
    · exact reduces_shallow_steep ha (lt_of_not_ge hb)
  · by_cases hb : |b| ≤ 1
    · exact (reduces_shallow_steep hb (lt_of_not_ge ha)).comm
    · exact reduces_two_steep (lt_of_not_ge ha) (lt_of_not_ge hb) hab

theorem reduces_slope_vertical (a : ℝ) :
    ReducesWithin 2 (slopeLine a) verticalAxis := by
  by_cases ha : a = 0
  · subst a
    exact ⟨0, by omega, .done .axes⟩
  · have h : ReducesWithin 2 (swapCoordinates '' slopeLine a) (swapCoordinates '' verticalAxis) := by
      rw [swapCoordinates_image_slope a ha, swapCoordinates_image_vertical]
      exact reduces_finite_slopes (1 / a) 0 (one_div_ne_zero ha)
    simpa only [swapCoordinates_image_image] using h.swap

/-- Every pair of distinct nondegenerate origin-centered lines reaches
Configuration 1 or 2 within two steps. This strengthens the paper's three-step
bound and includes all ten configurations and their boundary cases. -/
theorem reduces_origin_lines {A B : Set Point}
    (hA : IsOriginLine A) (hB : IsOriginLine B) (hne : A ≠ B) :
    ReducesWithin 2 A B := by
  rcases hA with rfl | ⟨a, rfl⟩
  · rcases hB with rfl | ⟨b, rfl⟩
    · exact (hne rfl).elim
    · exact (reduces_slope_vertical b).comm
  · rcases hB with rfl | ⟨b, rfl⟩
    · exact reduces_slope_vertical a
    · exact reduces_finite_slopes a b (fun h => hne (congrArg slopeLine h))

/-- Theorem 5's stated bound, with no case omitted. -/
theorem reduces_origin_lines_within_three {A B : Set Point}
    (hA : IsOriginLine A) (hB : IsOriginLine B) (hne : A ≠ B) :
    ReducesWithin 3 A B := by
  obtain ⟨n, hn, h⟩ := reduces_origin_lines hA hB hne
  exact ⟨n, by omega, h⟩

/-- Once Configuration 1 or 2 is reached, there is another genuine pair in
Configuration 1 or 2 whose union is the next midset. -/
theorem AttractorPair.next {A B : Set Point} (h : AttractorPair A B) :
    ∃ C D : Set Point, IsOriginLine C ∧ IsOriginLine D ∧ C ≠ D ∧
      midset A B = C ∪ D ∧ AttractorPair C D := by
  induction h with
  | even s h =>
    have h' := SlopePair.toOdd_config h
    exact ⟨slopeLine s.toOdd.a, slopeLine s.toOdd.b, isOriginLine_slope _,
      isOriginLine_slope _, slopeLine_ne_of_ne h'.distinct,
      SlopePair.midset_eq_toOdd h, .odd _ h'⟩
  | odd s h =>
    have h' := SlopePair.toEven_config h
    exact ⟨slopeLine s.toEven.a, slopeLine s.toEven.b, isOriginLine_slope _,
      isOriginLine_slope _, slopeLine_ne_of_ne h'.distinct,
      SlopePair.midset_eq_toEven h, .even _ h'⟩
  | axes =>
    exact ⟨slopeLine 1, slopeLine (-1), isOriginLine_slope _, isOriginLine_slope _,
      slopeLine_ne_of_ne (by norm_num), midset_axes, .diagonals⟩
  | diagonals =>
    exact ⟨horizontalAxis, verticalAxis, isOriginLine_slope 0, isOriginLine_vertical,
      slopeLine_ne_vertical 0, midset_diagonals, .axes⟩
  | comm h ih =>
    obtain ⟨C, D, hC, hD, hne, hm, ht⟩ := ih
    exact ⟨C, D, hC, hD, hne, by rw [midset_comm]; exact hm, ht⟩

noncomputable def translateBy (v : Point) : Point ≃ᵢ Point where
  toFun p := ⟨p.x + v.x, p.y + v.y⟩
  invFun p := ⟨p.x - v.x, p.y - v.y⟩
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro p q
    simp [dist_eq]

/-- A nondegenerate affine line through `v`. -/
def IsLineThrough (v : Point) (A : Set Point) : Prop :=
  ∃ L : Set Point, IsOriginLine L ∧ A = translateBy v '' L

def AttractorPairAt (v : Point) (A B : Set Point) : Prop :=
  ∃ C D : Set Point, AttractorPair C D ∧ A = translateBy v '' C ∧ B = translateBy v '' D

inductive ReducesInAt (v : Point) : ℕ → Set Point → Set Point → Prop where
  | done {A B : Set Point} : AttractorPairAt v A B → ReducesInAt v 0 A B
  | step {n : ℕ} {A B C D : Set Point}
      (hC : IsLineThrough v C) (hD : IsLineThrough v D) (hne : C ≠ D)
      (hmid : midset A B = C ∪ D) (hnext : ReducesInAt v n C D) : ReducesInAt v (n + 1) A B

theorem ReducesIn.translate {n : ℕ} {A B : Set Point} (h : ReducesIn n A B) (v : Point) :
    ReducesInAt v n (translateBy v '' A) (translateBy v '' B) := by
  induction h with
  | done h => exact .done ⟨_, _, h, rfl, rfl⟩
  | step hC hD hne hm hn ih =>
    apply ReducesInAt.step ⟨_, hC, rfl⟩ ⟨_, hD, rfl⟩
      (fun he => hne ((translateBy v).injective.image_injective he))
    · rw [← isometryEquiv_image_midset, hm, Set.image_union]
    · exact ih

/-- The reduction theorem at an arbitrary intersection point, with every
intermediate line and midset translated by a proved taxicab isometry. -/
theorem reduces_lines_through (v : Point) {A B : Set Point}
    (hA : IsLineThrough v A) (hB : IsLineThrough v B) (hne : A ≠ B) :
    ∃ n ≤ 2, ReducesInAt v n A B := by
  obtain ⟨C, hC, rfl⟩ := hA
  obtain ⟨D, hD, rfl⟩ := hB
  have hCD : C ≠ D := by intro he; exact hne (congrArg (fun L => translateBy v '' L) he)
  obtain ⟨n, hn, h⟩ := reduces_origin_lines hC hD hCD
  exact ⟨n, hn, h.translate v⟩

/-- Lines in their usual implicit affine-coordinate representation. -/
def affineLine (a b c : ℝ) : Set Point := {p | a * p.x + b * p.y = c}

theorem affineLine_isLineThrough (a b c : ℝ) (v : Point)
    (hnd : a ≠ 0 ∨ b ≠ 0) (hv : v ∈ affineLine a b c) :
    IsLineThrough v (affineLine a b c) := by
  change a * v.x + b * v.y = c at hv
  by_cases hb : b = 0
  · have ha : a ≠ 0 := by simpa only [hb, ne_self_iff_false, or_false] using hnd
    refine ⟨verticalAxis, isOriginLine_vertical, ?_⟩
    ext p
    constructor
    · intro hp
      change a * p.x + b * p.y = c at hp
      have he : p.x = v.x := by
        have : a * (p.x - v.x) = 0 := by rw [hb] at hp hv; nlinarith
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha)
      refine ⟨⟨0, p.y - v.y⟩, rfl, ?_⟩
      ext <;> simp [translateBy, he]
    · rintro ⟨q, hq, rfl⟩
      change q.x = 0 at hq
      change a * (q.x + v.x) + b * (q.y + v.y) = c
      simp only [hq, hb, zero_add, zero_mul, add_zero] at hv ⊢
      exact hv
  · refine ⟨slopeLine (-a / b), isOriginLine_slope _, ?_⟩
    ext p
    constructor
    · intro hp
      change a * p.x + b * p.y = c at hp
      refine ⟨⟨p.x - v.x, p.y - v.y⟩, ?_, ?_⟩
      · change p.y - v.y = (-a / b) * (p.x - v.x)
        field_simp
        nlinarith [hp, hv]
      · ext <;> simp [translateBy]
    · rintro ⟨q, hq, rfl⟩
      change q.y = (-a / b) * q.x at hq
      field_simp at hq
      change a * (q.x + v.x) + b * (q.y + v.y) = c
      nlinarith [hq, hv]

/-- In particular, the theorem applies to any two distinct nondegenerate
affine lines with a common point, not just to a slope parametrization. -/
theorem reduces_intersecting_affine_lines
    (a b c d e f : ℝ) (v : Point)
    (h₁ : a ≠ 0 ∨ b ≠ 0) (h₂ : d ≠ 0 ∨ e ≠ 0)
    (hv₁ : v ∈ affineLine a b c) (hv₂ : v ∈ affineLine d e f)
    (hne : affineLine a b c ≠ affineLine d e f) :
    ∃ n ≤ 2, ReducesInAt v n (affineLine a b c) (affineLine d e f) :=
  reduces_lines_through v (affineLine_isLineThrough a b c v h₁ hv₁)
    (affineLine_isLineThrough d e f v h₂ hv₂) hne

/-- Configuration 1 in all four relevant upper-half-plane octants, allowing
either input order. The first slope in a witness is always the shallow one. -/
inductive ConfigurationOnePair : Set Point → Set Point → Prop where
  | even (s : SlopePair) (h : s.EvenConfig) : ConfigurationOnePair (slopeLine s.a) (slopeLine s.b)
  | odd (s : SlopePair) (h : s.OddConfig) : ConfigurationOnePair (slopeLine s.a) (slopeLine s.b)
  | comm {A B : Set Point} : ConfigurationOnePair A B → ConfigurationOnePair B A

/-- Theorem 1: the first midset lies in the other two octants of Configuration
1; the second lies in the original octants. The middle disjunction records
which of the even/odd orientations the three pairs occupy. -/
theorem configuration_one_two_steps {A B : Set Point} (h : ConfigurationOnePair A B) :
    ∃ s t u : SlopePair,
      ((A = slopeLine s.a ∧ B = slopeLine s.b) ∨ (B = slopeLine s.a ∧ A = slopeLine s.b)) ∧
      ((s.EvenConfig ∧ t.OddConfig ∧ u.EvenConfig) ∨
        (s.OddConfig ∧ t.EvenConfig ∧ u.OddConfig)) ∧
      midset A B = slopeLine t.a ∪ slopeLine t.b ∧
      midset (slopeLine t.a) (slopeLine t.b) = slopeLine u.a ∪ slopeLine u.b := by
  induction h with
  | even s h =>
    have ht := SlopePair.toOdd_config h
    exact ⟨s, s.toOdd, s.twoStep, Or.inl ⟨rfl, rfl⟩,
      Or.inl ⟨h, ht, SlopePair.twoStep_config h⟩,
      SlopePair.midset_eq_toOdd h, SlopePair.midset_eq_toEven ht⟩
  | odd s h =>
    have ht := SlopePair.toEven_config h
    exact ⟨s, s.toEven, s.toEven.toOdd, Or.inl ⟨rfl, rfl⟩,
      Or.inr ⟨h, ht, SlopePair.toOdd_config ht⟩,
      SlopePair.midset_eq_toEven h, SlopePair.midset_eq_toOdd ht⟩
  | comm h ih =>
    obtain ⟨s, t, u, hp, hs, hm, hn⟩ := ih
    exact ⟨s, t, u, hp.symm, hs, by rw [midset_comm]; exact hm, hn⟩

theorem configuration_one_next {A B : Set Point} (h : ConfigurationOnePair A B) :
    ∃ C D : Set Point, midset A B = C ∪ D ∧ ConfigurationOnePair C D := by
  obtain ⟨s, t, u, _, hregions, hm, _⟩ := configuration_one_two_steps h
  refine ⟨slopeLine t.a, slopeLine t.b, hm, ?_⟩
  rcases hregions with heven | hodd
  · exact .odd t heven.2.1
  · exact .even t hodd.2.1

end FitzhughFarnsworth
