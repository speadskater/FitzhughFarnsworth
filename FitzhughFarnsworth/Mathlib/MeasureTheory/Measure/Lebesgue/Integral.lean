/-
Copyright (c) 2026 Josh Fitzhugh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Fitzhugh
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Area of a region including its boundary graphs

Closed-vertical-section versions of `volume_regionBetween_eq_integral'` and
`volume_regionBetween_eq_integral`. The base measure and measurable set are
arbitrary. Only integrability on that set and an almost-everywhere ordering
are needed; continuity and compactness are not required.
-/

public section

open Set MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
  {f g : α → ℝ} {s : Set α}

/-- The volume between two integrable functions, including both boundary graphs,
is the integral of their difference when they are ordered almost everywhere. -/
theorem volume_region_between_cc_eq_integral' (hf : IntegrableOn f s μ)
    (hg : IntegrableOn g s μ) (hs : MeasurableSet s) (hfg : f ≤ᵐ[μ.restrict s] g) :
    μ.prod volume {p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ Icc (f p.1) (g p.1)} =
      ENNReal.ofReal (∫ x in s, g x - f x ∂μ) := by
  let region : Set (α × ℝ) := {p | p.1 ∈ s ∧ p.2 ∈ Icc (f p.1) (g p.1)}
  have hsupport : region ⊆ s ×ˢ univ := fun _ h ↦ ⟨h.1, mem_univ _⟩
  have hrestrict : μ.prod volume region = (μ.restrict s).prod volume region := by
    rw [Measure.restrict_prod_eq_prod_univ, Measure.restrict_eq_self _ hsupport]
  change μ.prod volume region = _
  rw [hrestrict, Measure.prod_apply₀ (nullMeasurableSet_region_between_cc (μ.restrict s)
    hf.aemeasurable hg.aemeasurable hs.nullMeasurableSet)]
  have hsection : (fun x ↦ volume (Prod.mk x ⁻¹' region)) =ᵐ[μ.restrict s]
      fun x ↦ ENNReal.ofReal (g x - f x) := by
    filter_upwards [ae_restrict_mem hs] with x hx
    have hpre : Prod.mk x ⁻¹' region = Icc (f x) (g x) := by
      ext y
      exact and_iff_right hx
    rw [hpre, Real.volume_Icc]
  rw [lintegral_congr_ae hsection]
  exact (ofReal_integral_eq_lintegral_ofReal (hg.sub hf)
    (hfg.mono fun _ h ↦ sub_nonneg.mpr h)).symm

/-- The volume between two integrable, pointwise ordered functions on a measurable set,
including both boundary graphs, is the integral of their difference. -/
theorem volume_region_between_cc_eq_integral (hf : IntegrableOn f s μ)
    (hg : IntegrableOn g s μ) (hs : MeasurableSet s) (hfg : ∀ x ∈ s, f x ≤ g x) :
    μ.prod volume {p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ Icc (f p.1) (g p.1)} =
      ENNReal.ofReal (∫ x in s, g x - f x ∂μ) :=
  volume_region_between_cc_eq_integral' hf hg hs
    ((ae_restrict_iff' hs).mpr (Filter.Eventually.of_forall hfg))
