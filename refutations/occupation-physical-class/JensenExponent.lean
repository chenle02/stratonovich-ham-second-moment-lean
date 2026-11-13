/-
Refutation for the auxiliary Jensen step of `P:occupation-physical-class`
(`notes/integrated_spatial_occupation.tex` lines 423-425 at a284420: concavity of `x^{α/2}`
for `0 < α/2 < 1`), package theorem
`StratonovichHAMSecondMoment.OccupationPhysicalClass.lintegral_rpow_le`
(`∫_0^1 f^p ≤ (∫_0^1 f)^p` for `0 < p < 1`).

Wrong variant: the hypothesis `p < 1` dropped, at `p = 2`.  Counterexample: `f = 2` on
`(0,1/2)` and `0` elsewhere: `∫_0^1 f² = 2` and `(∫_0^1 f)² = 1`.
`jensen_exponent_contrast` applies the package theorem to the same `f` at `p = 1/2`.
No junk-value reliance (all integrals finite).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.OccupationPhysicalClass

set_option autoImplicit false

open MeasureTheory Set StratonovichHAMSecondMoment.OccupationPhysicalClass
open scoped ENNReal

namespace Refutations.OccupationPhysicalClass

/-- The test function `2 · 1_{(-∞,1/2)}`. -/
noncomputable def fJ : ℝ → ℝ≥0∞ := (Iio (1 / 2 : ℝ)).indicator fun _ => 2

theorem volI_Iio_half : volI (Iio (1 / 2 : ℝ)) = ENNReal.ofReal (1 / 2) := by
  rw [Measure.restrict_apply measurableSet_Iio,
    show Iio (1 / 2 : ℝ) ∩ Ioo 0 1 = Ioo 0 (1 / 2) by
      ext x; simp only [mem_inter_iff, mem_Iio, mem_Ioo]; constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩,
    Real.volume_Ioo]
  norm_num

theorem lint_fJ : ∫⁻ s, fJ s ∂volI = 1 := by
  rw [fJ, lintegral_indicator_const measurableSet_Iio, volI_Iio_half,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem lint_fJ_sq : ∫⁻ s, fJ s ^ (2 : ℝ) ∂volI = 2 := by
  have e : (fun s => fJ s ^ (2 : ℝ)) = (Iio (1 / 2 : ℝ)).indicator fun _ => (4 : ℝ≥0∞) := by
    funext s
    by_cases hs : s ∈ Iio (1 / 2 : ℝ)
    · simp only [fJ, indicator_of_mem hs, ENNReal.rpow_two]; norm_num
    · simp only [fJ, indicator_of_notMem hs]
      exact ENNReal.zero_rpow_of_pos (by norm_num)
  rw [e, lintegral_indicator_const measurableSet_Iio, volI_Iio_half,
    ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- Jensen without `p < 1` (at `p = 2`) is false. -/
theorem jensen_exponent_refuted :
    ¬ (∀ f : ℝ → ℝ≥0∞, AEMeasurable f volI →
        ∫⁻ s, f s ^ (2 : ℝ) ∂volI ≤ (∫⁻ s, f s ∂volI) ^ (2 : ℝ)) := by
  intro h
  have := h fJ ((measurable_const.indicator measurableSet_Iio).aemeasurable)
  rw [lint_fJ, lint_fJ_sq, ENNReal.one_rpow] at this
  norm_num at this

/-- The package bound for the same `f` at `p = 1/2`. -/
theorem jensen_exponent_contrast :
    ∫⁻ s, fJ s ^ ((1 : ℝ) / 2) ∂volI ≤ (∫⁻ s, fJ s ∂volI) ^ ((1 : ℝ) / 2) :=
  lintegral_rpow_le ((measurable_const.indicator measurableSet_Iio).aemeasurable)
    (by norm_num) (by norm_num)

end Refutations.OccupationPhysicalClass
