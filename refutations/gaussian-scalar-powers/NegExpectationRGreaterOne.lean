import StratonovichHAMSecondMoment.GaussianScalarPowers

/-!
Refutation for `StratonovichHAMSecondMoment.GaussianScalarPowers.expectation_rpow_le`
(manuscript `L:gaussian-scalar-powers`, part (4)): the hypothesis `r < 1` cannot
be dropped.

The wrong variant is the package statement (same binders and remaining
hypotheses, the sample space quantified over `Type`) with `hr1 : r < 1` removed.
Counterexample: `Ω = Bool` with the uniform probability measure,
`Z true = 2`, `Z false = 0`, `r = 2`: `E Z^2 = 2 > 1 = (E Z)^2`.
This is strictly more faithful than the earlier Mathlib-only version, which
fixed `Ω = Bool`, `r = 2` and kept only the integral inequality.
The contrast theorem records that `r = 2` violates only `r < 1` and applies the
package theorem to the same `μ`, `Z` for every `r ∈ (0, 1)`.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory

namespace Refutations.GaussianScalarPowers

/-- `expectation_rpow_le` without the hypothesis `r < 1` is false. -/
theorem expectation_rpow_le_drop_r_lt_one :
    ¬ (∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Z : Ω → ℝ), Integrable Z μ → 0 ≤ᵐ[μ] Z → ∀ (r : ℝ), 0 < r →
      Integrable (fun ω => Z ω ^ r) μ ∧ ∫ ω, Z ω ^ r ∂μ ≤ (∫ ω, Z ω ∂μ) ^ r) := by
  intro h
  let μ : Measure Bool := (2⁻¹ : ENNReal) • Measure.count
  have hμ : IsProbabilityMeasure μ := ⟨by simp [μ, Measure.count_apply_finite,
    ENNReal.inv_mul_cancel]⟩
  have := (h Bool μ (fun b => if b then 2 else 0) (Integrable.of_finite)
    (Filter.Eventually.of_forall fun b => by cases b <;> norm_num) 2 (by norm_num)).2
  simp [μ, integral_smul_measure, integral_count] at this
  norm_num at this

/-- Contrast: the counterexample `r = 2` violates exactly the dropped hypothesis
`r < 1`; for the same `μ` and `Z` the package theorem holds for every `r ∈ (0, 1)`. -/
theorem expectation_rpow_le_drop_r_lt_one_contrast :
    ¬ ((2 : ℝ) < 1) ∧
      ∀ r : ℝ, 0 < r → r < 1 →
        ∫ b : Bool, (if b then (2 : ℝ) else 0) ^ r ∂((2⁻¹ : ENNReal) • Measure.count) ≤
          (∫ b : Bool, (if b then (2 : ℝ) else 0) ∂((2⁻¹ : ENNReal) • Measure.count)) ^ r := by
  refine ⟨by norm_num, fun r hr0 hr1 => ?_⟩
  have : IsProbabilityMeasure ((2⁻¹ : ENNReal) • (Measure.count : Measure Bool)) :=
    ⟨by simp [Measure.count_apply_finite, ENNReal.inv_mul_cancel]⟩
  exact (StratonovichHAMSecondMoment.GaussianScalarPowers.expectation_rpow_le
    ((2⁻¹ : ENNReal) • Measure.count) (fun b : Bool => if b then (2 : ℝ) else 0)
    Integrable.of_finite
    (Filter.Eventually.of_forall fun b => by cases b <;> norm_num) r hr0 hr1).2

end Refutations.GaussianScalarPowers
