import StratonovichHAMSecondMoment.DampedSmoothing
import StratonovichHAMSecondMoment.WhiteModel

/-!
Refutation for the multiplier itself in the covariance-smoothing assertion of
`L:damped-homogeneous-norms` (main TeX lines 1052-1053, proof 1150-1151), package theorem
`StratonovichHAMSecondMoment.DampedSmoothing.smoothedCov_spectral`.

Class (a), manuscript-claim perturbation in the manuscript domain: white model
`Γ = δ₀`, `μ = (2π)⁻¹ Lebesgue` on `ℝ¹` (`H:homog` by
`WhiteModel.white_homogCovariance`), `ε = 1 > 0`.

Wrong variant: smoothing does not change the spectral measure (multiplier `m = 1`, i.e.
`μ` itself is a spectral measure of `p_ε * Γ`).  Separated from the true multiplier
`e^{-ε|ξ|²/2}` by the Gaussian test (`spectral_multiplier_separation`).

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory

namespace Refutations.DampedSmoothing

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.DampedSmoothing
open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure)
open DampedNormsHomog (smoothed)
open DampedMultiplier (gaussMult coe_gaussMult isMultiplier_gaussMult IsMultiplier)
open WhiteModel (whiteCov whiteSpectral white_homogCovariance whiteSpectral_tempered)

/-- The white spectral measure charges `{ξ ≠ 0}`. -/
theorem whiteSpectral_compl_ne' : whiteSpectral 1 ({0}ᶜ : Set (Rd 1)) ≠ 0 := by
  intro h
  have hu := measure_univ_le_add_compl (μ := whiteSpectral 1) ({0} : Set (Rd 1))
  have h0 : whiteSpectral 1 ({0} : Set (Rd 1)) = 0 := by
    simp [whiteSpectral, Measure.smul_apply, measure_singleton]
  rw [h0, h, add_zero, nonpos_iff_eq_zero, Measure.measure_univ_eq_zero] at hu
  have hv : whiteSpectral 1 Set.univ ≠ 0 := by
    simp only [whiteSpectral, Measure.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero,
      ENNReal.ofReal_eq_zero, not_or, not_le]
    exact ⟨by positivity, (Measure.measure_univ_pos.2 (NeZero.ne _)).ne'⟩
  exact hv (by rw [hu]; rfl)

/-- Contrast: `e^{-|ξ|²/2} μ` is a spectral measure of `p_1 * δ₀` and `μ` is not. -/
theorem no_smoothing_change_contrast :
    IsSpectralMeasure (smoothedCov (whiteCov 1) 1)
        (smoothed (whiteSpectral 1) (gaussMult (1 / 2))) ∧
      ¬ IsSpectralMeasure (smoothedCov (whiteCov 1) 1) (whiteSpectral 1) := by
  have hH := white_homogCovariance (c := 1) (a := 1 / 2) zero_le_one (by norm_num) (by norm_num)
  obtain ⟨-, -, -, -, hsp⟩ := spatial_smoothing_multiplier_paper hH 1 one_pos
  have hm := isMultiplier_gaussMult (d := 1) (1 / 2) (by norm_num)
  refine ⟨hsp, fun h1 => ?_⟩
  have h1' : IsSpectralMeasure (smoothedCov (whiteCov 1) 1)
      (smoothed (whiteSpectral 1) (fun _ => 1)) := by
    simpa [smoothed] using h1
  refine spectral_multiplier_separation (whiteSpectral_tempered 1) whiteSpectral_compl_ne'
    measurable_const hm.1 (fun _ => le_rfl) hm.2 (fun ξ hξ => ?_) h1' hsp
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  rw [← NNReal.coe_lt_coe, coe_gaussMult, NNReal.coe_one]
  exact lt_of_lt_of_eq (Real.exp_lt_exp.2 (by nlinarith [pow_pos hn 2] : _ < (0 : ℝ)))
    Real.exp_zero

/-- The wrong variant (`μ` itself a spectral measure of `p_ε * Γ`, `H:homog`,
`ε > 0`) is false. -/
theorem no_smoothing_change :
    ¬ ∀ (alpha alpha0 : ℝ) (Γ μ : Measure (Rd 1)), HomogCovariance 1 alpha alpha0 Γ μ →
      ∀ ε : ℝ, 0 < ε → IsSpectralMeasure (smoothedCov Γ ε) μ := by
  intro H
  exact no_smoothing_change_contrast.2 (H 1 (1 / 2) _ _
    (white_homogCovariance zero_le_one (by norm_num) (by norm_num)) 1 one_pos)

end Refutations.DampedSmoothing
