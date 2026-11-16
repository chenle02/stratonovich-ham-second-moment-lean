import StratonovichHAMSecondMoment.DampedSmoothing
import StratonovichHAMSecondMoment.WhiteModel

/-!
Refutation for the Gaussian constant of the covariance-smoothing assertion of
`L:damped-homogeneous-norms` (main TeX lines 1052-1053, proof 1150-1151), package theorem
`StratonovichHAMSecondMoment.DampedSmoothing.smoothedCov_spectral` (spectral measure
`e^{-ε|ξ|²/2} μ` of `p_ε * Γ`, with `p_ε` of covariance `ε I`).

Class (a), manuscript-claim perturbation in the manuscript domain: the witness is the
white model `Γ = δ₀`, `μ = (2π)⁻¹ Lebesgue` on `ℝ¹`, which satisfies `H:homog`
(`WhiteModel.white_homogCovariance`), with `ε = 1 > 0`.

Wrong variant: the multiplier `e^{-ε|ξ|²}` (the factor `1/2` dropped).  The Gaussian
test function `e^{-|x|²}` separates the two multipliers
(`DampedSmoothing.spectral_multiplier_separation`).

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory

namespace Refutations.DampedSmoothing

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.DampedSmoothing
open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure)
open DampedNormsHomog (smoothed)
open DampedMultiplier (gaussMult coe_gaussMult isMultiplier_gaussMult)
open WhiteModel (whiteCov whiteSpectral white_homogCovariance whiteSpectral_tempered)

/-- The white spectral measure charges `{ξ ≠ 0}`. -/
theorem whiteSpectral_compl_ne : whiteSpectral 1 ({0}ᶜ : Set (Rd 1)) ≠ 0 := by
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

/-- Contrast: `e^{-|ξ|²/2} μ` is a spectral measure of `p_1 * δ₀`, and `e^{-|ξ|²} μ`
is not. -/
theorem wrong_gauss_constant_contrast :
    IsSpectralMeasure (smoothedCov (whiteCov 1) 1) (smoothed (whiteSpectral 1) (gaussMult (1 / 2)))
      ∧ ¬ IsSpectralMeasure (smoothedCov (whiteCov 1) 1)
        (smoothed (whiteSpectral 1) (gaussMult 1)) := by
  have hH := white_homogCovariance (c := 1) (a := 1 / 2) zero_le_one (by norm_num) (by norm_num)
  obtain ⟨-, -, -, -, hsp⟩ := spatial_smoothing_multiplier_paper hH 1 one_pos
  have hm := isMultiplier_gaussMult (d := 1) (1 / 2) (by norm_num)
  refine ⟨hsp, spectral_multiplier_separation (whiteSpectral_tempered 1) whiteSpectral_compl_ne
    hm.1 (isMultiplier_gaussMult (d := 1) 1 zero_le_one).1 hm.2 (fun ξ => ?_)
    (fun ξ hξ => ?_) hsp⟩
  · rw [← NNReal.coe_le_coe, coe_gaussMult, coe_gaussMult, Real.exp_le_exp]
    nlinarith [sq_nonneg ‖ξ‖]
  · have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    rw [← NNReal.coe_lt_coe, coe_gaussMult, coe_gaussMult, Real.exp_lt_exp]
    nlinarith [pow_pos hn 2]

/-- The wrong variant (multiplier `e^{-ε|ξ|²}` under `H:homog`, `ε > 0`) is false. -/
theorem wrong_gauss_constant :
    ¬ ∀ (alpha alpha0 : ℝ) (Γ μ : Measure (Rd 1)), HomogCovariance 1 alpha alpha0 Γ μ →
      ∀ ε : ℝ, 0 < ε → IsSpectralMeasure (smoothedCov Γ ε) (smoothed μ (gaussMult ε)) := by
  intro H
  exact wrong_gauss_constant_contrast.2 (H 1 (1 / 2) _ _
    (white_homogCovariance zero_le_one (by norm_num) (by norm_num)) 1 one_pos)

end Refutations.DampedSmoothing
