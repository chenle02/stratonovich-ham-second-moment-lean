import StratonovichHAMSecondMoment.DampedSmoothing
import StratonovichHAMSecondMoment.WhiteModel

/-!
Refutation for the hypothesis `0 < ε` of
`StratonovichHAMSecondMoment.DampedSmoothing.smoothedCov_spectral` (covariance smoothing
of `L:damped-homogeneous-norms`, main TeX lines 1052-1053; the TeX smooths with `ε > 0`).

Class (c), control of Lean's totalized arithmetic outside the manuscript domain: at
`ε = 0` the Lean density `p_0` is `0^{-1/2} e^{-|w|²/0} = 0` (Lean's `0^{-1/2} = 0`),
so `p_0 * Γ = 0`, while the multiplier `e^{-0}` is `1` and `μ` is not `0`.
Witness: white model `Γ = δ₀`, `μ = (2π)⁻¹ Lebesgue` on `ℝ¹` (`H:homog`).

Wrong variant: `0 < ε` weakened to `0 ≤ ε`.

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

/-- Lean's junk value: `p_0 * Γ` is the zero measure. -/
theorem smoothedCov_zero (Γ : Measure (Rd 1)) : smoothedCov Γ 0 = 0 := by
  have hp : ∀ w : Rd 1, LowAlphaConvolution.heatDens 0 w = 0 := by
    intro w
    simp only [LowAlphaConvolution.heatDens, mul_zero]
    rw [Real.zero_rpow (by norm_num), zero_mul]
  have hg : ∀ x, LowAlphaConvolution.gammaEps Γ 0 x = 0 := by
    intro x
    simp [LowAlphaConvolution.gammaEps, hp]
  simp [smoothedCov, hg]

/-- Contrast: `p_0 * Γ = 0` for the white model, while for `ε = 1` the theorem holds. -/
theorem eps_zero_junk_contrast :
    smoothedCov (whiteCov 1) 0 = 0 ∧
      IsSpectralMeasure (smoothedCov (whiteCov 1) 1)
        (smoothed (whiteSpectral 1) (gaussMult (1 / 2))) := by
  have hH := white_homogCovariance (c := 1) (a := 1 / 2) zero_le_one (by norm_num) (by norm_num)
  exact ⟨smoothedCov_zero _, (spatial_smoothing_multiplier_paper hH 1 one_pos).2.2.2.2⟩

/-- The wrong variant (`0 ≤ ε` in place of `0 < ε`, under `H:homog`) is false. -/
theorem eps_zero_junk :
    ¬ ∀ (alpha alpha0 : ℝ) (Γ μ : Measure (Rd 1)), HomogCovariance 1 alpha alpha0 Γ μ →
      ∀ ε : ℝ, 0 ≤ ε →
        IsSpectralMeasure (smoothedCov Γ ε) (smoothed μ (gaussMult (ε / 2))) := by
  intro H
  have h := H 1 (1 / 2) _ _ (white_homogCovariance zero_le_one (by norm_num) (by norm_num))
    0 le_rfl
  rw [eps_zero_junk_contrast.1] at h
  have hm := isMultiplier_gaussMult (d := 1) (0 / 2) (by norm_num)
  have h0 : IsSpectralMeasure (0 : Measure (Rd 1)) (smoothed (whiteSpectral 1) 0) := by
    intro φ
    simp [smoothed]
  refine spectral_multiplier_separation (whiteSpectral_tempered 1) whiteSpectral_compl_ne'
    hm.1 measurable_const hm.2 (fun _ => zero_le) (fun ξ _ => ?_) h h0
  show (0 : NNReal) < gaussMult (0 / 2) ξ
  rw [← NNReal.coe_lt_coe, NNReal.coe_zero, coe_gaussMult]
  exact Real.exp_pos _

end Refutations.DampedSmoothing
