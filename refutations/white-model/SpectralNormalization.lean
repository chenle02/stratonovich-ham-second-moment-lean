import StratonovichHAMSecondMoment.WhiteModel

/-!
Refutation for `StratonovichHAMSecondMoment.WhiteModel.whiteSpectral_isSpectral` (and so for
`white_homogCovariance`, `white_model_paper`): the white model of
`notes/integrated_white_evaluation.tex` (edf7085f, lines 4-9) under `H:homog`.

Wrong variant: the spectral measure of `c δ₀` taken as `c · Lebesgue`, forgetting the factor
`1/(2π)` of the convention `Γ = ∫ e^{iξx} μ(dξ)`.  Counterexample: `c = 1` and a smooth bump
`φ` with `φ(0) = 1`; the package identity gives `φ(0) = (1/(2π)) X` for the double integral
`X`, the wrong variant gives `φ(0) = X`, so `φ(0) = 0`.  No junk-value reliance.
`spectral_normalization_contrast` is the package identity at `c = 1`.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory

namespace Refutations.WhiteModel

open StratonovichHAMSecondMoment.HomogHypothesis StratonovichHAMSecondMoment.WhiteModel

/-- `c · Lebesgue` is not the spectral measure of `c δ₀` (at `c = 1`). -/
theorem spectral_normalization_refuted :
    ¬ IsSpectralMeasure (whiteCov 1) (ENNReal.ofReal 1 • (volume : Measure (Rd 1))) := by
  intro h
  let b : ContDiffBump (0 : Rd 1) := ⟨1, 2, by norm_num, by norm_num⟩
  have hsupp : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((b x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  set φ := hsupp.toSchwartzMap hsmooth
  have hgood := whiteSpectral_isSpectral (c := 1) zero_le_one φ
  have hbad := h φ
  have h0 : φ 0 = 1 := by
    simp [φ, b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
  set X := ∫ ξ, (∫ x, φ x * Complex.exp (Complex.I * (inner ℝ ξ x : ℝ))) ∂(volume : Measure (Rd 1))
  rw [whiteSpectral, integral_smul_measure, integral_whiteCov zero_le_one, h0,
    ENNReal.toReal_ofReal (by positivity)] at hgood
  rw [integral_smul_measure, integral_whiteCov zero_le_one, h0,
    ENNReal.toReal_ofReal zero_le_one, one_smul, one_smul] at hbad
  rw [← hbad, one_smul, Complex.real_smul, mul_one] at hgood
  have := congrArg Complex.re hgood
  rw [Complex.one_re, Complex.ofReal_re] at this
  have hp := Real.pi_gt_three
  field_simp at this
  linarith

/-- Contrast: the package identity at `c = 1` (spectral measure `(1/(2π)) Lebesgue`). -/
theorem spectral_normalization_contrast : IsSpectralMeasure (whiteCov 1) (whiteSpectral 1) :=
  whiteSpectral_isSpectral zero_le_one

end Refutations.WhiteModel
