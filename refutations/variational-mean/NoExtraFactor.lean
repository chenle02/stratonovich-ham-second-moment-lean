/-
Refutation for the identity of `L:variational-heat-envelope`
(`notes/integrated_unmasked_variational.tex` lines 28-29, and line 57: "without
an extra normalization factor"), package theorem
`StratonovichHAMSecondMoment.VariationalMean.heat_identity`.

Wrong variant: the identity with the Fourier factor `(2π)^{-d}`,
`(Γ * p_ε)(x) = (2π)^{-d} ∫ e^{iξ·x} e^{-ε|ξ|²/2} μ(dξ)`, for every `Γ`, `μ`
with the spectral convention.  Counterexample: `d = 1`, `Γ` = Lebesgue
measure, `μ = δ_0` (spectral convention: `∫ φ dx = (∫ φ(x) e^{i0·x} dx)`),
`ε = 1`, `x = 0`: the package identity gives `(Γ * p_1)(0) = 1`, while the
variant gives `1/(2π)`.  `no_extra_factor_contrast` is the package identity
at that point.  Junk reliance: none (`δ_0` integrals are evaluations).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.VariationalMean

set_option autoImplicit false

open MeasureTheory
open StratonovichHAMSecondMoment HomogHypothesis VariationalDilation VariationalMean

namespace Refutations.VariationalMean.Factor

/-- Lebesgue measure on `ℝ¹` has spectral measure `δ_0`. -/
theorem leb_spectral : IsSpectralMeasure (volume : Measure (Rd 1)) (Measure.dirac 0) := by
  intro φ
  rw [integral_dirac]
  simp

/-- The package identity at `Γ` = Lebesgue, `μ = δ_0`, `ε = 1`, `x = 0`. -/
theorem no_extra_factor_contrast :
    ((conv (volume : Measure (Rd 1)) (heatK 1) 0 : ℝ) : ℂ) = 1 := by
  rw [heat_identity leb_spectral one_pos, integral_dirac]
  simp [heatSpec]

/-- The identity with an extra factor `(2π)^{-d}` is false. -/
theorem extra_factor_false :
    ¬ (∀ (Γ μ : Measure (Rd 1)), IsSpectralMeasure Γ μ → ∀ ε : ℝ, 0 < ε → ∀ x : Rd 1,
        ((conv Γ (heatK ε) x : ℝ) : ℂ) =
          ((2 * Real.pi) ^ (-(1 : ℝ)) : ℝ) * ∫ ξ, heatSpec ε x ξ ∂μ) := by
  intro h
  have h1 := h volume (Measure.dirac 0) leb_spectral 1 one_pos 0
  rw [← heat_identity leb_spectral one_pos, no_extra_factor_contrast, mul_one] at h1
  have h2 := congrArg Complex.re h1
  simp only [Complex.one_re, Complex.ofReal_re] at h2
  rw [Real.rpow_neg_one] at h2
  have hpi : (1 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
  have : (2 * Real.pi)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpi
  linarith

end Refutations.VariationalMean.Factor
