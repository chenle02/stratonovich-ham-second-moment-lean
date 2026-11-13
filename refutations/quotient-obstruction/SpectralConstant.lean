/-
Refutation for `P:masked-quotient-obstruction`
(`notes/integrated_covariance_foundation.tex` lines 266-267 at a284420:
`μ = (2π)^{-1} dξ₁ δ₀(dξ₂)`), package theorem
`StratonovichHAMSecondMoment.QuotientObstruction.spectral_Gamma0`.

Wrong variant: the normalization `(2π)^{-1}` dropped, i.e. `dξ₁ δ₀(dξ₂)`
(`lineMeasure e1`) is the spectral measure of `Γ = δ₀(dx₁) dx₂` in the
convention of `H:homog`.
Counterexample: the Gaussian Schwartz test `φ(x) = e^{-|x|²}`
(`GaussianTest.gaussTest 1 _ 0 0`), for which `∫ φ dΓ = √π ≠ 0`; the package
identity (`spectral_Gamma0`, the contrast) makes the wrong right side `2π` times
the left side.
No junk-value reliance (`φ` is integrable on the axis; the package proves the
spectral identity for every Schwartz test).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.QuotientObstruction
import StratonovichHAMSecondMoment.GaussianTest

set_option autoImplicit false

open MeasureTheory Real
open StratonovichHAMSecondMoment HomogHypothesis QuotientObstruction

namespace Refutations.QuotientObstruction

/-- `∫ e^{-|x|²} Γ(dx) = √π`. -/
theorem Gamma0_gauss :
    ∫ x, GaussianTest.gaussTest (E := Rd 2) 1 one_pos 0 0 x ∂Gamma0 = (Real.sqrt π : ℂ) := by
  rw [Gamma0, integral_lineMeasure norm_e2]
  have hpt : ∀ t : ℝ, GaussianTest.gaussTest (E := Rd 2) 1 one_pos 0 0 (t • e2) =
      ((Real.exp (-1 * t ^ 2) : ℝ) : ℂ) := by
    intro t
    rw [GaussianTest.gaussTest_apply]
    simp [norm_smul, norm_e2]
  simp_rw [hpt]
  rw [integral_complex_ofReal, integral_gaussian]
  simp

/-- The package spectral identity at the Gaussian test. -/
theorem spectral_constant_contrast :
    ∫ x, GaussianTest.gaussTest (E := Rd 2) 1 one_pos 0 0 x ∂Gamma0 =
      ∫ ξ, (∫ x, GaussianTest.gaussTest (E := Rd 2) 1 one_pos 0 0 x *
        Complex.exp (Complex.I * (inner ℝ ξ x : ℝ))) ∂mu0 :=
  spectral_Gamma0 _

/-- `dξ₁ δ₀(dξ₂)` without the factor `(2π)^{-1}` is not the spectral measure of
`Γ = δ₀(dx₁) dx₂`. -/
theorem spectral_constant_refuted : ¬ IsSpectralMeasure Gamma0 (lineMeasure e1) := by
  intro h
  have h1 := spectral_constant_contrast
  rw [mu0, integral_smul_measure, ← h, Gamma0_gauss,
    ENNReal.toReal_ofReal (by positivity)] at h1
  have h2 : Real.sqrt π = (2 * π)⁻¹ * Real.sqrt π := by
    have := congrArg Complex.re h1
    simpa using this
  have hs : 0 < Real.sqrt π := Real.sqrt_pos.2 pi_pos
  have h3 : (2 * π)⁻¹ = 1 := by
    field_simp at h2 ⊢
    nlinarith
  have : 2 * π = 1 := by
    rw [inv_eq_one] at h3; exact h3
  linarith [pi_gt_three]

end Refutations.QuotientObstruction
