/-
Refutation for the Gaussian bound of `P:masked-spectral-growth`
(`notes/integrated_covariance_foundation.tex` lines 46-47 at a284420),
package theorem
`StratonovichHAMSecondMoment.MaskedSpectralGrowth.translated_gauss_le`.

Wrong variant: the exponent `r^α` replaced by `r^{α+1}`, i.e. for every `Γ`, `μ`
with the spectral convention and `Γ(cA) = c^{d-α}Γ(A)`,
`∫ e^{-|ξ-y|²/r²} μ(dξ) ≤ r^{α+1} M_Γ/(2√π)^d`.
Counterexample: `d = 1`, `Γ` = Lebesgue measure, `μ = δ_0`, `α = 0` (outside
the range of `H:homog`, but inside the hypotheses of the general theorem):
the spectral convention holds, `Γ(cA) = c Γ(A)`, `M_Γ = 2√π`, and at `y = 0`,
`r = 1/2` the left side is `1` and the right side `1/2`.
`exponent_shift_contrast` applies the package theorem at the same point:
`1 ≤ r^0 M_Γ/(2√π)`, which holds with equality.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.MaskedSpectralGrowth

set_option autoImplicit false

open MeasureTheory Real
open StratonovichHAMSecondMoment HomogHypothesis SpectralHomog MaskedSpectralGrowth

namespace Refutations.MaskedSpectralGrowth

/-- Lebesgue measure on `ℝ¹` has spectral measure `δ_0`. -/
theorem leb_spectral : IsSpectralMeasure (volume : Measure (Rd 1)) (Measure.dirac 0) := by
  intro φ
  rw [integral_dirac]
  simp

/-- Lebesgue measure on `ℝ¹` scales with exponent `d - α = 1 - 0`. -/
theorem leb_scaling : SpectralHomogeneous (volume : Measure (Rd 1)) (((1 : ℕ) : ℝ) - 0) := by
  intro A _ c hc
  rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, pow_one, abs_of_pos hc]
  norm_num

/-- `M_Γ = 2√π` for Lebesgue measure on `ℝ¹`. -/
theorem leb_MGamma : MGamma (volume : Measure (Rd 1)) = 2 * Real.sqrt Real.pi := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Rd 1) (b := 1 / 4) (by norm_num)
  rw [finrank_euclideanSpace_fin] at h
  unfold MGamma
  have hpt : ∀ x : Rd 1, Real.exp (-(‖x‖ ^ 2 / 4)) = Real.exp (-(1 / 4) * ‖x‖ ^ 2) := by
    intro x; congr 1; ring
  simp_rw [hpt, h]
  rw [show Real.pi / (1 / 4) = (2 * Real.sqrt Real.pi) ^ 2 by
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]; ring]
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
  norm_num

/-- The left side at `μ = δ_0`, `y = 0`: `∫ e^{-|ξ|²/r²} dδ_0 = 1`. -/
theorem dirac_gauss (r : ℝ) :
    ∫ ξ, Real.exp (-(‖ξ - 0‖ ^ 2 / r ^ 2)) ∂(Measure.dirac (0 : Rd 1)) = 1 := by
  rw [integral_dirac]; simp

/-- The bound with `r^{α+1}` in place of `r^α` is false. -/
theorem exponent_shift_refuted :
    ¬ (∀ (Γ μ : Measure (Rd 1)) (alpha : ℝ), IsSpectralMeasure Γ μ →
        SpectralHomogeneous Γ (((1 : ℕ) : ℝ) - alpha) → ∀ (y : Rd 1) (r : ℝ), 0 < r →
        ∫ ξ, Real.exp (-(‖ξ - y‖ ^ 2 / r ^ 2)) ∂μ ≤
          r ^ (alpha + 1) * MGamma Γ / (2 * Real.sqrt Real.pi) ^ 1) := by
  intro h
  have := h volume (Measure.dirac 0) 0 leb_spectral leb_scaling 0 (1 / 2) (by norm_num)
  rw [dirac_gauss, leb_MGamma] at this
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have h2 : (0 : ℝ) < 2 * Real.sqrt Real.pi := by positivity
  rw [zero_add, Real.rpow_one, pow_one, mul_div_assoc, div_self h2.ne'] at this
  norm_num at this

/-- The package bound at the same point: `1 ≤ r^0 M_Γ/(2√π)` (equality). -/
theorem exponent_shift_contrast :
    ∫ ξ, Real.exp (-(‖ξ - 0‖ ^ 2 / (1 / 2 : ℝ) ^ 2)) ∂(Measure.dirac (0 : Rd 1)) ≤
      (1 / 2 : ℝ) ^ (0 : ℝ) * MGamma (volume : Measure (Rd 1)) /
        (2 * Real.sqrt Real.pi) ^ 1 :=
  translated_gauss_le leb_spectral leb_scaling 0 (1 / 2) (by norm_num)

end Refutations.MaskedSpectralGrowth
