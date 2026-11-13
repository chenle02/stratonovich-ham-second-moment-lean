/-
Refutation for the Gaussian Fourier integral of `GaussianTest`, package
theorem `StratonovichHAMSecondMoment.GaussianTest.gaussTest_fourier`
(`notes/integrated_covariance_foundation.tex` lines 61-64 at a284420, constant
`(2√π/r)^d = (π/s)^{d/2}` with `s = r²/4`), package definition
`StratonovichHAMSecondMoment.GaussianTest.gaussTest`.

Wrong variant: exponent `d` instead of `d/2` in the constant, i.e.
`∫ gaussTest(x) e^{i⟨ξ,x⟩} dx = (π/s)^d e^{i⟨ξ-y,w⟩} e^{-|ξ-y|²/(4s)}`.
Counterexample: `d = 1`, `s = 1`, `w = y = ξ = 0`: the integral is `√π`
(package theorem) while the variant gives `π`, and `√π ≠ π` since `π > 1`.
`fourier_exponent_contrast` is the package identity at the same point.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.GaussianTest

set_option autoImplicit false

open MeasureTheory Real
open StratonovichHAMSecondMoment HomogHypothesis GaussianTest

namespace Refutations.MaskedSpectralGrowth

/-- The package identity at `d = 1`, `s = 1`, `w = y = ξ = 0`. -/
theorem fourier_exponent_contrast :
    ∫ x, gaussTest (E := Rd 1) 1 one_pos 0 0 x * Complex.exp (Complex.I * (inner ℝ (0 : Rd 1) x : ℝ)) =
      ((Real.pi / 1) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) *
        Complex.exp (Complex.I * (inner ℝ ((0 : Rd 1) - 0) 0 : ℝ)) *
          (Real.exp (-(‖(0 : Rd 1) - 0‖ ^ 2 / (4 * 1))) : ℂ) :=
  gaussTest_fourier 1 one_pos 0 0 0

/-- The constant `(π/s)^d` (exponent `d` instead of `d/2`) is false. -/
theorem fourier_exponent_refuted :
    ¬ (∀ (s : ℝ) (hs : 0 < s) (w y ξ : Rd 1),
        ∫ x, gaussTest s hs w y x * Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) =
          ((Real.pi / s) ^ ((1 : ℕ) : ℝ) : ℝ) *
            Complex.exp (Complex.I * (inner ℝ (ξ - y) w : ℝ)) *
              (Real.exp (-(‖ξ - y‖ ^ 2 / (4 * s))) : ℂ)) := by
  intro h
  have h1 := h 1 one_pos 0 0 0
  rw [fourier_exponent_contrast] at h1
  simp only [sub_zero, inner_zero_left, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    mul_one, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    neg_zero, Real.exp_zero, Complex.ofReal_one, div_one] at h1
  have h2 : Real.pi ^ (((1 : ℕ) : ℝ) / 2) = Real.pi ^ ((1 : ℕ) : ℝ) := by exact_mod_cast h1
  have h3 : Real.pi ^ (((1 : ℕ) : ℝ) / 2) < Real.pi ^ ((1 : ℕ) : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by linarith [Real.pi_gt_three]) (by norm_num)
  linarith

end Refutations.MaskedSpectralGrowth
