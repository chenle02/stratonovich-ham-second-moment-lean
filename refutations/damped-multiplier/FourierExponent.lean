/-
Refutation for `L:damped-homogeneous-norms` (main TeX
`notes/notes_stratonovich_ham_second_moment.tex`, revision a284420, lines
845-846 and 915-916, Green smoothing as a multiplier), package theorem
`StratonovichHAMSecondMoment.DampedMultiplier.charFun_gaussKernel_conv`
(`\widehat{p*G}(ξ) = e^{-v|ξ|²/2} Ĝ(ξ)` for `p = N(0, vI)`).

Wrong variant: wrong constant in the exponent, `e^{-v|ξ|²}` for one smoothed
transform (the factor that appears only in the PRODUCT of two transforms).
Counterexample: `d = 1`, `G = δ₀` (`Ĝ = 1`), `v = 1`, `ξ = e₀`:
`e^{-1/2} ≠ e^{-1}`.  `fourier_exponent_contrast` is the package value at the
same point.  No junk-value reliance (finite measures).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.DampedMultiplier

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment StratonovichHAMSecondMoment.DampedMultiplier

namespace Refutations.DampedMultiplier

/-- The unit vector `e₀` of `ℝ¹`. -/
noncomputable def e1 : HomogHypothesis.Rd 1 := EuclideanSpace.single 0 1

/-- `|e₀| = 1`. -/
theorem norm_e1 : ‖e1‖ = 1 := by simp [e1]

/-- The smoothed transform with multiplier `e^{-v|ξ|²}` (no `1/2`) is false. -/
theorem fourier_exponent_refuted :
    ¬ (∀ v : ℝ, 0 ≤ v → ∀ ξ : HomogHypothesis.Rd 1,
        charFun (gaussKernel v ∗ Measure.dirac (0 : HomogHypothesis.Rd 1)) ξ =
          Complex.exp (-(v * ‖ξ‖ ^ 2)) * charFun (Measure.dirac 0) ξ) := by
  intro h
  have h1 := h 1 zero_le_one e1
  rw [charFun_gaussKernel_conv 1 zero_le_one] at h1
  have hc : charFun (Measure.dirac (0 : HomogHypothesis.Rd 1)) e1 = 1 := by
    simp [charFun_apply]
  rw [hc, mul_one, mul_one, norm_e1] at h1
  simp only [one_pow, one_mul, Complex.ofReal_one] at h1
  have h3 : ((Real.exp (-1 / 2) : ℝ) : ℂ) = ((Real.exp (-1) : ℝ) : ℂ) := by
    push_cast; exact h1
  have h2 := Complex.ofReal_injective h3
  have := Real.exp_lt_exp.2 (show (-1 : ℝ) < -1 / 2 by norm_num)
  linarith

/-- The package value at the same point: `\widehat{p*δ₀}(e₀) = e^{-1/2}`. -/
theorem fourier_exponent_contrast :
    charFun (gaussKernel 1 ∗ Measure.dirac (0 : HomogHypothesis.Rd 1)) e1 =
      Complex.exp (-((1 : ℝ) * ‖e1‖ ^ 2) / 2) * charFun (Measure.dirac 0) e1 :=
  charFun_gaussKernel_conv 1 zero_le_one _ _

end Refutations.DampedMultiplier
