/-
Refutation for the positivity `γ_ε ≥ 0` used in the lower bound of
`E:low-alpha-convolution` (main TeX lines 4752-4755 at a284420), package
theorem `StratonovichHAMSecondMoment.LowAlphaConvolution.heatDens_nonneg`
(the Gaussian density `p_ε ≥ 0`, hypothesis `ε ≥ 0`).

Wrong variant: dropping `ε ≥ 0`.  With `ε = -1` in `d = 2`, the formula
`(2πε)^{-d/2} e^{-|w|²/(2ε)}` at `w = 0` is `(-2π)^{-1} < 0` (Mathlib's real
power of a negative base with exponent `-1` is the inverse).
`negative_variance_contrast` is the package bound at `ε = 1`, `w = 0`.
Junk-value reliance: the value of `rpow` at a negative base (the variant only
exists through it).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.LowAlphaConvolution

set_option autoImplicit false

open Real

namespace Refutations.LowAlphaConvolution

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.LowAlphaConvolution

/-- `p_ε ≥ 0` fails without `ε ≥ 0`. -/
theorem negative_variance_refuted :
    ¬ (∀ ε : ℝ, ∀ w : HomogHypothesis.Rd 2, 0 ≤ heatDens ε w) := by
  intro H
  have h := H (-1) 0
  simp only [heatDens, norm_zero] at h
  have hc : -(((2 : ℕ) : ℝ) / 2) = -1 := by norm_num
  rw [hc, Real.rpow_neg_one] at h
  have hneg : (2 * π * (-1 : ℝ))⁻¹ < 0 := inv_lt_zero.2 (by nlinarith [Real.pi_pos])
  have hpos := Real.exp_pos (-((0 : ℝ) ^ 2 / (2 * -1)))
  nlinarith

/-- The package bound at `ε = 1`, `w = 0`. -/
theorem negative_variance_contrast : 0 ≤ heatDens (d := 2) 1 0 :=
  heatDens_nonneg zero_le_one 0

end Refutations.LowAlphaConvolution
