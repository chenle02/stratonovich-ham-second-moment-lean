/-
Refutation for the constant of `E:low-alpha-radial` (main TeX lines
4706-4708 at a284420), package theorem
`StratonovichHAMSecondMoment.LowAlphaConvolution.lintegral_rpow_Ioc`
(the radial integral `∫_0^h u^{-α} du` behind `V h^{1-α}/(1-α)`).

Wrong variant: the constant without the factor `1/(1-α)`,
`∫_0^h u^{-α} du = h^{1-α}` for all `0 < α < 1`, `h > 0`.  Counterexample:
`α = 1/2`, `h = 1`, where the integral is `2`, not `1`.
`missing_factor_contrast` is the package identity at the same point.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.LowAlphaConvolution

set_option autoImplicit false

open MeasureTheory Set

namespace Refutations.LowAlphaConvolution

open StratonovichHAMSecondMoment.LowAlphaConvolution

/-- Dropping `1/(1-α)` from the radial integral is false. -/
theorem missing_factor_refuted :
    ¬ (∀ alpha : ℝ, 0 < alpha → alpha < 1 → ∀ h : ℝ, 0 < h →
        ∫⁻ t in Ioc 0 h, ENNReal.ofReal (t ^ (-alpha)) = ENNReal.ofReal (h ^ (1 - alpha))) := by
  intro H
  have h1 := H (1 / 2) (by norm_num) (by norm_num) 1 one_pos
  rw [lintegral_rpow_Ioc (by norm_num) zero_le_one] at h1
  norm_num at h1

/-- The package identity at `α = 1/2`, `h = 1`. -/
theorem missing_factor_contrast :
    ∫⁻ t in Ioc 0 1, ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) =
      ENNReal.ofReal ((1 : ℝ) ^ (1 - (1 / 2 : ℝ)) / (1 - 1 / 2)) :=
  lintegral_rpow_Ioc (by norm_num) zero_le_one

end Refutations.LowAlphaConvolution
