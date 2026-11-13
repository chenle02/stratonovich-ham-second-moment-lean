/-
Refutation for the middle region of the three-region bound of
`L:phase-contractions` (main TeX lines 2134-2135 at a284420), package theorem
`StratonovichHAMSecondMoment.PhaseContractions.middle_region_le`.

Wrong variant: the power `a^{1-α}` replaced by `a^{2-α}`, i.e. for
`a/2 ≤ r ≤ 2a`,
`((a+r)^{2-α} - |a-r|^{2-α})/(2r(2-α)) ≤ 3^{2-α} a^{2-α}/(2-α)`.
Counterexample: `a = r = 1/4`, `α = 1`: the left side is
`(1/2 - 0)/(1/2) = 1`, the variant's right side `3/4`.
`middle_region_exponent_contrast` is the package bound at the same point
(`1 ≤ 3 (1/4)^0 = 3`).  No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.PhaseContractions

set_option autoImplicit false

open Real
open StratonovichHAMSecondMoment PhaseContractions

namespace Refutations.PhaseContractions

/-- The middle-region bound with `a^{2-α}` is false. -/
theorem middle_region_exponent_refuted :
    ¬ (∀ a r alpha : ℝ, 0 < a → alpha < 2 → a / 2 ≤ r → r ≤ 2 * a →
        ((a + r) ^ (2 - alpha) - |a - r| ^ (2 - alpha)) / (2 * r * (2 - alpha)) ≤
          3 ^ (2 - alpha) * a ^ (2 - alpha) / (2 - alpha)) := by
  intro h
  have h1 := h (1 / 4) (1 / 4) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h1

/-- The package bound at the same point. -/
theorem middle_region_exponent_contrast :
    (((1 / 4 : ℝ) + 1 / 4) ^ (2 - (1 : ℝ)) - |(1 / 4 : ℝ) - 1 / 4| ^ (2 - (1 : ℝ))) /
        (2 * (1 / 4) * (2 - 1)) ≤
      3 ^ (2 - (1 : ℝ)) * (1 / 4 : ℝ) ^ (1 - (1 : ℝ)) / (2 - 1) :=
  middle_region_le (1 / 4) (1 / 4) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Refutations.PhaseContractions
