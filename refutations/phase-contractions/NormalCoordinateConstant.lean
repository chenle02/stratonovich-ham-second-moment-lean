/-
Refutation for the one-dimensional integral behind the sphere convolution
formula of `L:phase-contractions` (main TeX lines 2125-2131 at a284420),
package theorem
`StratonovichHAMSecondMoment.PhaseContractions.integral_normal_coordinate`.

Wrong variant: the denominator `ar(2-α)` replaced by `2ar(2-α)` (the factor
`1/2` of the sphere formula moved into the one-dimensional integral), i.e.
`∫_{-1}^{1} (r² + a² - 2art)^{-α/2} dt = ((a+r)^{2-α} - |a-r|^{2-α})/(2ar(2-α))`.
Counterexample: `a = r = α = 1`: the integral is `2` (package theorem), the
variant gives `1`.  `normal_coordinate_constant_contrast` is the package
theorem at the same point.  No junk-value reliance (`|a - r|^{1} = 0`
is a genuine value).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.PhaseContractions

set_option autoImplicit false

open Real
open StratonovichHAMSecondMoment PhaseContractions

namespace Refutations.PhaseContractions

/-- The normal-coordinate integral with an extra factor `1/2` is false. -/
theorem normal_coordinate_constant_refuted :
    ¬ (∀ a r alpha : ℝ, 0 < a → 0 < r → alpha < 2 →
        ∫ t in (-1 : ℝ)..1, (r ^ 2 + a ^ 2 - 2 * a * r * t) ^ (-alpha / 2) =
          ((a + r) ^ (2 - alpha) - |a - r| ^ (2 - alpha)) / (2 * a * r * (2 - alpha))) := by
  intro h
  have h1 := h 1 1 1 one_pos one_pos (by norm_num)
  rw [(integral_normal_coordinate 1 1 1 one_pos one_pos (by norm_num)).2] at h1
  norm_num at h1

/-- The package value at the same point: `((1+1)^1 - 0^1)/(1·1·1) = 2`. -/
theorem normal_coordinate_constant_contrast :
    ∫ t in (-1 : ℝ)..1, ((1 : ℝ) ^ 2 + 1 ^ 2 - 2 * 1 * 1 * t) ^ (-(1 : ℝ) / 2) = 2 := by
  rw [(integral_normal_coordinate 1 1 1 one_pos one_pos (by norm_num)).2]
  norm_num

end Refutations.PhaseContractions
