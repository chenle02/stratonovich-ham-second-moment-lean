import StratonovichHAMSecondMoment.TimeFractional

/-!
Refutation for `StratonovichHAMSecondMoment.TimeFractional.twoTimeR_integral`
(the real two-time Laplace lemma behind the cone integration in the proof of
`P:clock-copy-obstruction`, main TeX lines 7784-7800):
`∫∫_{(0,∞)²} e^{-c(s+t)-λ|s-t|} ds dt = 1/(c(c+λ))`.

Wrong variant: the value `1/(2c(c+λ))` (only one of the two cones `s < t`,
`t < s` counted), with the same binders and hypotheses. Witness: `c = 1`,
`λ = 0`, where the package value is `1` and the wrong value `1/2`. No junk
value is used (the package states integrability).
The contrast theorem applies the package theorem at the witness.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory

namespace Refutations.TimeFractional

open StratonovichHAMSecondMoment.TimeFractional

/-- Contrast: at `c = 1`, `λ = 0` the two-time integral exceeds the one-cone
value `1/2`. -/
theorem one_cone_contrast : (1 : ℝ) / 2 < ∫ p, twoTimeR 1 0 p ∂P2 := by
  rw [(twoTimeR_integral 1 0 one_pos le_rfl).2]
  norm_num

/-- The one-cone value `1/(2c(c+λ))` is false. -/
theorem one_cone_only :
    ¬ (∀ c lam : ℝ, 0 < c → 0 ≤ lam →
      ∫ p, twoTimeR c lam p ∂P2 = 1 / (2 * c * (c + lam))) := by
  intro h
  have := h 1 0 one_pos le_rfl
  have hc := one_cone_contrast
  rw [this] at hc
  norm_num at hc

end Refutations.TimeFractional
