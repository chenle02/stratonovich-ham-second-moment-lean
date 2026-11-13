import StratonovichHAMSecondMoment.WhiteClockLaplace

/-!
Refutation for `StratonovichHAMSecondMoment.WhiteClockLaplace.cross_transform_iterated`
(and so for `white_clock_laplace_paper`), manuscript display
`E:white-cross-clock-transform` of `L:white-clock-laplace`.

Wrong variant: the cross transform with `(θ₁+θ₂)` instead of `(θ₁+θ₂)²` in the
denominator (the first elementary integral `∫ t e^{-ct} dt = c^{-2}` taken as `c^{-1}`).
Counterexample: `a = 1/2`, `θ₁ = θ₂ = 1`; the package value is `Γ_E(1/2)/4`, the
variant gives `Γ_E(1/2)/2`.  `cross_square_contrast` is the package value at the same
point.  No junk-value reliance.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory Set Real

namespace Refutations.WhiteClockLaplace

open StratonovichHAMSecondMoment.WhiteClockLaplace

/-- The cross transform with an unsquared `θ₁+θ₂` is false. -/
theorem cross_square_refuted :
    ¬ (∀ a θ₁ θ₂ : ℝ, 0 < a → a < 1 → 0 < θ₁ → 0 < θ₂ →
        ∫ t in Ioi (0:ℝ), ∫ s in Ioi (0:ℝ), crossIntegrand a θ₁ θ₂ (s, t) =
          Gamma (1 - a) / (2 * (θ₁ + θ₂)) * (θ₁ ^ (a - 1) + θ₂ ^ (a - 1))) := by
  intro h
  have h1 := h (1 / 2) 1 1 (by norm_num) (by norm_num) one_pos one_pos
  rw [(cross_transform_iterated (by norm_num) (by norm_num) one_pos one_pos).2,
    crossValue, one_rpow] at h1
  have hG := Gamma_pos_of_pos (by norm_num : (0:ℝ) < 1 - 1 / 2)
  norm_num at h1
  linarith

/-- Contrast: the package value at `a = 1/2`, `θ₁ = θ₂ = 1`. -/
theorem cross_square_contrast :
    ∫ t in Ioi (0:ℝ), ∫ s in Ioi (0:ℝ), crossIntegrand (1 / 2) 1 1 (s, t) =
      crossValue (1 / 2) 1 1 :=
  (cross_transform_iterated (by norm_num) (by norm_num) one_pos one_pos).2

end Refutations.WhiteClockLaplace
