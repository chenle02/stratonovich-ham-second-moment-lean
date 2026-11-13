import StratonovichHAMSecondMoment.WhiteClockLaplace

/-!
Refutation for `StratonovichHAMSecondMoment.WhiteClockLaplace.self_transform` (and so for
`white_clock_laplace_paper`), manuscript display `E:white-self-clock-transform` of
`L:white-clock-laplace`.

Wrong variant: the self transform with the exponent sign of `η₂` flipped,
`Γ_E(1-a)/(2 η₁² η₂^{a-1})` instead of `Γ_E(1-a)/(2 η₁² η₂^{1-a})`.
Counterexample: `a = 1/2`, `η₁ = 1`, `η₂ = 4`, where `4^{1/2} ≠ 4^{-1/2}` and
`Γ_E(1/2) > 0`.  `self_exponent_sign_contrast` is the package value at the same
point.  No junk-value reliance (all parameters in the lemma's range).

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory Set Real

namespace Refutations.WhiteClockLaplace

open StratonovichHAMSecondMoment.WhiteClockLaplace

/-- The self transform with `η₂^{a-1}` in the denominator is false. -/
theorem self_exponent_sign_refuted :
    ¬ (∀ a η₁ η₂ : ℝ, 0 < a → a < 1 → 0 < η₁ → 0 < η₂ →
        ∫ r₂ in Ioi (0:ℝ), ∫ r₁ in Ioi (0:ℝ), selfIntegrand a η₁ η₂ (r₁, r₂) =
          Gamma (1 - a) / (2 * η₁ ^ 2 * η₂ ^ (a - 1))) := by
  intro h
  have h1 := h (1 / 2) 1 4 (by norm_num) (by norm_num) one_pos (by norm_num)
  rw [(self_transform (by norm_num) one_pos (by norm_num)).2.2, selfValue] at h1
  have hG := Gamma_pos_of_pos (by norm_num : (0:ℝ) < 1 - 1 / 2)
  have hb : 0 < (4:ℝ) ^ (1 - 1 / 2 : ℝ) := rpow_pos_of_pos (by norm_num) _
  have hc : 0 < (4:ℝ) ^ (1 / 2 - 1 : ℝ) := rpow_pos_of_pos (by norm_num) _
  have hlt : (4:ℝ) ^ (1 / 2 - 1 : ℝ) < (4:ℝ) ^ (1 - 1 / 2 : ℝ) :=
    rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  rw [div_eq_div_iff (by positivity) (by positivity)] at h1
  have := mul_left_cancel₀ hG.ne' h1
  nlinarith

/-- Contrast: the package value at `a = 1/2`, `η₁ = 1`, `η₂ = 4`. -/
theorem self_exponent_sign_contrast :
    ∫ r₂ in Ioi (0:ℝ), ∫ r₁ in Ioi (0:ℝ), selfIntegrand (1 / 2) 1 4 (r₁, r₂) =
      Gamma (1 - 1 / 2) / (2 * 1 ^ 2 * (4:ℝ) ^ (1 - 1 / 2 : ℝ)) :=
  (self_transform (by norm_num) one_pos (by norm_num)).2.2

end Refutations.WhiteClockLaplace
