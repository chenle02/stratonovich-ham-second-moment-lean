import StratonovichHAMSecondMoment.WhiteRelativeWidth

/-!
Refutation for `StratonovichHAMSecondMoment.WhiteRelativeWidth.boundK0_mul_boundMass_le`
(and so for `white_relative_width_paper`), manuscript label `C:white-relative-width`.

Wrong variant: the bound with a halved constant,
`K_0(a) M_a ≤ sqrt π / (4 Γ_E(5/4)²)` for all `0 < a < 1`.  Counterexample: `a = 1/2`,
where the package gives `K_0(1/2) M_{1/2} = sqrt π / (2 Γ_E(5/4)²) > 0`, which exceeds
its half.  `halved_width_contrast` is the package identity at the same point.
No junk-value reliance (`Γ_E(5/4) > 0`, `sqrt π > 0`).

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open Real

namespace Refutations.WhiteRelativeWidth

open StratonovichHAMSecondMoment.WhiteRelativeWidth

/-- The relative-width bound with constant `sqrt π / (4 Γ_E(5/4)²)` is false. -/
theorem halved_width_refuted :
    ¬ (∀ a : ℝ, 0 < a → a < 1 →
        boundK0 a * boundMass a ≤ sqrt π / (4 * Gamma (5 / 4) ^ 2)) := by
  intro h
  have h1 := h (1 / 2) (by norm_num) (by norm_num)
  rw [boundK0_mul_boundMass (by norm_num) (by norm_num),
    show (1:ℝ) + 1 / 2 / 2 = 5 / 4 by norm_num, show ((3:ℝ) - 1 / 2) / 2 = 5 / 4 by norm_num] at h1
  have hG := Gamma_pos_of_pos (by norm_num : (0:ℝ) < 5 / 4)
  have hpi : 0 < sqrt π := sqrt_pos.2 pi_pos
  have : sqrt π / (4 * Gamma (5 / 4) ^ 2) < sqrt π / (2 * Gamma (5 / 4) * Gamma (5 / 4)) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hpi (pow_pos hG 2)]
  linarith

/-- Contrast: the package value at `a = 1/2` is `sqrt π / (2 Γ_E(5/4)²)`, exactly
the constant of `C:white-relative-width`. -/
theorem halved_width_contrast :
    boundK0 (1 / 2) * boundMass (1 / 2) = sqrt π / (2 * Gamma (5 / 4) ^ 2) := by
  rw [boundK0_mul_boundMass (by norm_num) (by norm_num),
    show (1:ℝ) + 1 / 2 / 2 = 5 / 4 by norm_num, show ((3:ℝ) - 1 / 2) / 2 = 5 / 4 by norm_num]
  ring

end Refutations.WhiteRelativeWidth
