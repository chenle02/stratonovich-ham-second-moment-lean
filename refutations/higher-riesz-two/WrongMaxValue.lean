/-
Refutation for `StratonovichHAMSecondMoment.HigherRieszTwo.F3_max` (manuscript
`L:higher-riesz`, the value `F_3(e_1) = 2^{1-α}/(2-α)` of the `d = 3` closed
form, main TeX lines 6134-6146 at 39f2597a).

Wrong variant: the value without the factor `1/2` coming from the denominator
`2vρ`, i.e. `F3 (2-α) 1 = 2^{2-α}/(2-α)` for all `1 < α < 2`.
Counterexample: `α = 3/2`, where the true value `2^{-1/2}/(1/2)` is half of
`2^{1/2}/(1/2)`.  `wrong_max_value_contrast` is the package value at
`α = 3/2`.  No junk-value reliance (`2 - α > 0`, `ρ = 1 > 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.HigherRieszTwo

set_option autoImplicit false

namespace Refutations.HigherRieszTwo

open StratonovichHAMSecondMoment.HigherRieszTwo

/-- The package value at `α = 3/2`. -/
theorem wrong_max_value_contrast :
    F3 (2 - 3 / 2) 1 = (2 : ℝ) ^ (1 - 3 / 2 : ℝ) / (2 - 3 / 2) :=
  (F3_max (by norm_num) (by norm_num)).2

/-- The value `2^{2-α}/(2-α)` (missing the factor `1/2`) is false. -/
theorem wrong_max_value_refuted :
    ¬ (∀ α : ℝ, 1 < α → α < 2 → F3 (2 - α) 1 = (2 : ℝ) ^ (2 - α) / (2 - α)) := by
  intro h
  have h1 := h (3 / 2) (by norm_num) (by norm_num)
  rw [wrong_max_value_contrast] at h1
  have e : (2 : ℝ) ^ (2 - 3 / 2 : ℝ) = 2 * 2 ^ (1 - 3 / 2 : ℝ) := by
    rw [show (2 : ℝ) - 3 / 2 = 1 + (1 - 3 / 2) by norm_num, Real.rpow_add (by norm_num),
      Real.rpow_one]
  rw [e] at h1
  have hp : 0 < (2 : ℝ) ^ (1 - 3 / 2 : ℝ) := by positivity
  have h2 : (2 : ℝ) ^ (1 - 3 / 2 : ℝ) = 2 * 2 ^ (1 - 3 / 2 : ℝ) := by
    have hne : (2 : ℝ) - 3 / 2 ≠ 0 := by norm_num
    field_simp at h1
    linarith
  linarith

end Refutations.HigherRieszTwo
