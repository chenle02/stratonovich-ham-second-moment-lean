/-
Refutation for the bound `𝒬_h ≤ 2` used in `P:frequency-row` (TeX lines 86-87:
"Both bracket powers in `𝒬_h` are at most one, since `a - 1 < 0`"), package
theorem `StratonovichHAMSecondMoment.FrequencyRow.frequencyPair_le_two` and
package definition `StratonovichHAMSecondMoment.MaskedTrigProducts.frequencyPair`.

Wrong variant: the hypothesis `a < 1` dropped. At `a = 3`, `h = 1`, `r = 1`,
`ρ = 0` each bracket power is `⟨1⟩^2 = 2`, so `𝒬_1(1,0) = 4 > 2`. No junk value
is involved (`⟨1⟩ = √2 > 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.FrequencyRow

set_option autoImplicit false

open StratonovichHAMSecondMoment.MaskedTrigProducts (bracket frequencyPair)

namespace Refutations.FrequencyRow

theorem pair_at_three : frequencyPair 3 1 1 0 = 4 := by
  have hb : bracket 1 ^ ((3 : ℝ) - 1) = 2 := by
    rw [show (3 : ℝ) - 1 = (2 : ℕ) by norm_num, Real.rpow_natCast]
    unfold bracket
    rw [Real.sq_sqrt (by norm_num)]; norm_num
  unfold frequencyPair
  simp only [mul_one, sub_zero, add_zero]
  rw [hb]; norm_num

/-- Dropping `a < 1` from `frequencyPair_le_two` is false. -/
theorem pair_le_two_without_a_lt_one :
    ¬ ∀ a h r ρ : ℝ, frequencyPair a h r ρ ≤ 2 := by
  intro H
  have := H 3 1 1 0
  rw [pair_at_three] at this
  norm_num at this

/-- The package theorem at an admissible `a`. -/
theorem pair_le_two_contrast : frequencyPair (1 / 2) 1 1 0 ≤ 2 :=
  StratonovichHAMSecondMoment.FrequencyRow.frequencyPair_le_two (by norm_num) 1 1 0

end Refutations.FrequencyRow
