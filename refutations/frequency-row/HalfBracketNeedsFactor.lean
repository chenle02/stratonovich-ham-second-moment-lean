/-
Refutation for the far-region bracket bound of `P:frequency-row` (TeX line 107:
"Each oscillatory bracket is at least `⟨hr⟩/2`"), package theorem
`StratonovichHAMSecondMoment.FrequencyRow.bracket_rpow_le_half`.

Wrong variant: the factor `2^{1-a}` dropped, i.e. `|x| ≥ t/2` implies
`⟨x⟩^{a-1} ≤ ⟨t⟩^{a-1}`. At `a = 0`, `x = 1`, `t = 2`: `⟨1⟩^{-1} = 1/√2 > 1/√5 = ⟨2⟩^{-1}`.
No junk value is involved (both brackets are positive).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.FrequencyRow

set_option autoImplicit false

open StratonovichHAMSecondMoment.MaskedTrigProducts (bracket)

namespace Refutations.FrequencyRow

theorem bracket_one_inv_gt : bracket 2 ^ ((0 : ℝ) - 1) < bracket 1 ^ ((0 : ℝ) - 1) := by
  have h1 : (0 : ℝ) < bracket 1 := StratonovichHAMSecondMoment.FrequencyRow.bracket_pos 1
  have hlt : bracket 1 < bracket 2 := by
    unfold bracket; apply Real.sqrt_lt_sqrt (by positivity); norm_num
  exact Real.rpow_lt_rpow_of_neg h1 hlt (by norm_num)

/-- Without the factor `2^{1-a}` the half-bracket bound is false. -/
theorem half_bracket_without_factor :
    ¬ ∀ a x t : ℝ, a < 1 → 0 ≤ t → t / 2 ≤ |x| → bracket x ^ (a - 1) ≤ bracket t ^ (a - 1) := by
  intro H
  have := H 0 1 2 (by norm_num) (by norm_num) (by norm_num)
  exact absurd this (not_le.mpr bracket_one_inv_gt)

/-- The package theorem at the same point. -/
theorem half_bracket_contrast :
    bracket 1 ^ ((0 : ℝ) - 1) ≤ (2 : ℝ) ^ ((1 : ℝ) - 0) * bracket 2 ^ ((0 : ℝ) - 1) :=
  StratonovichHAMSecondMoment.FrequencyRow.bracket_rpow_le_half (by norm_num) (by norm_num)
    (by norm_num)

end Refutations.FrequencyRow
