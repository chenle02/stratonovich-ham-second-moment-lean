import StratonovichHAMSecondMoment.OccupationCeilingFinite

/-!
Refutation for `StratonovichHAMSecondMoment.OccupationCeilingFinite.rpow_add_rpow_le`
(`s^p + (1-s)^p ≤ 2^{1-p}`, the concavity step of the row bound,
`integrated_intrinsic_constant.tex` lines 42-46).

Wrong variant: the bound `1` in place of `2^{1-p}`, with the same binders and hypotheses.
Witness: `p = 0`, `s = 1/2`, where the left side is `2`. No junk value is used (`x^0 = 1`).
The contrast theorem applies the package theorem at the witness.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open Set

namespace Refutations.OccupationCeilingFinite

open StratonovichHAMSecondMoment.OccupationCeilingFinite

/-- Contrast: at `p = 0`, `s = 1/2` the package bound is `2` and is attained. -/
theorem row_constant_contrast :
    (1 / 2 : ℝ) ^ (0 : ℝ) + (1 - 1 / 2) ^ (0 : ℝ) ≤ 2 ^ (1 - 0 : ℝ) ∧
      (1 : ℝ) < (1 / 2 : ℝ) ^ (0 : ℝ) + (1 - 1 / 2) ^ (0 : ℝ) :=
  ⟨rpow_add_rpow_le le_rfl zero_le_one ⟨by norm_num, by norm_num⟩, by simp⟩

/-- The bound `s^p + (1-s)^p ≤ 1` is false. -/
theorem wrong_row_constant :
    ¬ (∀ p s : ℝ, 0 ≤ p → p ≤ 1 → s ∈ Icc (0 : ℝ) 1 → s ^ p + (1 - s) ^ p ≤ 1) := by
  intro h
  have := h 0 (1 / 2) le_rfl zero_le_one ⟨by norm_num, by norm_num⟩
  linarith [row_constant_contrast.2]

end Refutations.OccupationCeilingFinite
