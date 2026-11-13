import StratonovichHAMSecondMoment.OccupationCeilingFinite

/-!
Refutation for `StratonovichHAMSecondMoment.OccupationCeilingFinite.K0` and the sharp row
bound `row_le` (`K_0 = 2^a/(1-a)`, `E:positive-bochner-inclusion`,
`integrated_intrinsic_constant.tex` line 29).

Wrong variant: the row constant `1/(1-a)` (the factor `2^a` dropped), i.e. `K_0 ≤ 1/(1-a)`
for all `0 ≤ a < 1`. Witness: `a = 1/2`, where `K_0 = 2√2 > 2 = 1/(1-a)`. No junk value is used.
The contrast theorem evaluates the package constant at the witness.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.OccupationCeilingFinite

open StratonovichHAMSecondMoment.OccupationCeilingFinite

/-- Contrast: `K_0(1/2) > 2`. -/
theorem wrong_K0_contrast : (2 : ℝ) < K0 (1 / 2) := by
  unfold K0
  have h : (1 : ℝ) < 2 ^ (1 / 2 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  rw [lt_div_iff₀ (by norm_num)]
  linarith

/-- The row constant `1/(1-a)` is false. -/
theorem wrong_K0 : ¬ (∀ a : ℝ, 0 ≤ a → a < 1 → K0 a ≤ 1 / (1 - a)) := by
  intro h
  have := h (1 / 2) (by norm_num) (by norm_num)
  have hc := wrong_K0_contrast
  norm_num at this
  linarith

end Refutations.OccupationCeilingFinite
