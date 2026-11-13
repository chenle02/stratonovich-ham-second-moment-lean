import StratonovichHAMSecondMoment.OccupationCeilingFinite

/-!
Refutation for `StratonovichHAMSecondMoment.OccupationCeilingFinite.young_quarter`
(`√X T^{α/4} - T ≤ (q/4)(α/4)^{α/q} X^{2/q}`, the first scalar maximum of the proof of
`T:intrinsic-occupation-ceiling`, `integrated_occupation_ceiling.tex` lines 224-231).

Wrong variant: the maximum `0` (the gradient budget `T` alone controls the occupation term),
with the same binders and hypotheses. Witness: `α = 1`, `X = 4`, `T = 1`, where the left side
is `1`. No junk value is used. The contrast theorem applies the package theorem there.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.OccupationCeilingFinite

open StratonovichHAMSecondMoment.OccupationCeilingFinite

/-- Contrast: at `α = 1`, `X = 4`, `T = 1` the left side is `1`, and the package bound holds. -/
theorem zero_quarter_contrast :
    Real.sqrt 4 * (1 : ℝ) ^ ((1 : ℝ) / 4) - 1 = 1 ∧
      Real.sqrt 4 * (1 : ℝ) ^ ((1 : ℝ) / 4) - 1 ≤
        (4 - 1) / 4 * (1 / 4 : ℝ) ^ ((1 : ℝ) / (4 - 1)) * (4 : ℝ) ^ (2 / (4 - 1 : ℝ)) := by
  refine ⟨?_, young_quarter one_pos (by norm_num) (by norm_num) zero_le_one⟩
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num), Real.one_rpow]
  norm_num

/-- The maximum `0` is false. -/
theorem zero_quarter_max :
    ¬ (∀ alpha X T : ℝ, 0 < alpha → alpha < 4 → 0 ≤ X → 0 ≤ T →
      Real.sqrt X * T ^ (alpha / 4) - T ≤ 0) := by
  intro h
  have := h 1 4 1 one_pos (by norm_num) (by norm_num) zero_le_one
  linarith [zero_quarter_contrast.1]

end Refutations.OccupationCeilingFinite
