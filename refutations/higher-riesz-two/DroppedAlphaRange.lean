/-
Refutation for `StratonovichHAMSecondMoment.HigherRieszTwo.M2_pos` and hence
for the range `α < 3/2` in `higher_riesz_two` (manuscript `L:higher-riesz`,
dimension two, main TeX lines 6106-6111 at edf7085f): Hypothesis
`H:spatial-maximum` asks for `M > 0`, and the displayed `M_2` is not positive
outside the stated range.

Wrong variant: `0 < M_2(1, α)` for every `α > 0` (the range `α < 3/2`
dropped).  Counterexample: `α = 2`, where
`M_2 = 4^2 + (4/(-1/2)) 4^{1/2} = 16 - 16 = 0`.  `dropped_alpha_range_contrast`
is the package positivity at `α = 1`.  No junk-value reliance
(`3/2 - α = -1/2 ≠ 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.HigherRieszTwo

set_option autoImplicit false

namespace Refutations.HigherRieszTwo

open StratonovichHAMSecondMoment.HigherRieszTwo

/-- The package positivity at `c = 1`, `α = 1`. -/
theorem dropped_alpha_range_contrast : 0 < M2 1 1 :=
  M2_pos one_pos one_pos (by norm_num)

/-- `M_2 > 0` without `α < 3/2` is false. -/
theorem dropped_alpha_range_refuted : ¬ (∀ α : ℝ, 0 < α → 0 < M2 1 α) := by
  intro h
  have h1 := h 2 (by norm_num)
  have e1 : (4 : ℝ) ^ (2 : ℝ) = 16 := by norm_num
  have e2 : (4 : ℝ) ^ ((2 : ℝ) - 3 / 2) = 2 := by
    rw [show (2 : ℝ) - 3 / 2 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [M2, e1, e2] at h1
  norm_num at h1

end Refutations.HigherRieszTwo
