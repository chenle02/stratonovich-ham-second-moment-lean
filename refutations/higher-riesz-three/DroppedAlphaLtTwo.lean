/-
Refutation for `StratonovichHAMSecondMoment.HigherRieszThree.M3_pos` and the
range `α < 2` of `higher_riesz_three` (manuscript `L:higher-riesz`, dimension
three, main TeX lines 6104-6106 at edf7085f): Hypothesis `H:spatial-maximum`
asks for `M > 0`, and `M_3 = c 2^{1-α}/(2-α)` is negative for `α > 2`.

Wrong variant: `0 < M_3(1, α)` for every `α > 1` (`α < 2` dropped).
Counterexample: `α = 3`, `M_3 = 2^{-2}/(-1) < 0`.  `dropped_alpha_lt_two_contrast`
is the package positivity at `α = 3/2`.  No junk-value reliance
(`2 - 3 = -1 ≠ 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.HigherRieszThree

set_option autoImplicit false

namespace Refutations.HigherRieszThree

open StratonovichHAMSecondMoment.HigherRieszThree

/-- The package positivity at `c = 1`, `α = 3/2`. -/
theorem dropped_alpha_lt_two_contrast : 0 < M3 1 (3 / 2) :=
  M3_pos one_pos (by norm_num)

/-- `M_3 > 0` without `α < 2` is false. -/
theorem dropped_alpha_lt_two_refuted : ¬ (∀ α : ℝ, 1 < α → 0 < M3 1 α) := by
  intro h
  have h1 := h 3 (by norm_num)
  have hp : (0 : ℝ) < 2 ^ (1 - 3 : ℝ) := by positivity
  rw [M3] at h1
  have : (2 : ℝ) ^ (1 - 3 : ℝ) / (2 - 3) < 0 := div_neg_of_pos_of_neg hp (by norm_num)
  linarith

end Refutations.HigherRieszThree
