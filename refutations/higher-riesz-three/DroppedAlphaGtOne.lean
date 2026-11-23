/-
Refutation for `StratonovichHAMSecondMoment.HigherRieszThree.F3w_le` (manuscript
`L:higher-riesz`, dimension three, main TeX lines 6104-6106 and 6140-6146 at
edf7085f): the uniform bound `F_3 ≤ 2^{1-α}/(2-α)` needs `α > 1`.

Wrong variant: `F_3(w) ≤ 2^{1-α}/(2-α)` for every `0 < α < 2` and every `w`
(`1 < α` dropped).  Counterexample: `α = 1/2`, `w = 0`, where `F_3(0) = 1`
(`F3w_zero`) but `2^{1/2}/(3/2) < 1`.  `dropped_alpha_gt_one_contrast` is the
package bound at `α = 3/2`.  No junk-value reliance (`2 - α = 3/2 ≠ 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.HigherRieszThree

set_option autoImplicit false

namespace Refutations.HigherRieszThree

open StratonovichHAMSecondMoment.HigherRieszThree

/-- The package bound at `α = 3/2`, `w = 0`. -/
theorem dropped_alpha_gt_one_contrast :
    F3w (3 / 2) 0 ≤ ENNReal.ofReal ((2 : ℝ) ^ (1 - 3 / 2 : ℝ) / (2 - 3 / 2)) :=
  F3w_le (by norm_num) (by norm_num) 0

/-- The bound without `1 < α` is false. -/
theorem dropped_alpha_gt_one_refuted :
    ¬ (∀ α : ℝ, 0 < α → α < 2 → ∀ w,
      F3w α w ≤ ENNReal.ofReal ((2 : ℝ) ^ (1 - α) / (2 - α))) := by
  intro h
  have h1 := h (1 / 2) (by norm_num) (by norm_num) 0
  rw [F3w_zero, ← ENNReal.ofReal_one,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  have e : (2 : ℝ) ^ (1 - 1 / 2 : ℝ) = Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow]; norm_num
  rw [e, le_div_iff₀ (by norm_num)] at h1
  have hs : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

end Refutations.HigherRieszThree
