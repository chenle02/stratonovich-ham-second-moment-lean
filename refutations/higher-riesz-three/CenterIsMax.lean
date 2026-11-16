/-
Refutation for `StratonovichHAMSecondMoment.HigherRieszThree.F3w_unit` read as
"the maximum of `F_3` is its value at the center" (manuscript `L:higher-riesz`,
main TeX lines 6140-6146 at 39f2597a: the maximum is at `|w| = 1`, not at
`w = 0`).

Wrong variant: `F_3(w) ≤ F_3(0) = 1` for every `w`, at `α = 3/2`.
Counterexample: `|w| = 1`, where `F_3(w) = 2^{-1/2}/(1/2) = √2 > 1`.
`center_is_max_contrast` is the package value `F_3(0) = 1`.  No junk-value
reliance (`w ≠ 0`, `2 - α ≠ 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.HigherRieszThree

set_option autoImplicit false

namespace Refutations.HigherRieszThree

open StratonovichHAMSecondMoment.HigherRieszThree

/-- The package value at the center. -/
theorem center_is_max_contrast : F3w (3 / 2) 0 = 1 :=
  F3w_zero _

/-- `F_3 ≤ F_3(0)` is false. -/
theorem center_is_max_refuted : ¬ (∀ w, F3w (3 / 2) w ≤ F3w (3 / 2) 0) := by
  intro h
  obtain ⟨w, hw⟩ := exists_norm_eq (StratonovichHAMSecondMoment.HomogHypothesis.Rd 3)
    (zero_le_one : (0 : ℝ) ≤ 1)
  have h1 := h w
  rw [F3w_zero, F3w_unit (by norm_num) (by norm_num) hw, ← ENNReal.ofReal_one,
    ENNReal.ofReal_le_ofReal_iff zero_le_one] at h1
  have e : (2 : ℝ) ^ (1 - 3 / 2 : ℝ) = (Real.sqrt 2)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by norm_num)]; norm_num
  rw [e, div_le_iff₀ (by norm_num)] at h1
  have hs : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs0 : 0 < Real.sqrt 2 := by positivity
  rw [inv_le_iff_one_le_mul₀ hs0] at h1
  nlinarith

end Refutations.HigherRieszThree
