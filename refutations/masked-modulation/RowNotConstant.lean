/-
Refutation for the row integral behind `E:masked-time-schur` (TeX lines
171-172), package theorem
`StratonovichHAMSecondMoment.TimeSchur.integral_row`.

Wrong variant: the row integral `∫_0^T |t-s|^{-a} ds` is identically equal to
its bound `2T^{1-a}/(1-a)` (the Schur bound attained in every row). Witness
`a = 1/2`, `T = 1`, `t = 0`: the row integral is `(0 + 1)/(1/2) = 2`, the
variant claims `4`. No junk value is involved (the integrand is integrable,
`integral_row`). The contrast theorem is `integral_row` at the same point.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TimeSchur

set_option autoImplicit false

namespace Refutations.TimeSchur

open MeasureTheory Set StratonovichHAMSecondMoment.TimeSchur

/-- The row integral is not constantly equal to the Schur bound. -/
theorem row_not_constant :
    ¬ ∀ a T t : ℝ, 0 < a → a < 1 → t ∈ Icc 0 T →
      ∫ s in Icc 0 T, kern a (t - s) = 2 * T ^ (1 - a) / (1 - a) := by
  intro h
  have h1 := h (1 / 2) 1 0 (by norm_num) (by norm_num) ⟨le_rfl, zero_le_one⟩
  rw [(integral_row (a := 1 / 2) (T := 1) (t := 0) (by norm_num)
    ⟨le_rfl, zero_le_one⟩).2] at h1
  norm_num at h1

/-- Contrast: the package's exact row integral at the counterexample point. -/
theorem row_not_constant_contrast :
    IntegrableOn (fun s => kern (1 / 2) (0 - s)) (Icc 0 1) ∧
      ∫ s in Icc (0 : ℝ) 1, kern (1 / 2) (0 - s) =
        ((0 : ℝ) ^ (1 - (1 / 2 : ℝ)) + (1 - 0) ^ (1 - (1 / 2 : ℝ))) / (1 - 1 / 2) :=
  integral_row (by norm_num) ⟨le_rfl, zero_le_one⟩

end Refutations.TimeSchur
