import StratonovichHAMSecondMoment.WhiteModel

/-!
Refutation for `StratonovichHAMSecondMoment.WhiteModel.whiteSpectral_closedBall` (part (b) of
`white_model_paper`): `V = μ{|ξ| ≤ 1} = c/π` for the white model
(`notes/integrated_white_evaluation.tex`, 39f2597a, lines 4-9; `V` as at main TeX line 5559).

Wrong variant: `V = c/(2π)`, the spectral density alone, forgetting that the unit ball of
`ℝ¹` has length `2`.  Counterexample: `c = 1`.  No junk-value reliance (`1/π ≠ 1/(2π)`,
both positive).  `ball_length_contrast` is the package value at `c = 1`.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory Metric

namespace Refutations.WhiteModel

open StratonovichHAMSecondMoment.HomogHypothesis StratonovichHAMSecondMoment.WhiteModel

/-- `V ≠ c/(2π)` at `c = 1`. -/
theorem ball_length_refuted :
    ¬ (∀ c : ℝ, 0 ≤ c →
        whiteSpectral c (closedBall 0 1) = ENNReal.ofReal (c / (2 * Real.pi))) := by
  intro h
  have h1 := (h 1 zero_le_one).symm.trans (whiteSpectral_closedBall zero_le_one)
  rw [ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at h1
  have hp := Real.pi_pos
  field_simp at h1
  linarith

/-- Contrast: the package value `V = 1/π` at `c = 1`. -/
theorem ball_length_contrast :
    whiteSpectral 1 (closedBall 0 1) = ENNReal.ofReal (1 / Real.pi) :=
  whiteSpectral_closedBall zero_le_one

end Refutations.WhiteModel
