import StratonovichHAMSecondMoment.WhiteModel

/-!
Refutation for `StratonovichHAMSecondMoment.WhiteModel.white_homogCovariance` (part (a) of
`white_model_paper`): white noise satisfies `H:homog` only with `α = d = 1`
(main TeX lines 395-400; `notes/integrated_white_evaluation.tex`, 39f2597a, line 4).

Wrong variant: the white model with scaling exponent `α = 1/2` (an exponent in the open
range `0 < α < d`).  Counterexample: `c = 1`, `a = 1/4`, `A = {0}`, scale `2`:
`Γ(2·{0}) = Γ{0} = 1` but `2^{d-α} Γ{0} = √2`.  No junk-value reliance.
`scaling_exponent_contrast` is the package statement at `α = 1`.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory
open scoped Pointwise

namespace Refutations.WhiteModel

open StratonovichHAMSecondMoment.HomogHypothesis StratonovichHAMSecondMoment.WhiteModel

/-- The white model does not satisfy `H:homog` with `α = 1/2`. -/
theorem scaling_exponent_refuted :
    ¬ HomogCovariance 1 (1 / 2) (1 / 4) (whiteCov 1) (whiteSpectral 1) := by
  intro h
  have hs := h.scaling {0} (measurableSet_singleton 0) 2 two_pos
  rw [Set.smul_set_singleton, smul_zero] at hs
  have h0 : whiteCov 1 {0} = 1 := by
    rw [whiteCov, Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton 0)]
    simp
  rw [h0, mul_one] at hs
  have hgt : (1 : ℝ) < (2 : ℝ) ^ (((1 : ℕ) : ℝ) - 1 / 2) :=
    Real.one_lt_rpow (by norm_num) (by norm_num)
  have := congrArg ENNReal.toReal hs
  rw [ENNReal.toReal_ofReal (by positivity)] at this
  simp at this
  linarith

/-- Contrast: the package statement with `α = 1` at `c = 1`, `a = 1/4`. -/
theorem scaling_exponent_contrast :
    HomogCovariance 1 1 (1 / 4) (whiteCov 1) (whiteSpectral 1) :=
  white_homogCovariance zero_le_one (by norm_num) (by norm_num)

end Refutations.WhiteModel
