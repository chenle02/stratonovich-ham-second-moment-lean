import StratonovichHAMSecondMoment.WhiteMomentBounds

/-!
Refutation for the range `c > 0` of `StratonovichHAMSecondMoment.WhiteMomentBounds.
white_moment_bounds_paper` (`T:white-moment-bounds`, `notes/integrated_white_evaluation.tex`,
edf7085f, lines 140-167): the case `c = 0` is out (decision 4 of wave L10).

Wrong variant: "the standing assumption `Γ ≠ 0` of the bracket
(`integrated_occupation_ceiling.tex` lines 20-21) holds for every `c ≥ 0`", which would let
the wrapper be stated for `c ≥ 0`.  Counterexample: `c = 0`, where `c δ₀ = 0`.  No junk-value
reliance (`ENNReal.ofReal 0 = 0` is the genuine value).  `zero_covariance_contrast` is the
package fact `c δ₀ ≠ 0` at `c = 1`.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.WhiteMomentBounds

open StratonovichHAMSecondMoment.WhiteModel StratonovichHAMSecondMoment.WhiteMomentBounds

/-- `c δ₀ ≠ 0` fails at `c = 0`. -/
theorem zero_covariance_refuted : ¬ (∀ c : ℝ, 0 ≤ c → whiteCov c ≠ 0) :=
  fun h => h 0 le_rfl whiteCov_zero

/-- Contrast: `c δ₀ ≠ 0` at `c = 1`. -/
theorem zero_covariance_contrast : whiteCov 1 ≠ 0 := whiteCov_ne_zero one_pos

end Refutations.WhiteMomentBounds
