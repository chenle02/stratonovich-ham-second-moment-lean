/-
Refutation for the log gap of `C:intrinsic-spatial-bracket`, package theorem
`StratonovichHAMSecondMoment.SpatialBracket.logGap_pos`
(`integrated_occupation_ceiling.tex` lines 275-283 at a284420: `Δ > 0` for `a > 0`,
`q - 2a > 0`).

Wrong variant: the hypothesis `a > 0` is dropped (`Δ > 0` whenever `q - 2a > 0`).
Counterexample: `a = 0`, `α = 1`: `Δ = ½[3 log 3 + 3 log 3] - 3 log 3 = 0`.
`log_gap_zero_contrast` is the package bound at `α = 1`, `a = 1/2`.
No junk-value reliance (all logarithms have positive arguments).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpatialBracket

set_option autoImplicit false

open StratonovichHAMSecondMoment.SpatialBracket

namespace Refutations.SpatialBracket

/-- Dropping `a > 0` from `Δ > 0` is false (`Δ = 0` at `a = 0`). -/
theorem log_gap_zero_refuted :
    ¬ (∀ alpha a : ℝ, 0 < 4 - alpha - 2 * a → 0 < logGap alpha a) := by
  intro h
  have h1 := h 1 0 (by norm_num)
  unfold logGap at h1
  norm_num at h1

/-- The package bound at `α = 1`, `a = 1/2`. -/
theorem log_gap_zero_contrast : 0 < logGap 1 (1 / 2) :=
  logGap_pos (by norm_num) (by norm_num)

end Refutations.SpatialBracket
