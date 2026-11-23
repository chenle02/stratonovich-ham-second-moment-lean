import StratonovichHAMSecondMoment.WhiteMomentBounds

/-!
Refutation for the one-sided use of the named input in `StratonovichHAMSecondMoment.
WhiteMomentBounds.white_moment_lower_of_ge` and `white_moment_upper_of_le`
(`T:white-moment-bounds`, `notes/integrated_white_evaluation.tex`, edf7085f, lines 140-167):
the lower bound needs `c²/6 ≤ 𝓔_sp` and the upper bound `𝓔_sp ≤ c²/6`, because `F₀` is
increasing (`WhiteMomentBounds.F0_mono`).

Wrong variant: `F₀` is antitone on `[0,∞)` at `α = 1` (which would let the upper half of the
input carry the lower bound).  Counterexample: `0 ≤ 1/6`, with `F₀(0) = 0 < F₀(1/6) =
1/(3√2)`.  No junk-value reliance (`0^{1/2} = 0` is the genuine value).
`input_direction_contrast` is the package monotonicity on the same pair.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.WhiteMomentBounds

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.WhiteModel

/-- `F₀(1,·)` is not antitone on `[0,∞)`. -/
theorem input_direction_refuted :
    ¬ (∀ z w : ℝ, 0 ≤ z → z ≤ w → SpatialFourLinear.F0 1 w ≤ SpatialFourLinear.F0 1 z) := by
  intro h
  have h1 := h 0 (1 ^ 2 / 6) le_rfl (by norm_num)
  have h0 : SpatialFourLinear.F0 1 0 = 0 := by
    have := F0_white (c := 0) le_rfl
    rw [show (0 : ℝ) ^ 2 / 6 = 0 by norm_num, Real.sqrt_zero, zero_div] at this
    exact this
  rw [F0_white zero_le_one, h0, Real.sqrt_one] at h1
  have : (0 : ℝ) < 1 / (3 * Real.sqrt 2) := by positivity
  linarith

/-- Contrast: `F₀(1,0) ≤ F₀(1,1/6)`. -/
theorem input_direction_contrast :
    SpatialFourLinear.F0 1 0 ≤ SpatialFourLinear.F0 1 (1 ^ 2 / 6) :=
  WhiteMomentBounds.F0_mono (by norm_num) le_rfl (by norm_num)

end Refutations.WhiteMomentBounds
