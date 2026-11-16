import StratonovichHAMSecondMoment.WhiteMomentBounds

/-!
Refutation for the closed forms of `StratonovichHAMSecondMoment.WhiteMomentBounds.
white_moment_bounds_paper` (`E:white-moment-bounds`, `notes/integrated_white_evaluation.tex`,
39f2597a, lines 143-144, 159-161): the bounds scale as `√c`, because `𝓔_sp = c²/6` enters `F₀`
through `(2𝓔_sp)^{1/4}`.

Wrong variant: the upper formula is linear in the covariance mass,
`(2/3)√(c K₀) = (2/3) c √K₀` for every `c > 0` (reading `c` as the noise coefficient
`√c`, which line 6 warns against).  Counterexample: `c = 4`, `a = 1/2`: `2√K₀ ≠ 4√K₀` since
`K₀ > 0`.  No junk-value reliance.  `linear_in_c_contrast` is the package identity
`(2/3)√(c K₀) = (2/3)√c √K₀` at `c = 4`.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.WhiteMomentBounds

open StratonovichHAMSecondMoment.WhiteRelativeWidth

/-- The upper formula is not `(2/3) c √K₀` (at `c = 4`, `a = 1/2`). -/
theorem linear_in_c_refuted :
    ¬ (∀ c a : ℝ, 0 < c → 0 < a → a < 1 →
        upperFormula c a = 2 / 3 * c * Real.sqrt (boundK0 a)) := by
  intro h
  have h1 := h 4 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have hK := Real.sqrt_pos.2 (boundK0_pos (a := 1 / 2) (by norm_num))
  rw [upperFormula, Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)] at h1
  nlinarith

/-- Contrast: `(2/3)√(4 K₀) = (2/3) · 2 · √K₀`. -/
theorem linear_in_c_contrast :
    upperFormula 4 (1 / 2) = 2 / 3 * 2 * Real.sqrt (boundK0 (1 / 2)) := by
  rw [upperFormula, Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  ring

end Refutations.WhiteMomentBounds
