import StratonovichHAMSecondMoment.WhiteModel

/-!
Refutation for `StratonovichHAMSecondMoment.WhiteModel.F0_white` (part of
`white_score_arithmetic_paper`): `F₀(c²/6) = √c/(3√2)` at `α = 1`
(`notes/integrated_white_evaluation.tex`, edf7085f, lines 157-160).

Wrong variant: `F₀(c²/6) = √c/3` (the factor `1/√2` dropped, i.e. `2^m F₀ = (2/3)√c` read
with `m = 1`).  Counterexample: `c = 1`: `1/(3√2) ≠ 1/3`.  No junk-value reliance.
`F0_constant_contrast` is the package value at `c = 1`.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.WhiteModel

open StratonovichHAMSecondMoment.WhiteModel

/-- `F₀(c²/6) ≠ √c/3` at `c = 1`. -/
theorem F0_constant_refuted :
    ¬ (∀ c : ℝ, 0 < c →
        StratonovichHAMSecondMoment.SpatialFourLinear.F0 1 (c ^ 2 / 6) = Real.sqrt c / 3) := by
  intro h
  have h1 := (h 1 one_pos).symm.trans (F0_white zero_le_one)
  have h2 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [Real.sqrt_one] at h1
  field_simp at h1
  linarith

/-- Contrast: the package value at `c = 1`. -/
theorem F0_constant_contrast :
    StratonovichHAMSecondMoment.SpatialFourLinear.F0 1 (1 ^ 2 / 6) =
      Real.sqrt 1 / (3 * Real.sqrt 2) :=
  F0_white zero_le_one

end Refutations.WhiteModel
