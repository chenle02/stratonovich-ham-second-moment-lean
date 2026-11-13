import StratonovichHAMSecondMoment.WhiteRelativeWidth

/-!
Refutation for `StratonovichHAMSecondMoment.WhiteRelativeWidth.ratio_eq` (and so for
`white_relative_width_paper`), manuscript label `C:white-relative-width`.

Wrong variant: the ratio identity with the hypothesis `c > 0` (TeX line 132) weakened
to the section's `c ≥ 0` (line 4).  Counterexample: `c = 0`, `a = 1/2`.  JUNK-VALUE
RELIANCE: at `c = 0` both formulas are `0` and Lean's `0/0 = 0`, while
`sqrt(K_0 M) > 0`; mathematically the ratio is undefined there, which is why the
corollary assumes `c > 0`.  `drop_positive_c_contrast` is the package identity at
`c = 1`, `a = 1/2`.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open Real

namespace Refutations.WhiteRelativeWidth

open StratonovichHAMSecondMoment.WhiteRelativeWidth

/-- The ratio identity fails at `c = 0`. -/
theorem drop_positive_c_refuted :
    ¬ (∀ c a : ℝ, 0 ≤ c → 0 < a → a < 1 →
        upperFormula c a / lowerFormula c a = sqrt (boundK0 a * boundMass a)) := by
  intro h
  have h1 := h 0 (1 / 2) le_rfl (by norm_num) (by norm_num)
  have hK := boundK0_pos (a := 1 / 2) (by norm_num)
  have hM := boundMass_pos (a := 1 / 2) (by norm_num) (by norm_num)
  have hs : 0 < sqrt (boundK0 (1 / 2) * boundMass (1 / 2)) := sqrt_pos.2 (mul_pos hK hM)
  simp [upperFormula, lowerFormula] at h1
  linarith

/-- Contrast: at `c = 1`, `a = 1/2` the package identity holds. -/
theorem drop_positive_c_contrast :
    upperFormula 1 (1 / 2) / lowerFormula 1 (1 / 2) =
      sqrt (boundK0 (1 / 2) * boundMass (1 / 2)) :=
  ratio_eq one_pos (by norm_num) (by norm_num)

end Refutations.WhiteRelativeWidth
