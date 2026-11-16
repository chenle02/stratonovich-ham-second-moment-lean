/-
Refutation for `E:interval-area` (main TeX lines 4923-4935 at 39f2597a: "`F(a,b,c)
= 4ab-(a+b-c)_+^2+(|a-b|-c)_+^2`.  This is the area of `{|x|<a, |y|<b,
|x-y|<c}`"), package definitions `StratonovichHAMSecondMoment.WhiteFour.tri`,
`F`, theorem `volume_tri`.

Wrong variant: the area without the correction term `(|a-b|-c)_+^2`, i.e. only
one right triangle removed per side (the case `c ≥ |a-b|` of line 4931 applied
when `c < |a-b|`).  Counterexample: `a = 3`, `b = c = 1`: the true area is
`F = 12 - 9 + 1 = 4` (a strip of width `2c` across the `2b` rectangle), the
variant gives `3`.  `areaCorrection_contrast` is the package value.
Class (a): manuscript-claim perturbation in the manuscript domain.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.WhiteFour

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment WhiteFour

namespace Refutations.WhiteFour

/-- The area formula without the correction term. -/
noncomputable def Fwrong (a b c : ℝ) : ℝ := 4 * a * b - max (a + b - c) 0 ^ 2

/-- The package: the area is `F(3,1,1) = 4`. -/
theorem areaCorrection_contrast : volume (tri 3 1 1) = ENNReal.ofReal 4 := by
  rw [volume_tri (by norm_num) (by norm_num) (by norm_num)]
  congr 1
  simp only [F]
  norm_num [abs_of_pos]

/-- The uncorrected formula is not the area. -/
theorem areaCorrection_refuted : ¬ (volume (tri 3 1 1) = ENNReal.ofReal (Fwrong 3 1 1)) := by
  rw [areaCorrection_contrast, Fwrong, ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)]
  norm_num

end Refutations.WhiteFour
