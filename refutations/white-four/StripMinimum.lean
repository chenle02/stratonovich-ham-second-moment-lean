/-
Refutation for the row `(0,4), B` of `E:white-four-table` (main TeX lines
4956-4959 and 4996-4998 at edf7085f: "`(x,y,x,y)` ... areas are `4ac`,
`4a min(b,c,d)` and `4a min(b,d)`"), package theorem
`StratonovichHAMSecondMoment.WhiteFour.whiteSpatial_04B`.

Wrong variant: `V = ab/4` (only the first closing indicator `|y-x| < b` kept;
the identified positions make the indicators of labels 3 and 4 constrain the
same difference).  Counterexample: `h = (a,b,c,d) = (1,2,1,1)`: the true
factor is `a min(b,c,d)/4 = 1/4`, the variant gives `1/2`.
`stripMinimum_contrast` is the package value.
Class (a): manuscript-claim perturbation in the manuscript domain.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.WhiteFour

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment WhiteCollapse WhiteFour

namespace Refutations.WhiteFour

/-- The increments `(1,2,1,1)`. -/
def hSM : Fin 4 → ℝ := ![1, 2, 1, 1]

theorem hSM_pos : ∀ i, 0 < hSM i := by
  intro i; fin_cases i <;> norm_num [hSM]

/-- The package: the collapsed factor is `1/4`. -/
theorem stripMinimum_contrast : whiteSpatial 0 pB hSM = ENNReal.ofReal (1 / 4) := by
  rw [whiteSpatial_04B hSM_pos]
  congr 1
  norm_num [hSM]

/-- Keeping only the indicator of label 2 gives the wrong factor. -/
theorem stripMinimum_refuted :
    ¬ (whiteSpatial 0 pB hSM = ENNReal.ofReal (hSM 0 * hSM 1 / 4)) := by
  rw [stripMinimum_contrast, ENNReal.ofReal_eq_ofReal_iff (by norm_num)
    (by norm_num [hSM])]
  norm_num [hSM]

end Refutations.WhiteFour
