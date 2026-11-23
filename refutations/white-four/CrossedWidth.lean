/-
Refutation for the row `(2,2), C` of `E:white-four-table` (main TeX lines
4966-4967 and 5000-5001 at edf7085f: "`(x,y),(y,x)` for `C` ... `F(a,c,min(b,d))`"),
package theorem `StratonovichHAMSecondMoment.WhiteFour.whiteSpatial_22C`.

Wrong variant: the strip width `b + d` (adding the two closing widths) in
place of `min(b,d)`.  Counterexample: `h = (1,1,1,1)`: `F(1,1,1)/16 = 3/16`, the
variant gives `F(1,1,2)/16 = 4/16`.  `crossedWidth_contrast` is the package value.
Class (a): manuscript-claim perturbation in the manuscript domain.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.WhiteFour

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment WhiteCollapse WhiteFour

namespace Refutations.WhiteFour

/-- The unit increments. -/
def hCW : Fin 4 → ℝ := fun _ => 1

/-- The package: the collapsed factor is `F(1,1,1)/16 = 3/16`. -/
theorem crossedWidth_contrast : whiteSpatial 2 pC hCW = ENNReal.ofReal (3 / 16) := by
  rw [whiteSpatial_22C (h := hCW) fun _ => one_pos]
  congr 1
  simp only [hCW, F, min_self, sub_self, abs_zero]
  norm_num

/-- The added width `b + d` gives the wrong factor. -/
theorem crossedWidth_refuted :
    ¬ (whiteSpatial 2 pC hCW = ENNReal.ofReal (F (hCW 0) (hCW 2) (hCW 1 + hCW 3) / 16)) := by
  rw [crossedWidth_contrast, ENNReal.ofReal_eq_ofReal_iff (by norm_num)
    (by simp only [hCW, F]; norm_num)]
  simp only [hCW, F, sub_self, abs_zero]
  norm_num

end Refutations.WhiteFour
