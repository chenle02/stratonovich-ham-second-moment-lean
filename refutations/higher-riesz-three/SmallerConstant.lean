/-
Refutation for `StratonovichHAMSecondMoment.HigherRieszThree.higher_riesz_three`
read as "some smaller constant also works" (manuscript `L:higher-riesz`, main TeX
lines 6105-6106 and 6186-6189 at 39f2597a: `M_3` is the OPTIMAL uniform
constant).

Wrong variant: Hypothesis `H:spatial-maximum` in `d = 3` for `γ = |x|^{-3/2}`
with the halved constant `M_3/2`.  Refuted by `higher_riesz_three_optimal`
(Fatou), since `M_3 > 0`.  `smaller_constant_contrast` is the package bound
with `M_3` itself.  No junk-value reliance (`2 - 3/2 ≠ 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.HigherRieszThree

set_option autoImplicit false

namespace Refutations.HigherRieszThree

open StratonovichHAMSecondMoment.HigherRieszTwo StratonovichHAMSecondMoment.HigherRieszThree

/-- The package bound with `M_3` at `c = 1`, `α = 3/2`. -/
theorem smaller_constant_contrast :
    SpatialMaximum 3 (riesz 1 (3 / 2)) (3 / 2 - 1) (M3 1 (3 / 2)) :=
  higher_riesz_three one_pos (by norm_num) (by norm_num)

/-- The halved constant `M_3/2` is not admissible. -/
theorem smaller_constant_refuted :
    ¬ SpatialMaximum 3 (riesz 1 (3 / 2)) (3 / 2 - 1) (M3 1 (3 / 2) / 2) := by
  intro h
  have h1 := higher_riesz_three_optimal zero_le_one (by norm_num) (by norm_num) h
  have h2 := M3_pos one_pos (show (3 / 2 : ℝ) < 2 by norm_num)
  linarith

end Refutations.HigherRieszThree
