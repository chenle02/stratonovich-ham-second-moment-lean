/-
Refutation for the strict comparison of `C:intrinsic-spatial-bracket`, package theorem
`StratonovichHAMSecondMoment.SpatialBracket.F0_lt_Fa`
(`integrated_occupation_ceiling.tex` lines 261-265 and 286 at a284420: `F_0(z) < F_a(z)`).

Wrong variant: the comparison in the other direction, `F_a(z) ≤ F_0(z)` for every `z > 0`
(at `α = 1`, `a = 1/2`).  Counterexample: `z = 1`, where the package gives `F_0(1) < F_a(1)`.
`fa_below_f0_contrast` is the package inequality at the same point.
No junk-value reliance (`z > 0`, all bases positive).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpatialBracket

set_option autoImplicit false

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.SpatialBracket

namespace Refutations.SpatialBracket

/-- The package inequality `F_0(1) < F_{1/2}(1)` at `α = 1`. -/
theorem fa_below_f0_contrast : SpatialFourLinear.F0 1 1 < Fb 1 (1 / 2) 1 :=
  F0_lt_Fa (by norm_num) (by norm_num) (by norm_num) one_pos

/-- `F_a ≤ F_0` on `z > 0` is false at `α = 1`, `a = 1/2`. -/
theorem fa_below_f0_refuted :
    ¬ (∀ z : ℝ, 0 < z → Fb 1 (1 / 2) z ≤ SpatialFourLinear.F0 1 z) := by
  intro h
  exact absurd (h 1 one_pos) (not_le.2 fa_below_f0_contrast)

end Refutations.SpatialBracket
