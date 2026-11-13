/-
Refutation for the scalar maximum in the proof of `P:occupation-physical-class`
(`notes/integrated_spatial_occupation.tex` lines 431-433 at a284420), package theorem
`StratonovichHAMSecondMoment.OccupationPhysicalClass.scalar_max`, with the hypothesis
`α < 2` dropped (the manuscript's strict inequality, lines 7-8).

Wrong variant: the bound at `α = 2`.  There `spEnergyVal 2 c = 0` (the factor `(2-α)/2`
vanishes; Lean also reads `2/(2-α) = 2/0` as `0`, a junk value, but the vanishing factor
makes the right side `0` regardless), while `c T - T/2 = 1/2 > 0` at `c = T = 1`.
`alpha_two_contrast` is the package bound at `α = 1`, `c = T = 1`.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.OccupationPhysicalClass

set_option autoImplicit false

open StratonovichHAMSecondMoment.OccupationPhysicalClass

namespace Refutations.OccupationPhysicalClass

/-- The scalar maximum without `α < 2` is false (at `α = 2`). -/
theorem alpha_two_refuted :
    ¬ (∀ c T : ℝ, 0 ≤ c → 0 ≤ T → c * T ^ ((2 : ℝ) / 2) - T / 2 ≤ spEnergyVal 2 c) := by
  intro h
  have := h 1 1 (by norm_num) (by norm_num)
  unfold spEnergyVal at this
  norm_num at this

/-- The package bound with `α = 1 < 2`. -/
theorem alpha_two_contrast : (1 : ℝ) * 1 ^ ((1 : ℝ) / 2) - 1 / 2 ≤ spEnergyVal 1 1 :=
  scalar_max (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Refutations.OccupationPhysicalClass
