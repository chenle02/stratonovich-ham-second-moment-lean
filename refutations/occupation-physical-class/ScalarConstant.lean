/-
Refutation for the scalar maximum in the proof of `P:occupation-physical-class`
(`notes/integrated_spatial_occupation.tex` lines 431-433 at a284420), package theorem
`StratonovichHAMSecondMoment.OccupationPhysicalClass.scalar_max`
(`c T^{α/2} - T/2 ≤ (2-α)/2 · α^{α/(2-α)} · c^{2/(2-α)}`).

Wrong variant: the constant halved, `c T^{α/2} - T/2 ≤ spEnergyVal α c / 2`.
Counterexample: `α = 1`, `c = 1`, `T = 1` (the maximiser `T = (cα)^{2/(2-α)}`): the left side
is `1/2`, `spEnergyVal 1 1 = 1/2`, so the variant would give `1/2 ≤ 1/4`.
`scalar_constant_contrast` applies the package theorem at the same point (equality).
No junk-value reliance (`0 < α < 2`, all bases positive).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.OccupationPhysicalClass

set_option autoImplicit false

open StratonovichHAMSecondMoment.OccupationPhysicalClass

namespace Refutations.OccupationPhysicalClass

theorem spEnergyVal_one_one : spEnergyVal 1 1 = 1 / 2 := by
  unfold spEnergyVal; norm_num

/-- The halved constant is false. -/
theorem scalar_constant_refuted :
    ¬ (∀ alpha c T : ℝ, 0 < alpha → alpha < 2 → 0 ≤ c → 0 ≤ T →
        c * T ^ (alpha / 2) - T / 2 ≤ spEnergyVal alpha c / 2) := by
  intro h
  have := h 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [spEnergyVal_one_one, Real.one_rpow] at this
  norm_num at this

/-- The package bound at the same point. -/
theorem scalar_constant_contrast : (1 : ℝ) * 1 ^ ((1 : ℝ) / 2) - 1 / 2 ≤ spEnergyVal 1 1 :=
  scalar_max (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Refutations.OccupationPhysicalClass
