/-
Refutation for the scalar maximum in the proof of `P:occupation-physical-class`
(`notes/integrated_spatial_occupation.tex` lines 431-433 at a284420), package theorem
`StratonovichHAMSecondMoment.OccupationPhysicalClass.scalar_max`.

Wrong variant: the exponent `2/(2-α)` of `c` dropped, i.e. (at `α = 1`)
`c T^{1/2} - T/2 ≤ (1/2) · 1^{1} · c = c/2` for all `c, T ≥ 0`.
Counterexample: `c = 4`, `T = 16`: the left side is `4 · 4 - 8 = 8`, the variant's right side
is `2`.  `scalar_exponent_contrast` applies the package theorem at the same point:
`8 ≤ spEnergyVal 1 4 = 8`.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.OccupationPhysicalClass

set_option autoImplicit false

open StratonovichHAMSecondMoment.OccupationPhysicalClass

namespace Refutations.OccupationPhysicalClass

theorem sixteen_rpow_half : (16 : ℝ) ^ ((1 : ℝ) / 2) = 4 := by
  rw [show (16 : ℝ) = 4 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- Dropping the exponent `2/(2-α)` of `c` is false. -/
theorem scalar_exponent_refuted :
    ¬ (∀ c T : ℝ, 0 ≤ c → 0 ≤ T →
        c * T ^ ((1 : ℝ) / 2) - T / 2 ≤ (2 - 1) / 2 * (1 : ℝ) ^ ((1 : ℝ) / (2 - 1)) * c) := by
  intro h
  have := h 4 16 (by norm_num) (by norm_num)
  rw [sixteen_rpow_half, Real.one_rpow] at this
  norm_num at this

/-- The package bound at the same point. -/
theorem scalar_exponent_contrast :
    (4 : ℝ) * 16 ^ ((1 : ℝ) / 2) - 16 / 2 ≤ spEnergyVal 1 4 :=
  scalar_max (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem scalar_exponent_contrast_value : spEnergyVal 1 4 = 8 := by
  unfold spEnergyVal; norm_num

end Refutations.OccupationPhysicalClass
