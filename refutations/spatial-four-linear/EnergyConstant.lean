/-
Refutation for the scalar maximum behind `E:spatial-energy-map`
(`notes/integrated_spatial_occupation.tex` lines 309-314 and 330-335 at a284420), package
theorem `StratonovichHAMSecondMoment.SpatialFourLinear.young_bound`
(`R β^{α/2} - β/2 ≤ (2-α)/2 · α^{α/(2-α)} · R^{2/(2-α)}`).

Wrong variant: half the constant, `R β^{α/2} - β/2 ≤ energyValue α R / 2` for all `β ≥ 0`.
Counterexample: `α = 1`, `R = 1`, `β = 1`: the left side is `1/2`, while
`energyValue 1 1 / 2 = 1/4`.  `energy_constant_contrast` is the package bound at the same point.
No junk-value reliance (`0 < α < 2`, `R, β > 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpatialFourLinear

set_option autoImplicit false

open StratonovichHAMSecondMoment.SpatialFourLinear

namespace Refutations.SpatialFourLinear

theorem energyValue_one_one : energyValue 1 1 = 1 / 2 := by
  unfold energyValue
  norm_num

/-- Halving the constant of the scalar maximum is false. -/
theorem energy_constant_refuted :
    ¬ (∀ β : ℝ, 0 ≤ β → (1 : ℝ) * β ^ ((1 : ℝ) / 2) - β / 2 ≤ energyValue 1 1 / 2) := by
  intro h
  have := h 1 (by norm_num)
  rw [energyValue_one_one] at this
  norm_num at this

/-- The package bound at the counterexample point. -/
theorem energy_constant_contrast :
    (1 : ℝ) * (1 : ℝ) ^ ((1 : ℝ) / 2) - 1 / 2 ≤ energyValue 1 1 :=
  young_bound (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Refutations.SpatialFourLinear
