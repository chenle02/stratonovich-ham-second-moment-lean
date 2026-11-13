/-
Refutation for the attained scalar maximum of `E:spatial-energy-map`
(`notes/integrated_spatial_occupation.tex` lines 330-335 at a284420: the maximum of
`ℓ^α A - ℓ² b/2` is at `ℓ^{2-α} = αA/b`), package theorem
`StratonovichHAMSecondMoment.SpatialFourLinear.energy_attain` (maximiser
`β = (αR)^{2/(2-α)}`).

Wrong variant: the maximiser `β = αR` (exponent `1` instead of `2/(2-α)`) attains the value.
Counterexample: `α = 1`, `R = 4`: `4 · 4^{1/2} - 4/2 = 6 ≠ 8 = energyValue 1 4`.
`maximizer_contrast` is the package identity at the same point.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpatialFourLinear

set_option autoImplicit false

open StratonovichHAMSecondMoment.SpatialFourLinear

namespace Refutations.SpatialFourLinear

theorem energyValue_one_four : energyValue 1 4 = 8 := by
  unfold energyValue
  rw [show (2 : ℝ) / (2 - 1) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- The maximiser `β = αR` does not attain the energy value. -/
theorem maximizer_refuted :
    ¬ ((4 : ℝ) * (1 * 4) ^ ((1 : ℝ) / 2) - 1 * 4 / 2 = energyValue 1 4) := by
  rw [energyValue_one_four, show ((1 : ℝ) * 4) = 2 ^ 2 by norm_num, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (by norm_num)]
  norm_num

/-- The package identity at the counterexample point. -/
theorem maximizer_contrast :
    (4 : ℝ) * ((1 * 4) ^ (2 / (2 - (1 : ℝ)))) ^ ((1 : ℝ) / 2) -
      (1 * 4) ^ (2 / (2 - (1 : ℝ))) / 2 = energyValue 1 4 :=
  energy_attain (by norm_num) (by norm_num) (by norm_num)

end Refutations.SpatialFourLinear
