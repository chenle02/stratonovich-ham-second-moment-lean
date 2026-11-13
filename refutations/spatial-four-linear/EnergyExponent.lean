/-
Refutation for the scalar maximum behind `E:spatial-energy-map`
(`notes/integrated_spatial_occupation.tex` lines 309-314 and 330-335 at a284420), package
theorem `StratonovichHAMSecondMoment.SpatialFourLinear.young_bound`.

Wrong variant: exponent `1` on `R` instead of `2/(2-α)`, i.e.
`R β^{α/2} - β/2 ≤ (2-α)/2 · α^{α/(2-α)} · R` for all `β ≥ 0`.
Counterexample: `α = 1`, `R = 4`, `β = 16`: the left side is `16 - 8 = 8`, the wrong right side
is `2`.  `energy_exponent_contrast` is the package bound at the same point (`energyValue 1 4 = 8`).
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpatialFourLinear

set_option autoImplicit false

open StratonovichHAMSecondMoment.SpatialFourLinear

namespace Refutations.SpatialFourLinear

theorem sixteen_rpow_half : (16 : ℝ) ^ ((1 : ℝ) / 2) = 4 := by
  rw [← Real.sqrt_eq_rpow, show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The exponent `1` on `R` in the scalar maximum is false. -/
theorem energy_exponent_refuted :
    ¬ (∀ β : ℝ, 0 ≤ β → (4 : ℝ) * β ^ ((1 : ℝ) / 2) - β / 2 ≤
      (2 - 1) / 2 * (1 : ℝ) ^ ((1 : ℝ) / (2 - 1)) * 4) := by
  intro h
  have := h 16 (by norm_num)
  rw [sixteen_rpow_half] at this
  norm_num at this

/-- The package bound at the counterexample point. -/
theorem energy_exponent_contrast :
    (4 : ℝ) * (16 : ℝ) ^ ((1 : ℝ) / 2) - 16 / 2 ≤ energyValue 1 4 :=
  young_bound (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Refutations.SpatialFourLinear
