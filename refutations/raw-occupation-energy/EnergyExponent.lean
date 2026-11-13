/-
Refutation for the exponent of `E:raw-occupation-energy`
(`notes/integrated_occupation_ceiling.tex` lines 100-104 at a284420: `𝓔_ζ^𝒪 = D_ζ
C_occ^{2/(2-α)}`), at the level of the package's scalar maximum
`StratonovichHAMSecondMoment.RawOccupationEnergy.scalar_max_zeta`.

Wrong variant: the exponent `1/(2-α)` in place of `2/(2-α)`, i.e.
`r X^{α/2} - ζ X ≤ D_ζ r^{1/(2-α)}` for all `X ≥ 0`.  Counterexample: `α = 1`, `ζ = 1/2`,
`r = 2`, `X = 4` (the optimizer `(α r/(2ζ))^{2/(2-α)}`): the left side is `2`, the right side
is `D_{1/2} · 2 = 1`.  `energy_exponent_contrast` is the package bound at the same point (right
side `D_{1/2} · 2² = 2`).  No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.RawOccupationEnergy

set_option autoImplicit false

namespace Refutations.RawOccupationEnergy

open StratonovichHAMSecondMoment

/-- `4^{1/2} = 2`. -/
theorem four_rpow_half : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `D_{1/2} = 1/2` at `α = 1`. -/
theorem dzeta_value' : SpatialBracket.Dzeta 1 (1 / 2) = 1 / 2 := by
  unfold SpatialBracket.Dzeta
  norm_num

/-- The exponent `1/(2-α)` in the energy formula is false. -/
theorem energy_exponent_refuted :
    ¬ (∀ X : ℝ, 0 ≤ X →
        2 * X ^ ((1 : ℝ) / 2) - 1 / 2 * X ≤
          SpatialBracket.Dzeta 1 (1 / 2) * 2 ^ (1 / (2 - (1 : ℝ)))) := by
  intro h
  have h1 := h 4 (by norm_num)
  rw [four_rpow_half, dzeta_value'] at h1
  norm_num at h1

/-- The package bound at the same point. -/
theorem energy_exponent_contrast :
    (2 : ℝ) * (4 : ℝ) ^ ((1 : ℝ) / 2) - 1 / 2 * 4 ≤
      SpatialBracket.Dzeta 1 (1 / 2) * (2 : ℝ) ^ (2 / (2 - (1 : ℝ))) :=
  RawOccupationEnergy.scalar_max_zeta (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

end Refutations.RawOccupationEnergy
