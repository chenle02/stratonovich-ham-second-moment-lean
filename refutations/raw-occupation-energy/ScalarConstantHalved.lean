/-
Refutation for the scalar maximum of `P:raw-occupation-energy`
(`notes/integrated_occupation_ceiling.tex` lines 137-141 at a284420), package theorem
`StratonovichHAMSecondMoment.RawOccupationEnergy.scalar_max_zeta`
(`C X^{α/2} - ζ X ≤ D_ζ C^{2/(2-α)}`).

Wrong variant: the constant `D_ζ` halved, `C X^{α/2} - ζ X ≤ D_ζ C^{2/(2-α)}/2` for all
`C, X ≥ 0`.  Counterexample: `α = 1`, `ζ = 1/2`, `C = X = 1`: the left side is `1/2` and
`D_{1/2} = 1/2`, so the right side is `1/4`.  `scalar_constant_contrast` is the package bound at
the same point.  No junk-value reliance (`ζ > 0`, `α ∈ (0,2)`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.RawOccupationEnergy

set_option autoImplicit false

namespace Refutations.RawOccupationEnergy

open StratonovichHAMSecondMoment

/-- `D_{1/2} = 1/2` at `α = 1`. -/
theorem dzeta_value : SpatialBracket.Dzeta 1 (1 / 2) = 1 / 2 := by
  unfold SpatialBracket.Dzeta
  norm_num

/-- Halving the constant `D_ζ` of the scalar maximum is false. -/
theorem scalar_constant_halved_refuted :
    ¬ (∀ C X : ℝ, 0 ≤ C → 0 ≤ X →
        C * X ^ ((1 : ℝ) / 2) - 1 / 2 * X ≤
          SpatialBracket.Dzeta 1 (1 / 2) * C ^ (2 / (2 - (1 : ℝ))) / 2) := by
  intro h
  have h1 := h 1 1 (by norm_num) (by norm_num)
  rw [dzeta_value] at h1
  norm_num at h1

/-- The package bound at the same point. -/
theorem scalar_constant_contrast :
    (1 : ℝ) * (1 : ℝ) ^ ((1 : ℝ) / 2) - 1 / 2 * 1 ≤
      SpatialBracket.Dzeta 1 (1 / 2) * (1 : ℝ) ^ (2 / (2 - (1 : ℝ))) :=
  RawOccupationEnergy.scalar_max_zeta (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

end Refutations.RawOccupationEnergy
