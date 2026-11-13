/-
Refutation for a dropped hypothesis of the scalar maximum of `P:raw-occupation-energy`
(`notes/integrated_occupation_ceiling.tex` lines 99-104 and 137-141 at a284420, `ζ > 0`),
package theorem `StratonovichHAMSecondMoment.RawOccupationEnergy.scalar_max_zeta`.

Wrong variant: `ζ ≥ 0` in place of `ζ > 0`.  Counterexample: `ζ = 0`, `α = 1`, `C = X = 1`:
the left side is `1`.  JUNK-VALUE RELIANCE: at `ζ = 0` the formula
`D_0 = (2-α)/2 (α/(2·0))^{α/(2-α)}` is Lean's `1/0 = 0` value, so `D_0 = 0`; the TeX does not
define `D_0` (it takes `ζ > 0`), so the variant is false in Lean through that value.
`penalty_positive_contrast` is the package bound at `ζ = 1/2`, same `C`, `X`.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.RawOccupationEnergy

set_option autoImplicit false

namespace Refutations.RawOccupationEnergy

open StratonovichHAMSecondMoment

/-- Dropping `ζ > 0` (allowing `ζ = 0`) in the scalar maximum is false in Lean. -/
theorem penalty_positive_refuted :
    ¬ (∀ ζ C X : ℝ, 0 ≤ ζ → 0 ≤ C → 0 ≤ X →
        C * X ^ ((1 : ℝ) / 2) - ζ * X ≤ SpatialBracket.Dzeta 1 ζ * C ^ (2 / (2 - (1 : ℝ)))) := by
  intro h
  have h1 := h 0 1 1 le_rfl (by norm_num) (by norm_num)
  unfold SpatialBracket.Dzeta at h1
  norm_num at h1

/-- The package bound at `ζ = 1/2`, `C = X = 1`. -/
theorem penalty_positive_contrast :
    (1 : ℝ) * (1 : ℝ) ^ ((1 : ℝ) / 2) - 1 / 2 * 1 ≤
      SpatialBracket.Dzeta 1 (1 / 2) * (1 : ℝ) ^ (2 / (2 - (1 : ℝ))) :=
  RawOccupationEnergy.scalar_max_zeta (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

end Refutations.RawOccupationEnergy
