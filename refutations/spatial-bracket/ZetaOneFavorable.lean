/-
Refutation for the `ζ = 1` remark of `C:intrinsic-spatial-bracket`, package theorem
`StratonovichHAMSecondMoment.SpatialBracket.counterexample_ratio`
(`integrated_occupation_ceiling.tex` lines 290-298 at a284420).

Wrong variant: the strict comparison of lines 261-265 holds at every `ζ > 0`, i.e.
`U_𝔠[C] < 𝔠^m F_a(D_ζ C^{2/(2-α)})` for all `𝔠, C, ζ > 0` (at `α = 5/4`, `a = 1/2`).
Counterexample: `ζ = 1`, `𝔠 = C = 1`, where the package gives the reverse strict inequality.
`zeta_one_contrast` is the package inequality at that point.
No junk-value reliance (`𝔠, C, ζ > 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpatialBracket

set_option autoImplicit false

open StratonovichHAMSecondMoment.SpatialBracket

namespace Refutations.SpatialBracket

/-- The package inequality at `ζ = 1`, `𝔠 = C = 1`, `α = 5/4`, `a = 1/2`. -/
theorem zeta_one_contrast :
    (1 : ℝ) ^ (((4 : ℝ) - 5 / 4) / (3 - 5 / 4)) *
        Fb (5 / 4) (1 / 2) (Dzeta (5 / 4) 1 * (1 : ℝ) ^ ((2 : ℝ) / (2 - 5 / 4))) <
      ceilingValue (5 / 4) 1 1 :=
  counterexample_ratio one_pos one_pos

/-- The comparison `U_𝔠 < 𝔠^m F_a(D_ζ C^{2/(2-α)})` does not hold at every `ζ > 0`. -/
theorem zeta_one_refuted :
    ¬ (∀ c C ζ : ℝ, 0 < c → 0 < C → 0 < ζ →
      ceilingValue (5 / 4) c C <
        c ^ (((4 : ℝ) - 5 / 4) / (3 - 5 / 4)) *
          Fb (5 / 4) (1 / 2) (Dzeta (5 / 4) ζ * C ^ ((2 : ℝ) / (2 - 5 / 4)))) := by
  intro h
  exact lt_asymm (h 1 1 1 one_pos one_pos one_pos) zeta_one_contrast

end Refutations.SpatialBracket
