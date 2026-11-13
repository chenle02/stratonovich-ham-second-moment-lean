/-
Refutation for `C:static-moment-constant-continuity` (main TeX lines
7574-7593), package theorem
`StratonovichHAMSecondMoment.TypeContinuity.static_moment_constant_continuity_paper`
(`Λ̲_2(a)/Λ̄_1(a) → 2^{κ_st}`, `E:static-moment-ratio-continuity`).

Wrong variant: the limit ratio is the Jensen value `2` for every admissible
`α`, i.e. `2^{κ_st} = 2` for `0 < α < 2`. Counterexample: `α = 1`, where
`κ_st = (4-1)/(3-1) = 3/2` and `2^{3/2} > 2`.
`ratio_not_two_contrast` records that `κ_st(1) = 3/2` with the package's
own definitions. No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TypeContinuity

set_option autoImplicit false

namespace Refutations.TypeContinuity

open StratonovichHAMSecondMoment.TypeContinuity

/-- The limit ratio of `E:static-moment-ratio-continuity` is not the Jensen
value `2`. -/
theorem ratio_not_two_refuted :
    ¬ (∀ alpha : ℝ, 0 < alpha → alpha < 2 → (2 : ℝ) ^ kappaSt alpha = 2) := by
  intro h
  have h1 := h 1 one_pos (by norm_num)
  have hk : kappaSt 1 = 3 / 2 := by norm_num [kappaSt, nuOf]
  rw [hk] at h1
  have : (2 : ℝ) ^ (1 : ℝ) < (2 : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  rw [Real.rpow_one, h1] at this
  exact lt_irrefl _ this

/-- The package's `κ_st` at `α = 1` is `3/2 > 1`. -/
theorem ratio_not_two_contrast : kappaSt 1 = 3 / 2 ∧ 1 < kappaSt 1 := by
  constructor <;> norm_num [kappaSt, nuOf]

end Refutations.TypeContinuity
