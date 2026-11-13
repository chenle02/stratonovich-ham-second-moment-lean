/-
Refutation for the factorial inequality of `SeriesType`, package theorem
`StratonovichHAMSecondMoment.SeriesType.factorial_sq_le_mul_factorial`
(`(k!)^2 ≤ r! s!` when `r + s = 2k`; main TeX lines 2754, 5119).

Wrong variant: the reversed inequality `r! s! ≤ (k!)^2` when `r + s = 2k`
(the central split would maximize the product). Counterexample: `r = 0`,
`s = 2`, `k = 1`: `0! 2! = 2 > 1 = (1!)^2`.
`reversed_factorial_contrast` is the package inequality at the same point.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SeriesType

set_option autoImplicit false

open scoped Nat

namespace Refutations.SeriesType

/-- The central split does not maximize `r! s!`. -/
theorem reversed_factorial_refuted :
    ¬ (∀ r s k : ℕ, r + s = 2 * k → r ! * s ! ≤ (k !) ^ 2) := by
  intro h
  have := h 0 2 1 (by norm_num)
  simp [Nat.factorial] at this

/-- The package inequality at the same point: `(1!)^2 ≤ 0! 2!`. -/
theorem reversed_factorial_contrast : (1 !) ^ 2 ≤ 0 ! * 2 ! :=
  StratonovichHAMSecondMoment.SeriesType.factorial_sq_le_mul_factorial (by norm_num)

end Refutations.SeriesType
