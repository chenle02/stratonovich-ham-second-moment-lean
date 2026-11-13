import StratonovichHAMSecondMoment.GaussianScalarPowers

/-!
Refutation for `StratonovichHAMSecondMoment.GaussianScalarPowers.integer_power`
(manuscript `L:gaussian-scalar-powers`, display `E:gaussian-integer-power`):
the weights `q/L` and `(L-q)/L` cannot be swapped.

The wrong variant is the package statement (same binders and hypotheses) with
the two weights exchanged. Counterexample: `L = 3`, `q = 2`, `x = 2`, `y = 1`:
LHS `= 4`, swapped RHS `= 8/3 + 2/3 = 10/3 < 4`.
The contrast theorem applies the package theorem at the same point.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.GaussianScalarPowers

/-- `integer_power` with swapped weights is false. -/
theorem integer_power_swapped_weights :
    ¬ (∀ (L q : ℕ), 0 < L → q ≤ L → ∀ x y : ℝ,
      |x| ^ q * |y| ^ (L - q) ≤ ((L : ℝ) - q) / L * |x| ^ L + (q : ℝ) / L * |y| ^ L) := by
  intro h
  have := h 3 2 (by norm_num) (by norm_num) 2 1
  norm_num at this

/-- Contrast: at the counterexample `L = 3`, `q = 2`, `x = 2`, `y = 1` the
package statement (correct weights) holds. -/
theorem integer_power_swapped_weights_contrast :
    |(2 : ℝ)| ^ 2 * |(1 : ℝ)| ^ (3 - 2) ≤
      ((2 : ℕ) : ℝ) / (3 : ℕ) * |(2 : ℝ)| ^ 3 +
        (((3 : ℕ) : ℝ) - (2 : ℕ)) / (3 : ℕ) * |(1 : ℝ)| ^ 3 :=
  StratonovichHAMSecondMoment.GaussianScalarPowers.integer_power 3 2 (by norm_num)
    (by norm_num) 2 1

end Refutations.GaussianScalarPowers
