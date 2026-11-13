import StratonovichHAMSecondMoment.GaussianScalarPowers

/-!
Refutation for `StratonovichHAMSecondMoment.GaussianScalarPowers.integer_power`
(manuscript `L:gaussian-scalar-powers`, display `E:gaussian-integer-power`):
the absolute values cannot be dropped.

The wrong variant is the package statement (same binders and hypotheses) with
`|x|`, `|y|` replaced by `x`, `y`. Counterexample: `L = 3`, `q = 2`, `x = -2`,
`y = 1`: LHS `= 4`, RHS `= (2/3)(-8) + 1/3 = -5`.
The contrast theorem applies the package theorem at the same point.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.GaussianScalarPowers

/-- `integer_power` without absolute values is false. -/
theorem integer_power_signed :
    ¬ (∀ (L q : ℕ), 0 < L → q ≤ L → ∀ x y : ℝ,
      x ^ q * y ^ (L - q) ≤ (q : ℝ) / L * x ^ L + ((L : ℝ) - q) / L * y ^ L) := by
  intro h
  have := h 3 2 (by norm_num) (by norm_num) (-2) 1
  norm_num at this

/-- Contrast: at the counterexample `L = 3`, `q = 2`, `x = -2`, `y = 1` the
package statement (with absolute values) holds. -/
theorem integer_power_signed_contrast :
    |(-2 : ℝ)| ^ 2 * |(1 : ℝ)| ^ (3 - 2) ≤
      ((2 : ℕ) : ℝ) / (3 : ℕ) * |(-2 : ℝ)| ^ 3 +
        (((3 : ℕ) : ℝ) - (2 : ℕ)) / (3 : ℕ) * |(1 : ℝ)| ^ 3 :=
  StratonovichHAMSecondMoment.GaussianScalarPowers.integer_power 3 2 (by norm_num)
    (by norm_num) (-2) 1

end Refutations.GaussianScalarPowers
