/-
Refutation for the hypothesis `q ≥ 1` of the scalar series inequality
(proof of `P:d1-upper`, main TeX lines 5540-5545 at 39f2597a, used by
`P:low-alpha-upper` and `C:d1-first-calibration`).  Package theorem
`StratonovichHAMSecondMoment.TwoSimplexTime.sum_div_factorial_rpow_le`.

Wrong variant: the partial-sum inequality `Σ_{k<n} z^k/(k!)^q ≤ exp(q z^{1/q})`
for every `q > 0`.  Counterexample: `q = 1/2`, `z = 1`, `n = 2`: the left side is
`2` and the right side `e^{1/2} < 2`.  `subunitExponent_contrast` is the package
inequality at `q = 1`.  Class (c): a Lean generalization outside the manuscript
domain (there `q = 3 - α ≥ 2`); it shows the hypothesis `q ≥ 1` is needed.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TwoSimplexTime

set_option autoImplicit false

open StratonovichHAMSecondMoment TwoSimplexTime
open scoped Nat

namespace Refutations.LowAlphaUpper.SubunitExponent

/-- The inequality fails for `q = 1/2`. -/
theorem subunitExponent_refuted :
    ¬ (∀ q z : ℝ, 0 < q → 0 ≤ z → ∀ n : ℕ,
      ∑ k ∈ Finset.range n, z ^ k / (k ! : ℝ) ^ q ≤ Real.exp (q * z ^ (1 / q))) := by
  intro h
  have h1 := h (1 / 2) 1 (by norm_num) zero_le_one 2
  simp [Finset.sum_range_succ] at h1
  have he : Real.exp (1 / 2) < 2 := by
    have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h3 : Real.exp 1 < 4 := by
      have := Real.exp_one_lt_d9; linarith
    nlinarith [Real.exp_pos (1 / 2)]
  linarith

/-- The package inequality at `q = 1`, `z = 1`, `n = 2`. -/
theorem subunitExponent_contrast :
    ∑ k ∈ Finset.range 2, (1 : ℝ) ^ k / (k ! : ℝ) ^ (1 : ℝ) ≤
      Real.exp (1 * (1 : ℝ) ^ (1 / (1 : ℝ))) :=
  sum_div_factorial_rpow_le le_rfl zero_le_one 2

end Refutations.LowAlphaUpper.SubunitExponent
