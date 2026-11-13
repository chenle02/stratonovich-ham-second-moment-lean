/-
Refutation for the two-sided logarithmic factorial bounds of `SeriesType`,
package theorem `StratonovichHAMSecondMoment.SeriesType.log_factorial_bounds`
(`log k! ≤ k log k - k + 1 + log k` for `k ≥ 1`; main TeX lines 7246-7247).

Wrong variant: the upper bound without the `log k` term,
`log k! ≤ k log k - k + 1`. Counterexample: `k = 2`: it reads
`log 2 ≤ 2 log 2 - 1`, i.e. `1 ≤ log 2`, false since `log 2 < 0.7`.
`dropped_log_term_contrast` is the package bound at `k = 2`.
No junk-value reliance (`k = 2 > 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SeriesType

set_option autoImplicit false

open scoped Nat

namespace Refutations.SeriesType

/-- The upper factorial bound needs its `log k` term. -/
theorem dropped_log_term_refuted :
    ¬ (∀ k : ℕ, 1 ≤ k → Real.log (k ! : ℝ) ≤ (k : ℝ) * Real.log k - k + 1) := by
  intro h
  have h2 := h 2 (by norm_num)
  have hf : ((2 ! : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [hf] at h2
  push_cast at h2
  have := Real.log_two_lt_d9
  linarith

/-- The package bound at `k = 2`: `log 2! ≤ 2 log 2 - 2 + 1 + log 2`. -/
theorem dropped_log_term_contrast :
    Real.log ((2 ! : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ) * Real.log ((2 : ℕ) : ℝ) - ((2 : ℕ) : ℝ) + 1 +
      Real.log ((2 : ℕ) : ℝ) :=
  (StratonovichHAMSecondMoment.SeriesType.log_factorial_bounds 2 (by norm_num)).2

end Refutations.SeriesType
