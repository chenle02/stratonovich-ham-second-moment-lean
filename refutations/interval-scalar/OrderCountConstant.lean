/-
Refutation for the order-count step of `C:static-interaction` (main TeX line
2762 at revision a284420), package theorem
`StratonovichHAMSecondMoment.IntervalScalar.exp_mul_two_k_add_one_le`
(`e(2k+1) ≤ (3e)^k` for `k ≥ 1`).

Wrong variant: the smaller constant `B = 2e A²`, i.e. `e(2k+1) ≤ (2e)^k` for
all `k ≥ 1`.  Counterexample: `k = 1`, where `3e > 2e`.
`order_count_contrast` is the package bound at `k = 1`.
No junk-value reliance.

Expected outcome: compiles (refuted)
-/
import StratonovichHAMSecondMoment.IntervalScalar

set_option autoImplicit false

namespace Refutations.IntervalScalar

/-- `e(2k+1) ≤ (2e)^k` fails at `k = 1`. -/
theorem order_count_two_e_refuted :
    ¬ (∀ k : ℕ, 1 ≤ k → Real.exp 1 * (2 * k + 1) ≤ (2 * Real.exp 1) ^ k) := by
  intro h
  have h1 := h 1 le_rfl
  have he := Real.exp_pos 1
  norm_num at h1
  linarith

/-- The package bound at `k = 1`: `e · 3 ≤ (3e)^1`. -/
theorem order_count_contrast :
    Real.exp 1 * (2 * ((1 : ℕ) : ℝ) + 1) ≤ (3 * Real.exp 1) ^ (1 : ℕ) :=
  StratonovichHAMSecondMoment.IntervalScalar.exp_mul_two_k_add_one_le 1 le_rfl

end Refutations.IntervalScalar
