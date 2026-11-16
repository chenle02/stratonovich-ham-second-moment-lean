/-
Refutation for the height monotonicity behind `E:split-fresh-insertion`
(main TeX lines 3890-3894 at 39f2597a: `Λ(t_i)^{(α-2)/2} ≤ λ^{(α-2)/2}`),
package theorem `StratonovichHAMSecondMoment.FixedSplit.fock_insertion_bound`
(insertion bound `‖J_i x‖_ρ ≤ c_i ‖x‖_ρ` for `ρ ≥ λ` only).

Wrong variant: the same monotonicity for norms below `λ`, i.e.
`ρ^{(α-2)/2} ≤ λ^{(α-2)/2}` for `0 < ρ ≤ λ`, `α ≤ 2` (which would extend the
insertion bound with `c_i` to every `ρ ≤ λ`).
Counterexample: `α = 0`, `ρ = 1`, `λ = 4`: `1 ≤ 1/4` is false.  No
junk-value reliance (positive bases).  `insertion_below_lambda_contrast` is
the direction used by the package (`ρ ≥ λ`), on the same numbers.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.FixedSplit

set_option autoImplicit false

namespace Refutations.FixedSplit

/-- The insertion factor does not decrease below `λ`. -/
theorem insertion_below_lambda_refuted :
    ¬ (∀ alpha ρ lam : ℝ, alpha ≤ 2 → 0 < ρ → ρ ≤ lam →
        ρ ^ ((alpha - 2) / 2) ≤ lam ^ ((alpha - 2) / 2)) := by
  intro h
  have := h 0 1 4 (by norm_num) one_pos (by norm_num)
  have e : ((0 : ℝ) - 2) / 2 = -1 := by norm_num
  rw [e, Real.one_rpow, Real.rpow_neg_one] at this
  norm_num at this

/-- Contrast: for `ρ ≥ λ` the factor decreases (the step `hpow` of
`fock_insertion_bound`), on the same numbers. -/
theorem insertion_below_lambda_contrast :
    (4 : ℝ) ^ (((0 : ℝ) - 2) / 2) ≤ (1 : ℝ) ^ (((0 : ℝ) - 2) / 2) :=
  Real.rpow_le_rpow_of_nonpos one_pos (by norm_num) (by norm_num)

end Refutations.FixedSplit
