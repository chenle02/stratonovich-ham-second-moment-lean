/-
Refutation for the summation step of `P:interval-coefficients`
(`E:interval-phase-bound`, main TeX lines 3570-3579 at revision a284420),
package theorem
`StratonovichHAMSecondMoment.IntervalScalar.interval_phase_bound_of_coefficients`.

Wrong variant: dropping the prefactor `e` (the zero-order energy bound
`≤ e‖v‖²` of lines 3570-3571), i.e. `energy ≤ exp(ν C^{1/ν} R^{1/ν} T^{β/ν}) V`.
Counterexample: `ν = 2`, `β = 3`, `C = R = 0`, `T = V = 1`, coefficients
`c_0 = e` and `c_m = 0` otherwise (all hypotheses hold), energy `= e > 1 =
exp 0`.  The value `0^{1/2} = 0` is the honest real power at `0`, not a junk
value of a conclusion.  `phase_factor_contrast` is the package bound for the
same data.

Expected outcome: compiles (refuted)
-/
import StratonovichHAMSecondMoment.IntervalScalar

set_option autoImplicit false

open scoped Nat

namespace Refutations.IntervalScalar

/-- The coefficient sequence of the counterexample. -/
noncomputable def cEx : ℕ → ℝ := fun m => if m = 0 then Real.exp 1 else 0

theorem cEx_tsum : ∑' m, cEx m = Real.exp 1 := by
  unfold cEx
  simp

theorem cEx_hyps :
    (∀ k, cEx (2 * k + 1) = 0) ∧ cEx 0 ≤ Real.exp 1 * 1 ∧
      (∀ k, 1 ≤ k → |cEx (2 * k)| ≤
        (0 : ℝ) ^ k * (0 : ℝ) ^ k * (1 : ℝ) ^ ((3 : ℝ) * k) / (k ! : ℝ) ^ (2 : ℝ) * 1) := by
  refine ⟨fun k => by simp [cEx], by simp [cEx], fun k hk => ?_⟩
  have : 2 * k ≠ 0 := by omega
  simp only [cEx, this, ite_false, abs_zero]
  positivity

/-- Without the factor `e` the phase bound fails. -/
theorem phase_factor_refuted :
    ¬ (∀ c : ℕ → ℝ, (∀ k, c (2 * k + 1) = 0) → c 0 ≤ Real.exp 1 * 1 →
        (∀ k, 1 ≤ k → |c (2 * k)| ≤
          (0 : ℝ) ^ k * (0 : ℝ) ^ k * (1 : ℝ) ^ ((3 : ℝ) * k) / (k ! : ℝ) ^ (2 : ℝ) * 1) →
        ∑' m, c m ≤ Real.exp (2 * (0 : ℝ) ^ (1 / (2 : ℝ)) * (0 : ℝ) ^ (1 / (2 : ℝ)) *
          (1 : ℝ) ^ ((3 : ℝ) / 2)) * 1) := by
  intro h
  obtain ⟨h1, h2, h3⟩ := cEx_hyps
  have := h cEx h1 h2 h3
  rw [cEx_tsum, Real.zero_rpow (by norm_num)] at this
  simp at this
  have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
  linarith

/-- The package bound for the same data. -/
theorem phase_factor_contrast :
    ∑' m, cEx m ≤ Real.exp 1 * Real.exp (2 * (0 : ℝ) ^ (1 / (2 : ℝ)) * (0 : ℝ) ^ (1 / (2 : ℝ)) *
      (1 : ℝ) ^ ((3 : ℝ) / 2)) * 1 := by
  obtain ⟨h1, h2, h3⟩ := cEx_hyps
  exact (StratonovichHAMSecondMoment.IntervalScalar.interval_phase_bound_of_coefficients cEx
    (by norm_num) le_rfl le_rfl one_pos zero_le_one h1 h2 h3 rfl).2

end Refutations.IntervalScalar
