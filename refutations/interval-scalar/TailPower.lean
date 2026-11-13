/-
Refutation for the higher-order tail step of `C:static-interaction` (main TeX
lines 2762-2769 at revision a284420), package theorem
`StratonovichHAMSecondMoment.IntervalScalar.tail_series_le`
(`∑_{k≥2} x^k/(k!)^γ ≤ x² e^{γ x^{1/γ}}`).

Wrong variant: the prefactor `x³` instead of `x²` (one more power of the
coupling), i.e. `∑_{k≥2} x^k/(k!)^γ ≤ x³ e^{γ x^{1/γ}}` for all `x ≥ 0`, at
`γ = 1`.  Counterexample: `x = 1/100`; the `k = 2` term alone is `x²/2`, while
`x³ e^x ≤ x³ e < x²/2`.  `tail_power_contrast` is the package bound at the
same point.  The summability used for `term ≤ tsum` is the package's own
(no junk `tsum`).

Expected outcome: compiles (refuted)
-/
import StratonovichHAMSecondMoment.IntervalScalar

set_option autoImplicit false

open scoped Nat

namespace Refutations.IntervalScalar

/-- The tail bound with prefactor `x³` is false at `γ = 1`, `x = 1/100`. -/
theorem tail_power_refuted :
    ¬ (∀ x : ℝ, 0 ≤ x → ∑' j : ℕ, x ^ (j + 2) / ((j + 2)! : ℝ) ^ (1 : ℝ) ≤
        x ^ 3 * Real.exp (1 * x ^ (1 / (1 : ℝ)))) := by
  intro h
  have hx : (0 : ℝ) ≤ 1 / 100 := by norm_num
  have hs := (StratonovichHAMSecondMoment.IntervalScalar.tail_series_le le_rfl hx).1
  have h0 : (1 / 100 : ℝ) ^ (0 + 2) / ((0 + 2)! : ℝ) ^ (1 : ℝ) ≤
      ∑' j : ℕ, (1 / 100 : ℝ) ^ (j + 2) / ((j + 2)! : ℝ) ^ (1 : ℝ) :=
    hs.le_tsum 0 (fun j _ => by positivity)
  have h1 := h (1 / 100) hx
  have he : Real.exp (1 / 100) < 3 := by
    have := Real.exp_one_lt_d9
    have := Real.exp_le_exp.2 (show (1 / 100 : ℝ) ≤ 1 by norm_num)
    linarith
  simp only [Real.rpow_one, div_one, one_mul] at h0 h1
  norm_num [Nat.factorial] at h0 h1
  nlinarith [Real.exp_pos (1 / 100)]

/-- The package bound at the same point. -/
theorem tail_power_contrast :
    ∑' j : ℕ, (1 / 100 : ℝ) ^ (j + 2) / ((j + 2)! : ℝ) ^ (1 : ℝ) ≤
      (1 / 100 : ℝ) ^ 2 * Real.exp (1 * (1 / 100 : ℝ) ^ (1 / (1 : ℝ))) :=
  (StratonovichHAMSecondMoment.IntervalScalar.tail_series_le le_rfl (by norm_num)).2

end Refutations.IntervalScalar
