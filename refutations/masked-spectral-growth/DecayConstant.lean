/-
Refutation for the auxiliary Gaussian decay bound of `GaussianTest`, package
theorem `StratonovichHAMSecondMoment.GaussianTest.poly_mul_exp_neg_sq_le`
(`(1+s)^m e^{-cs²} ≤ e^{m²/(4c)}`; auxiliary to the Lean proof route of
`P:masked-spectral-growth`).

Wrong variant: a constant independent of `c`, i.e.
`(1+s) e^{-cs²} ≤ e^{1/4}` for all `c > 0` and `s ≥ 0` (the value of the
package bound at `c = 1`, `m = 1`).  Counterexample: `c = 1/100`, `s = 1`:
`2 e^{-1/100} > e^{1/4}` because `e^{26/100} < 2` (`log 2 > 0.69`).
`decay_constant_contrast` is the package bound at the same point.
No junk-value reliance (`c > 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.GaussianTest

set_option autoImplicit false

open Real

namespace Refutations.MaskedSpectralGrowth

/-- A `c`-independent constant in the Gaussian decay bound is false. -/
theorem decay_constant_refuted :
    ¬ (∀ c : ℝ, 0 < c → ∀ s : ℝ, 0 ≤ s →
        (1 + s) ^ 1 * Real.exp (-(c * s ^ 2)) ≤ Real.exp (1 / 4)) := by
  intro h
  have h1 := h (1 / 100) (by norm_num) 1 (by norm_num)
  have h2 : Real.exp (26 / 100) < 2 := by
    calc Real.exp (26 / 100) < Real.exp (Real.log 2) :=
          Real.exp_lt_exp.2 (by linarith [Real.log_two_gt_d9])
      _ = 2 := Real.exp_log two_pos
  have h3 : Real.exp (1 / 4) = Real.exp (26 / 100) * Real.exp (-(1 / 100 * 1 ^ 2)) := by
    rw [← Real.exp_add]; norm_num
  rw [h3] at h1
  have hpos := Real.exp_pos (-(1 / 100 * (1 : ℝ) ^ 2))
  norm_num at h1 hpos
  nlinarith

/-- The package bound at the same point: `2 e^{-1/100} ≤ e^{1/(4/100)}`. -/
theorem decay_constant_contrast :
    (1 + (1 : ℝ)) ^ 1 * Real.exp (-(1 / 100 * (1 : ℝ) ^ 2)) ≤
      Real.exp (((1 : ℕ) : ℝ) ^ 2 / (4 * (1 / 100))) :=
  StratonovichHAMSecondMoment.GaussianTest.poly_mul_exp_neg_sq_le 1 (by norm_num) (by norm_num)

end Refutations.MaskedSpectralGrowth
