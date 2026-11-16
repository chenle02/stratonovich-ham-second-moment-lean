/-
Refutation for the factorial step of `E:low-alpha-coefficient` (second
inequality; main TeX lines 5537-5538 and 5727-5730 at 39f2597a:
`k! k^{bk} ≥ (k!)^{b+1} = (k!)^q`).  Package theorem
`StratonovichHAMSecondMoment.LowAlphaUpper.coeff_factorial_le`.

Wrong variant: the exponent `q = b + 1` raised to `b + 2`,
`x/(k! k^{bk}) ≤ x/(k!)^{b+2}`.  Counterexample in the manuscript domain:
`b = 1` (`α = 1`), `k = 3`, `x = 1`: `1/162 > 1/216`.
`factorialExponent_contrast` is the package inequality with `b + 1` there.
Class (a): manuscript-claim perturbation in the manuscript domain.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.LowAlphaUpper

set_option autoImplicit false

open StratonovichHAMSecondMoment LowAlphaUpper
open scoped Nat

namespace Refutations.LowAlphaUpper.FactorialExponent

/-- The wrong exponent `b + 2` fails at `b = 1`, `k = 3`, `x = 1`. -/
theorem factorialExponent_refuted :
    ¬ (∀ (x b : ℝ), 0 ≤ x → 0 ≤ b → ∀ k : ℕ,
      x / ((k ! : ℝ) * (k : ℝ) ^ (b * k)) ≤ x / (k ! : ℝ) ^ (b + 2)) := by
  intro h
  have h1 := h 1 1 zero_le_one zero_le_one 3
  have e1 : ((3 : ℕ) : ℝ) ^ ((1 : ℝ) * ((3 : ℕ) : ℝ)) = 27 := by
    rw [one_mul, Real.rpow_natCast]; norm_num
  have e2 : (((3 : ℕ)! : ℕ) : ℝ) ^ ((1 : ℝ) + 2) = 216 := by
    rw [show (1 : ℝ) + 2 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num [Nat.factorial]
  rw [e1, e2] at h1
  norm_num [Nat.factorial] at h1

/-- The package inequality at the same point. -/
theorem factorialExponent_contrast :
    (1 : ℝ) / (((3 : ℕ)! : ℝ) * ((3 : ℕ) : ℝ) ^ ((1 : ℝ) * (3 : ℕ))) ≤
      1 / (((3 : ℕ)! : ℝ)) ^ ((1 : ℝ) + 1) :=
  coeff_factorial_le zero_le_one zero_le_one 3

end Refutations.LowAlphaUpper.FactorialExponent
