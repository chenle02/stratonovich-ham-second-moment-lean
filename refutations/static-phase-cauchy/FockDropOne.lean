import StratonovichHAMSecondMoment.StaticPhaseCauchy

/-!
Refutation for `StratonovichHAMSecondMoment.StaticPhaseCauchy.fockD_le` (the step
`d_n ≤ 2 √(2n) √R_α` of `P:static-phase-all-orders`, main TeX lines 2633-2634 at
a284420, with `d_N = 2 √(N+1) √R_α` of `E:fock-sandwich`, lines 2484-2488).

Wrong variant: `d_n ≤ 2 √n √R` (the `+1` of `N + 1` absorbed without the factor `2`).
Counterexample: `n = 1`, `R = 1`: `d_1 = 2√2 > 2`.  No junk-value reliance.
`fock_drop_one_contrast` is the package inequality at the same point.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.StaticPhaseCauchy

open StratonovichHAMSecondMoment.StaticPhaseCauchy

/-- `d_n ≤ 2 √n √R` fails at `n = 1`, `R = 1`. -/
theorem fock_drop_one_refuted :
    ¬ (∀ n : ℕ, 1 ≤ n → ∀ R : ℝ, fockD n R ≤ 2 * √(n : ℝ) * √R) := by
  intro H
  have h := H 1 le_rfl 1
  simp only [fockD, Nat.cast_one, Real.sqrt_one, mul_one] at h
  have h2 : (1 : ℝ) < √(1 + 1) := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- Contrast: the package inequality at `n = 1`, `R = 1`. -/
theorem fock_drop_one_contrast : fockD 1 1 ≤ 2 * √(2 * ((1 : ℕ) : ℝ)) * √1 :=
  fockD_le le_rfl 1

end Refutations.StaticPhaseCauchy
