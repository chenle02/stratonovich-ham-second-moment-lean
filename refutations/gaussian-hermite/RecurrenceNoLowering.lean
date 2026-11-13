import StratonovichHAMSecondMoment.GaussianHermite

/-!
Refutation for `StratonovichHAMSecondMoment.GaussianHermite.mul_hn` (the recurrence
`x hn_n = √(n+1) hn_{n+1} + √n hn_{n-1}`, main TeX lines 2515-2517 at a284420).

Wrong variant: multiplication by `x` as pure creation, `x hn_n = √(n+1) hn_{n+1}` (the
annihilation term dropped).  Counterexample: `n = 1`, `x = 0`: the package recurrence gives
`√2 hn_2(0) = -1`, while the wrong variant gives `√2 hn_2(0) = 0`.  No junk-value reliance.
`recurrence_contrast` is the package value at the same point.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.GaussianHermite

open StratonovichHAMSecondMoment.GaussianHermite

/-- The recurrence fails without the annihilation term. -/
theorem recurrence_no_lowering_refuted :
    ¬ (∀ (n : ℕ) (x : ℝ), x * hn n x = Real.sqrt ((n : ℝ) + 1) * hn (n + 1) x) := by
  intro H
  have h1 := H 1 0
  have h2 := mul_hn 1 0
  simp only [Nat.sub_self, hn_zero] at h2
  norm_num at h1 h2
  rw [h1] at h2
  norm_num at h2

/-- Contrast: the package recurrence at `n = 1`, `x = 0` gives `√2 hn_2(0) = -1`. -/
theorem recurrence_contrast : Real.sqrt 2 * hn 2 0 = -1 := by
  have h2 := mul_hn 1 0
  simp only [Nat.sub_self, hn_zero] at h2
  norm_num at h2
  linarith

end Refutations.GaussianHermite
