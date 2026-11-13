import StratonovichHAMSecondMoment.FiniteGaussianMatrix

/-!
Refutation for
`StratonovichHAMSecondMoment.FiniteGaussianMatrix.finite_hermitian_gaussian`
(manuscript `E:finite-hermitian-gaussian`): the constant `(2m-1)^m` cannot be
replaced by `1` (the "Gaussian moments are bounded by the variance power"
variant).

The wrong variant is the package statement at `m = 2` with `(2m-1)^m = 9`
replaced by `1`.  Counterexample: `N = 1`, the `1 × 1` matrix `B_1 = 1`, so
`Y = g_1`, `D = 1`: `E Tr Y^4 = E g^4 = 3 > 1 = Tr D^2`.
The contrast theorem applies the package theorem at the same family: `3 ≤ 9`.
No junk value is involved (the integrand is integrable).

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.FiniteGaussianMatrix

open MeasureTheory Matrix StratonovichHAMSecondMoment.FiniteGaussianMatrix
  StratonovichHAMSecondMoment.GaussianIBP

/-- The one-element family `B_1 = 1` (`1 × 1`). -/
def oneFamily : Fin 1 → Matrix (Fin 1) (Fin 1) ℂ := fun _ => 1

theorem trace_oneFamily_pow (x : Fin 1 → ℝ) :
    (trace (gaussLin oneFamily x ^ (2 * 2))).re = x 0 ^ 2 * x 0 ^ 2 := by
  simp [gaussLin, oneFamily, trace, smul_pow]
  norm_cast
  ring

theorem integral_oneFamily :
    ∫ x, (trace (gaussLin oneFamily x ^ (2 * 2))).re ∂stdPi 1 = 3 := by
  simp only [trace_oneFamily_pow]
  rw [(integral_sq_mul_sq (0 : Fin 1) 0).2]; simp

theorem trace_oneFamily_var : (trace ((∑ k, oneFamily k ^ 2) ^ 2)).re = 1 := by
  simp [oneFamily, trace]

/-- `E Tr Y^4 ≤ Tr D^2` (constant `1` instead of `(2m-1)^m = 9`) is false. -/
theorem finite_hermitian_gaussian_constant_one :
    ¬ (∀ B : Fin 1 → Matrix (Fin 1) (Fin 1) ℂ, (∀ k, (B k).IsHermitian) →
      ∫ x, (trace (gaussLin B x ^ (2 * 2))).re ∂stdPi 1 ≤ (trace ((∑ k, B k ^ 2) ^ 2)).re) := by
  intro h
  have := h oneFamily (fun _ => isHermitian_one)
  rw [integral_oneFamily, trace_oneFamily_var] at this
  norm_num at this

/-- Contrast: the package theorem at the same family gives `3 ≤ 9 · 1`. -/
theorem finite_hermitian_gaussian_constant_one_contrast :
    ∫ x, (trace (gaussLin oneFamily x ^ (2 * 2))).re ∂stdPi 1 ≤
      (2 * ((2 : ℕ) : ℝ) - 1) ^ 2 * (trace ((∑ k, oneFamily k ^ 2) ^ 2)).re ∧
    ¬ ((3 : ℝ) ≤ 1) :=
  ⟨(finite_hermitian_gaussian oneFamily (fun _ => isHermitian_one) 2 (by norm_num)).2,
    by norm_num⟩

end Refutations.FiniteGaussianMatrix
