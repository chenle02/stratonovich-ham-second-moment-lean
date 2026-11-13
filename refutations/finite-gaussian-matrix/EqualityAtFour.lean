import StratonovichHAMSecondMoment.FiniteGaussianMatrix

/-!
Refutation for
`StratonovichHAMSecondMoment.FiniteGaussianMatrix.finite_gaussian_matrix_two`
(manuscript `P:finite-gaussian-matrix`, "The first inequality is an equality
at `p = 2`"): the equality does not extend to `p = 4`.

The wrong variant is equality in `E:finite-gaussian-average` at `p = 4` for all
`1 × 16` families.  Counterexample: the coordinate rows of
`R:gaussian-one-variance-test`: the fourth power of the left side is `288`,
that of the right side is `9 · 136 = 1224`.
The contrast theorem applies the package equality at `p = 2` to the same
family.  All `rpow` bases are nonnegative.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.FiniteGaussianMatrix

open MeasureTheory Matrix StratonovichHAMSecondMoment.FiniteGaussianMatrix
  StratonovichHAMSecondMoment.GaussianIBP

/-- Equality in `E:finite-gaussian-average` at `p = 4` is false. -/
theorem finite_gaussian_average_equality_four :
    ¬ (∀ A : Fin 16 → Matrix (Fin 1) (Fin 16) ℂ,
      (∫ x, schattenPow (gaussLin A x) 2 ∂stdPi 16) ^ (1 / (2 * ((2 : ℕ) : ℝ))) =
        √(2 * ((2 : ℕ) : ℝ) - 1) *
          (((trace (vOut A ^ 2)).re + (trace (vIn A ^ 2)).re) / 2) ^
            (1 / (2 * ((2 : ℕ) : ℝ)))) := by
  intro h
  have h1 := congrArg (· ^ 4) (h (rowFamily 16))
  rw [integral_schattenPow_rowFamily.2, rpow_quarter_pow _ (by norm_num),
    gaussian_one_variance_test.2.2.2.2.2.2.2.1] at h1
  norm_num at h1

/-- Contrast: at `p = 2` the package equality holds for the same family. -/
theorem finite_gaussian_average_equality_four_contrast :
    (∫ x, schattenPow (gaussLin (rowFamily 16) x) 1 ∂stdPi 16) ^ (1 / (2 * ((1 : ℕ) : ℝ))) =
      √(2 * ((1 : ℕ) : ℝ) - 1) *
        (((trace (vOut (rowFamily 16) ^ 1)).re + (trace (vIn (rowFamily 16) ^ 1)).re) / 2) ^
          (1 / (2 * ((1 : ℕ) : ℝ))) :=
  (finite_gaussian_matrix_two (rowFamily 16)).2.2

end Refutations.FiniteGaussianMatrix
