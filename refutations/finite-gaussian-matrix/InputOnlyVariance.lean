import StratonovichHAMSecondMoment.FiniteGaussianMatrix

/-!
Refutation for
`StratonovichHAMSecondMoment.FiniteGaussianMatrix.finite_gaussian_matrix`
(manuscript `P:finite-gaussian-matrix`, display `E:finite-gaussian-maximum`,
and `R:gaussian-one-variance-test`): the maximum of the two variance
directions cannot be replaced by the input variance alone, nor by the output
variance alone.

Wrong variants: `(E‖X‖_{S_4}^4)^{1/4} ≤ √3 ‖V_in^{1/2}‖_{S_4}` for all `1 × 16`
families, and `(E‖X‖_{S_4}^4)^{1/4} ≤ √3 ‖V_out^{1/2}‖_{S_4}` for all `16 × 1`
families.  Counterexamples: the coordinate rows (`E = 288 > 9 Tr I^2 = 144`)
and their transposes.  The contrast theorem applies the package maximum bound
at the row family.  All `rpow` bases are nonnegative.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.FiniteGaussianMatrix

open MeasureTheory Matrix StratonovichHAMSecondMoment.FiniteGaussianMatrix
  StratonovichHAMSecondMoment.GaussianIBP
open scoped MatrixOrder

/-- The input-only bound is false. -/
theorem finite_gaussian_maximum_input_only :
    ¬ (∀ A : Fin 16 → Matrix (Fin 1) (Fin 16) ℂ,
      (∫ x, schattenPow (gaussLin A x) 2 ∂stdPi 16) ^ (1 / (2 * ((2 : ℕ) : ℝ))) ≤
        √(2 * ((2 : ℕ) : ℝ) - 1) * schattenNorm (CFC.sqrt (vIn A)) 2) :=
  fun h => gaussian_one_variance_test.2.2.2.2.2.2.1 (h (rowFamily 16))

/-- The output-only bound is false. -/
theorem finite_gaussian_maximum_output_only :
    ¬ (∀ A : Fin 16 → Matrix (Fin 16) (Fin 1) ℂ,
      (∫ x, schattenPow (gaussLin A x) 2 ∂stdPi 16) ^ (1 / (2 * ((2 : ℕ) : ℝ))) ≤
        √(2 * ((2 : ℕ) : ℝ) - 1) * schattenNorm (CFC.sqrt (vOut A)) 2) :=
  fun h => gaussian_one_variance_test.2.2.2.2.2.2.2.2.2.2 (h (colFamily 16))

/-- Contrast: at the row family the package bound with the maximum holds. -/
theorem finite_gaussian_maximum_input_only_contrast :
    (∫ x, schattenPow (gaussLin (rowFamily 16) x) 2 ∂stdPi 16) ^ (1 / (2 * ((2 : ℕ) : ℝ))) ≤
      √(2 * ((2 : ℕ) : ℝ) - 1) * max (schattenNorm (CFC.sqrt (vOut (rowFamily 16))) 2)
        (schattenNorm (CFC.sqrt (vIn (rowFamily 16))) 2) :=
  let h := finite_gaussian_matrix (rowFamily 16) 2 (by norm_num)
  h.2.1.trans h.2.2

end Refutations.FiniteGaussianMatrix
