import StratonovichHAMSecondMoment.FiniteGaussianMatrix

/-!
Refutation for
`StratonovichHAMSecondMoment.FiniteGaussianMatrix.finite_gaussian_matrix`
(manuscript `P:finite-gaussian-matrix`, display `E:finite-gaussian-average`):
the factor `√(p-1)` cannot be dropped (replaced by `1`) at `p = 4`.

The wrong variant is `(E‖X‖_{S_4}^4)^{1/4} ≤ ((Tr V_out^2 + Tr V_in^2)/2)^{1/4}`
for all families.  Counterexample: the coordinate rows of
`R:gaussian-one-variance-test`, `n = 16`: `E‖X‖_{S_4}^4 = 288` and
`(Tr V_out^2 + Tr V_in^2)/2 = (256 + 16)/2 = 136 < 288`.
The contrast theorem applies the package theorem at the same family.
All bases of `rpow` are nonnegative; no junk value is involved.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.FiniteGaussianMatrix

open MeasureTheory Matrix StratonovichHAMSecondMoment.FiniteGaussianMatrix
  StratonovichHAMSecondMoment.GaussianIBP

/-- `E:finite-gaussian-average` without the factor `√(p-1)` is false at `p = 4`. -/
theorem finite_gaussian_average_constant_one :
    ¬ (∀ A : Fin 16 → Matrix (Fin 1) (Fin 16) ℂ,
      (∫ x, schattenPow (gaussLin A x) 2 ∂stdPi 16) ^ (1 / (2 * ((2 : ℕ) : ℝ))) ≤
        (((trace (vOut A ^ 2)).re + (trace (vIn A ^ 2)).re) / 2) ^
          (1 / (2 * ((2 : ℕ) : ℝ)))) := by
  intro h
  have h1 := h (rowFamily 16)
  rw [integral_schattenPow_rowFamily.2, trace_vOut_rowFamily_sq,
    trace_vIn_rowFamily_sq] at h1
  have h4 := pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) h1 4
  rw [rpow_quarter_pow _ (by norm_num), rpow_quarter_pow _ (by norm_num)] at h4
  norm_num at h4

/-- Contrast: at the same family the package bound (with `√(p-1) = √3`) holds. -/
theorem finite_gaussian_average_constant_one_contrast :
    (∫ x, schattenPow (gaussLin (rowFamily 16) x) 2 ∂stdPi 16) ^ (1 / (2 * ((2 : ℕ) : ℝ))) ≤
      √(2 * ((2 : ℕ) : ℝ) - 1) *
        (((trace (vOut (rowFamily 16) ^ 2)).re + (trace (vIn (rowFamily 16) ^ 2)).re) / 2) ^
          (1 / (2 * ((2 : ℕ) : ℝ))) :=
  (finite_gaussian_matrix (rowFamily 16) 2 (by norm_num)).2.1

end Refutations.FiniteGaussianMatrix
