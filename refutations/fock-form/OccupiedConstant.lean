import StratonovichHAMSecondMoment.FockForm

/-!
Refutation for `StratonovichHAMSecondMoment.FockForm.occupied_multiplication`
(`E:occupied-multiplication`, `‖HF‖₂ ≤ 2√(n+1)‖H‖₂‖F‖₂`, main TeX lines 1802-1804 at a284420).

Wrong variant: the constant `n+1` in place of `4(n+1)` (i.e. `√(n+1)` in place of `2√(n+1)`,
keeping only the creation part).  Counterexample: one coordinate, `H = F = g` (`n = 1`):
`E[g⁴] = 3 > 2 = (n+1) E[g²]²`.  No junk-value reliance.  `occupied_contrast` is the package
bound at the same point.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.FockForm

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.FockForm MeasureTheory
  ProbabilityTheory

/-- Auxiliary: `∫ (x_0 x_0)² dγ_1 = 3`. -/
theorem integral_fourth : ∫ x, ((x 0) * (x 0)) ^ 2 ∂GaussianIBP.stdPi 1 = 3 := by
  have h : (fun x : Fin 1 → ℝ => ((x 0) * (x 0)) ^ 2) = fun x => ∏ i, (x i) ^ 4 := by
    funext x; simp; ring
  rw [h, GaussianIBP.stdPi, integral_fintype_prod_eq_prod (f := fun _ y => y ^ 4)]
  simp [GaussianIBP.moment_four]

/-- Auxiliary: `∫ x_0² dγ_1 = 1`. -/
theorem integral_second : ∫ x, (x 0) ^ 2 ∂GaussianIBP.stdPi 1 = 1 := by
  have h : (fun x : Fin 1 → ℝ => (x 0) ^ 2) = fun x => ∏ i, (x i) ^ 2 := by
    funext x; simp
  rw [h, GaussianIBP.stdPi, integral_fintype_prod_eq_prod (f := fun _ y => y ^ 2)]
  simp [GaussianIBP.moment_two]

/-- `E:occupied-multiplication` fails with the constant `n + 1`. -/
theorem occupied_constant_refuted :
    ¬ (∀ (n : ℕ) (a : Fin 1 → ℝ) (p : MvPolynomial (Fin 1) ℝ), p.totalDegree ≤ n →
        ∫ x, ((∑ i, a i * x i) * MvPolynomial.eval x p) ^ 2 ∂GaussianIBP.stdPi 1 ≤
          ((n : ℝ) + 1) * (∫ x, (∑ i, a i * x i) ^ 2 ∂GaussianIBP.stdPi 1) *
            ∫ x, (MvPolynomial.eval x p) ^ 2 ∂GaussianIBP.stdPi 1) := by
  intro H
  have h := H 1 (fun _ => 1) (MvPolynomial.X 0) (by simp)
  simp only [Fin.sum_univ_one, one_mul, MvPolynomial.eval_X] at h
  rw [integral_fourth, integral_second] at h
  norm_num at h

/-- Contrast: the package bound at the same point (`3 ≤ 8`). -/
theorem occupied_contrast :
    ∫ x, ((∑ i, (fun _ : Fin 1 => (1 : ℝ)) i * x i) *
        MvPolynomial.eval x (MvPolynomial.X 0)) ^ 2 ∂GaussianIBP.stdPi 1 ≤
      4 * ((1 : ℕ) + 1 : ℝ) * (∫ x, (∑ i, (fun _ : Fin 1 => (1 : ℝ)) i * x i) ^ 2
        ∂GaussianIBP.stdPi 1) *
        ∫ x, (MvPolynomial.eval x (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℝ)) ^ 2
          ∂GaussianIBP.stdPi 1 :=
  (occupied_multiplication 1 _ _ (by simp)).2.2.2

end Refutations.FockForm
