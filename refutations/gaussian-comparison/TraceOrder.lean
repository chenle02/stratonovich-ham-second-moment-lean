/-
Refutation for the finite Gaussian comparison of `P:masked-noise-completion`
(`notes/integrated_covariance_foundation.tex` lines 201-205 and 239-246 at
a284420), package theorem
`StratonovichHAMSecondMoment.GaussianComparison.gaussian_seminorm_moment_le`.

Wrong variant: the positive semidefinite order `A ≤ B` (TeX lines 240-241)
weakened to the trace order `tr A ≤ tr B` (with `A`, `B` positive
semidefinite).
Counterexample: `ι = Fin 2`, `A = diag(1,0)`, `B = diag(0,2)`, `N(x) = |x₀|`,
`p = 2`: `tr A = 1 ≤ 2 = tr B`, but `∫ |x₀|² dN(0,A) = 1 > 0 = ∫ |x₀|² dN(0,B)`
(`integral_coord_sq`).
`trace_order_contrast` applies the package theorem to the pair
`diag(0,2) ≤ diag(1,2)`, which is ordered in the positive semidefinite sense.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.GaussianComparison

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open StratonovichHAMSecondMoment GaussianComparison

namespace Refutations.GaussianComparison

/-- `diag(a,b)` is positive semidefinite for `a, b ≥ 0`. -/
theorem diag_psd {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Matrix.diagonal ![a, b]).PosSemidef := by
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> simpa

/-- The comparison under the trace order is false. -/
theorem trace_order_refuted :
    ¬ (∀ (A B : Matrix (Fin 2) (Fin 2) ℝ), A.PosSemidef → B.PosSemidef →
        A.trace ≤ B.trace →
        ∀ (N : Seminorm ℝ (EuclideanSpace ℝ (Fin 2))) (p : ℝ), 1 ≤ p →
        ∫ x, N x ^ p ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) A) ≤
          ∫ x, N x ^ p ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) B)) := by
  intro h
  have hA := diag_psd (a := 1) (b := 0) (by norm_num) le_rfl
  have hB := diag_psd (a := 0) (b := 2) le_rfl (by norm_num)
  have htr : (Matrix.diagonal ![(1 : ℝ), 0]).trace ≤ (Matrix.diagonal ![(0 : ℝ), 2]).trace := by
    simp [Matrix.trace, Fin.sum_univ_two]
  have := h _ _ hA hB htr (coordSeminorm 0) 2 (by norm_num)
  rw [integral_coord_sq hA, integral_coord_sq hB] at this
  simp at this
  norm_num at this

/-- The package theorem for `diag(0,2) ≤ diag(1,2)`: `∫ |x₀|² dN(0,diag(0,2)) ≤
∫ |x₀|² dN(0,diag(1,2))`. -/
theorem trace_order_contrast :
    ∫ x, coordSeminorm 0 x ^ (2 : ℝ)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (Matrix.diagonal ![0, 2])) ≤
      ∫ x, coordSeminorm 0 x ^ (2 : ℝ)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (Matrix.diagonal ![1, 2])) := by
  have hBA : (Matrix.diagonal ![(1 : ℝ), 2] - Matrix.diagonal ![0, 2]).PosSemidef := by
    rw [Matrix.diagonal_sub]
    convert diag_psd (a := 1) (b := 0) (by norm_num) le_rfl using 2
    ext i; fin_cases i <;> simp
  exact (gaussian_seminorm_moment_le (diag_psd le_rfl (by norm_num)) hBA
    (coordSeminorm 0) (by norm_num)).2.2

end Refutations.GaussianComparison
