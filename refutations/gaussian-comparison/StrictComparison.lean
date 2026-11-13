/-
Refutation for the finite Gaussian comparison of `P:masked-noise-completion`
(`notes/integrated_covariance_foundation.tex` lines 201-205 and 239-246 at
a284420), package theorem
`StratonovichHAMSecondMoment.GaussianComparison.gaussian_seminorm_moment_le`.

Wrong variant: a strict comparison whenever `A ≠ B`, i.e. for `A` and `B - A`
positive semidefinite with `A ≠ B`, every seminorm `N` and `p ≥ 1`,
`∫ N(x)^p dN(0,A) < ∫ N(x)^p dN(0,B)`.
Counterexample: `ι = Fin 1`, `A = 0`, `B = 1`, `N = 0` (the zero seminorm),
`p = 1`: both sides are `∫ 0 = 0`.
`strict_comparison_contrast` is the package (non-strict) inequality at the same
point.  No junk-value reliance (`0^1 = 0` is genuine).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.GaussianComparison

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open StratonovichHAMSecondMoment GaussianComparison

namespace Refutations.GaussianComparison

/-- A strict comparison for `A ≠ B` is false. -/
theorem strict_comparison_refuted :
    ¬ (∀ (A B : Matrix (Fin 1) (Fin 1) ℝ), A.PosSemidef → (B - A).PosSemidef → A ≠ B →
        ∀ (N : Seminorm ℝ (EuclideanSpace ℝ (Fin 1))) (p : ℝ), 1 ≤ p →
        ∫ x, N x ^ p ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) A) <
          ∫ x, N x ^ p ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) B)) := by
  intro h
  have hne : (0 : Matrix (Fin 1) (Fin 1) ℝ) ≠ 1 := by
    intro h0
    have := congrFun (congrFun h0 0) 0
    simp at this
  have := h 0 1 Matrix.PosSemidef.zero (by simpa using Matrix.PosSemidef.one) hne 0 1 le_rfl
  simp at this

/-- The package inequality at the same point (it holds with equality). -/
theorem strict_comparison_contrast :
    ∫ x, (0 : Seminorm ℝ (EuclideanSpace ℝ (Fin 1))) x ^ (1 : ℝ)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 0) ≤
      ∫ x, (0 : Seminorm ℝ (EuclideanSpace ℝ (Fin 1))) x ^ (1 : ℝ)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
  (gaussian_seminorm_moment_le Matrix.PosSemidef.zero (by simpa using Matrix.PosSemidef.one)
    0 le_rfl).2.2

end Refutations.GaussianComparison
