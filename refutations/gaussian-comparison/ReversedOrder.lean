/-
Refutation for the finite Gaussian comparison of `P:masked-noise-completion`
(`notes/integrated_covariance_foundation.tex` lines 201-205 and 239-246 at
a284420), package theorem
`StratonovichHAMSecondMoment.GaussianComparison.gaussian_seminorm_moment_le`.

Wrong variant: the comparison in the reversed direction, i.e. for `A` and
`B - A` positive semidefinite, `∫ N(x)^p dN(0,B) ≤ ∫ N(x)^p dN(0,A)`.
Counterexample: `ι = Fin 1`, `A = 0`, `B = 1`, `N(x) = |x₀|`, `p = 2`: the left
side is `B₀₀ = 1`, the right side `A₀₀ = 0` (`integral_coord_sq`).
`reversed_order_contrast` is the package inequality at the same point.
No junk-value reliance (both integrands are integrable, by the package).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.GaussianComparison

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open StratonovichHAMSecondMoment GaussianComparison

namespace Refutations.GaussianComparison

/-- The reversed comparison is false. -/
theorem reversed_order_refuted :
    ¬ (∀ (A B : Matrix (Fin 1) (Fin 1) ℝ), A.PosSemidef → (B - A).PosSemidef →
        ∀ (N : Seminorm ℝ (EuclideanSpace ℝ (Fin 1))) (p : ℝ), 1 ≤ p →
        ∫ x, N x ^ p ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) B) ≤
          ∫ x, N x ^ p ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) A)) := by
  intro h
  have := h 0 1 Matrix.PosSemidef.zero (by simpa using Matrix.PosSemidef.one)
    (coordSeminorm 0) 2 (by norm_num)
  rw [integral_coord_sq Matrix.PosSemidef.one, integral_coord_sq Matrix.PosSemidef.zero] at this
  norm_num at this

/-- The package inequality at the same point: `∫ |x₀|² dN(0,0) ≤ ∫ |x₀|² dN(0,1)`. -/
theorem reversed_order_contrast :
    ∫ x, coordSeminorm 0 x ^ (2 : ℝ)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 0) ≤
      ∫ x, coordSeminorm 0 x ^ (2 : ℝ)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
  (gaussian_seminorm_moment_le Matrix.PosSemidef.zero (by simpa using Matrix.PosSemidef.one)
    (coordSeminorm 0) (by norm_num)).2.2

end Refutations.GaussianComparison
