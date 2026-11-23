/-
Refutation for `L:source-finite-comparison`
(`notes/integrated_source_convergence.tex` lines 21-45 at edf7085f), package
theorem `StratonovichHAMSecondMoment.SourceTube.source_finite_comparison_law`.

Class (a): manuscript-claim perturbation in the manuscript domain.
Wrong variant: the reversed inequality
`(E‖∑ ξⱼ vⱼ‖^p)^{1/p} ≥ √C (E‖∑ gⱼ vⱼ‖^p)^{1/p}` (the covariance bound gives
only the upper comparison).  Counterexample: `N = 1`, `E = ℝ`, `v₁ = 1`,
`p = 2`, `ξ = 0` (`S = 0`), `C = 1`: the left side is `0`, the right side `1`.
`reversed_contrast` is the package inequality at the same point.  No junk-value
reliance (`0^{1/2} = 0` is genuine, both moments integrable).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SourceTube

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open StratonovichHAMSecondMoment GaussianComparison SourceTube

namespace Refutations.SourceTube

/-- Calibration: the second moment of `x ↦ x₁ · 1` under `N(0,S)` is `S₁₁`. -/
theorem reversed_moment {S : Matrix (Fin 1) (Fin 1) ℝ} (hS : S.PosSemidef) :
    ∫ x, ‖∑ j, x j • (1 : ℝ)‖ ^ (2 : ℝ)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) S) = S 0 0 := by
  rw [← integral_coord_sq hS 0]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [coordSeminorm_apply]

/-- The reversed comparison is false. -/
theorem reversed_refuted :
    ¬ (∀ (S : Matrix (Fin 1) (Fin 1) ℝ) (C : ℝ), S.PosSemidef → 0 ≤ C →
        (C • (1 : Matrix (Fin 1) (Fin 1) ℝ) - S).PosSemidef → ∀ p : ℝ, 1 ≤ p →
        Real.sqrt C * (∫ x, ‖∑ j, x j • (1 : ℝ)‖ ^ p
            ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)) ^ (1 / p) ≤
          (∫ x, ‖∑ j, x j • (1 : ℝ)‖ ^ p
            ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) S)) ^ (1 / p)) := by
  intro h
  have := h 0 1 Matrix.PosSemidef.zero zero_le_one (by simpa using Matrix.PosSemidef.one) 2
    (by norm_num)
  rw [reversed_moment Matrix.PosSemidef.zero, reversed_moment Matrix.PosSemidef.one] at this
  norm_num at this

/-- The package inequality at the same point. -/
theorem reversed_contrast :
    (∫ x, ‖∑ j, x j • (1 : ℝ)‖ ^ (2 : ℝ)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 0)) ^ (1 / (2 : ℝ)) ≤
      Real.sqrt 1 * (∫ x, ‖∑ j, x j • (1 : ℝ)‖ ^ (2 : ℝ)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)) ^ (1 / (2 : ℝ)) :=
  (source_finite_comparison_law Matrix.PosSemidef.zero zero_le_one
    (by simpa using Matrix.PosSemidef.one) (fun _ => (1 : ℝ)) (by norm_num)).2.2

end Refutations.SourceTube
