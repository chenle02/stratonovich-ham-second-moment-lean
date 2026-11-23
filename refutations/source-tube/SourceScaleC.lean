/-
Refutation for `L:source-finite-comparison`
(`notes/integrated_source_convergence.tex` lines 21-45 at edf7085f), package
theorem `StratonovichHAMSecondMoment.SourceTube.source_finite_comparison_law`.

Class (a): manuscript-claim perturbation in the manuscript domain.
Wrong variant: the factor `√C` in `E:source-finite-comparison` replaced by `C`.
Counterexample: `N = 1`, `E = ℝ`, `v₁ = 1`, `p = 2`, covariance `S = C = 1/4`:
the left side is `(1/4)^{1/2} = 1/2`, the right side `1/4 · 1^{1/2} = 1/4`.
`scale_c_contrast` is the package inequality (with `√C`) at the same point.
No junk-value reliance: both moments are integrable (package conclusion).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SourceTube

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open StratonovichHAMSecondMoment GaussianComparison SourceTube

namespace Refutations.SourceTube

/-- Calibration: the second moment of `x ↦ x₁ · 1` under `N(0,S)` is `S₁₁`. -/
theorem scale_c_moment {S : Matrix (Fin 1) (Fin 1) ℝ} (hS : S.PosSemidef) :
    ∫ x, ‖∑ j, x j • (1 : ℝ)‖ ^ (2 : ℝ)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) S) = S 0 0 := by
  rw [← integral_coord_sq hS 0]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [coordSeminorm_apply]

/-- Calibration: `(1/4)^{1/2} = 1/2`. -/
theorem scale_c_quarter : ((1 : ℝ) / 4) ^ ((1 : ℝ) / 2) = 1 / 2 := by
  rw [show (1 : ℝ) / 4 = (1 / 2) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- The comparison with `C` in place of `√C` is false. -/
theorem scale_c_refuted :
    ¬ (∀ (S : Matrix (Fin 1) (Fin 1) ℝ) (C : ℝ), S.PosSemidef → 0 ≤ C →
        (C • (1 : Matrix (Fin 1) (Fin 1) ℝ) - S).PosSemidef → ∀ p : ℝ, 1 ≤ p →
        (∫ x, ‖∑ j, x j • (1 : ℝ)‖ ^ p
            ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) S)) ^ (1 / p) ≤
          C * (∫ x, ‖∑ j, x j • (1 : ℝ)‖ ^ p
            ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)) ^ (1 / p)) := by
  intro h
  have hS : (((1 : ℝ) / 4) • (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by norm_num)
  have := h _ (1 / 4) hS (by norm_num) (by simpa using Matrix.PosSemidef.zero) 2 (by norm_num)
  rw [scale_c_moment hS, scale_c_moment Matrix.PosSemidef.one] at this
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    Real.one_rpow] at this
  rw [scale_c_quarter] at this
  norm_num at this

/-- The package inequality (with `√C`) at the same point. -/
theorem scale_c_contrast :
    (∫ x, ‖∑ j, x j • (1 : ℝ)‖ ^ (2 : ℝ) ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1))
        (((1 : ℝ) / 4) • (1 : Matrix (Fin 1) (Fin 1) ℝ)))) ^ (1 / (2 : ℝ)) ≤
      Real.sqrt (1 / 4) * (∫ x, ‖∑ j, x j • (1 : ℝ)‖ ^ (2 : ℝ)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)) ^ (1 / (2 : ℝ)) :=
  (source_finite_comparison_law (Matrix.PosSemidef.one.smul (by norm_num)) (by norm_num)
    (by simpa using Matrix.PosSemidef.zero) (fun _ => (1 : ℝ)) (by norm_num)).2.2

end Refutations.SourceTube
