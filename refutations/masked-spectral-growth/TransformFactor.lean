/-
Refutation for `E:masked-gaussian-transform` of `P:masked-spectral-growth`
(`notes/integrated_covariance_foundation.tex` lines 42-45 at a284420), package
theorem `StratonovichHAMSecondMoment.MaskedSpectralGrowth.masked_gaussian_transform`.

Wrong variant: the normalizing factor `(r/(2√π))^d` dropped, i.e.
`∫ e^{-|ξ-y|²/r²} μ(dξ) = ∫ e^{-r²|x|²/4} e^{-iy·x} Γ(dx)` for every pair with
the spectral convention.  Counterexample: `d = 1`, `Γ` = Lebesgue measure,
`μ = δ_0`, `y = 0`, `r = 1`: the left side is `1`, the right side is
`M_Γ = 2√π ≠ 1`.  `transform_factor_contrast` is the package identity at the
same point.  No junk-value reliance (both integrals are of integrable
functions).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.MaskedSpectralGrowth

set_option autoImplicit false

open MeasureTheory Real
open StratonovichHAMSecondMoment HomogHypothesis SpectralHomog MaskedSpectralGrowth

namespace Refutations.MaskedSpectralGrowth

/-- Lebesgue measure on `ℝ¹` has spectral measure `δ_0`. -/
theorem leb_spectral : IsSpectralMeasure (volume : Measure (Rd 1)) (Measure.dirac 0) := by
  intro φ
  rw [integral_dirac]
  simp

/-- Lebesgue measure on `ℝ¹` scales with exponent `d - α = 1 - 0`. -/
theorem leb_scaling : SpectralHomogeneous (volume : Measure (Rd 1)) (((1 : ℕ) : ℝ) - 0) := by
  intro A _ c hc
  rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, pow_one, abs_of_pos hc]
  norm_num

/-- `M_Γ = 2√π` for Lebesgue measure on `ℝ¹`. -/
theorem leb_MGamma : MGamma (volume : Measure (Rd 1)) = 2 * Real.sqrt Real.pi := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Rd 1) (b := 1 / 4) (by norm_num)
  rw [finrank_euclideanSpace_fin] at h
  unfold MGamma
  have hpt : ∀ x : Rd 1, Real.exp (-(‖x‖ ^ 2 / 4)) = Real.exp (-(1 / 4) * ‖x‖ ^ 2) := by
    intro x; congr 1; ring
  simp_rw [hpt, h]
  rw [show Real.pi / (1 / 4) = (2 * Real.sqrt Real.pi) ^ 2 by
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]; ring]
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
  norm_num

/-- The left side at `μ = δ_0`, `y = 0`: `∫ e^{-|ξ|²/r²} dδ_0 = 1`. -/
theorem dirac_gauss (r : ℝ) :
    ∫ ξ, Real.exp (-(‖ξ - 0‖ ^ 2 / r ^ 2)) ∂(Measure.dirac (0 : Rd 1)) = 1 := by
  rw [integral_dirac]; simp

/-- The Lebesgue right side at `y = 0`, `r = 1` is `M_Γ = 2√π`. -/
theorem leb_rhs :
    ∫ x : Rd 1, (Real.exp (-((1 : ℝ) ^ 2 * ‖x‖ ^ 2 / 4)) : ℂ) *
      Complex.exp (-(Complex.I * (inner ℝ (0 : Rd 1) x : ℝ))) =
      ((2 * Real.sqrt Real.pi : ℝ) : ℂ) := by
  rw [← leb_MGamma, MGamma, ← integral_complex_ofReal]
  congr 1; funext x
  simp

/-- The transform without its factor `(r/(2√π))^d` is false. -/
theorem transform_factor_refuted :
    ¬ (∀ (Γ μ : Measure (Rd 1)), IsSpectralMeasure Γ μ → ∀ (y : Rd 1) (r : ℝ), 0 < r →
        ((∫ ξ, Real.exp (-(‖ξ - y‖ ^ 2 / r ^ 2)) ∂μ : ℝ) : ℂ) =
          ∫ x, (Real.exp (-(r ^ 2 * ‖x‖ ^ 2 / 4)) : ℂ) *
            Complex.exp (-(Complex.I * (inner ℝ y x : ℝ))) ∂Γ) := by
  intro h
  have := h volume (Measure.dirac 0) leb_spectral 0 1 one_pos
  rw [leb_rhs] at this
  have h1 : ∫ ξ, Real.exp (-(‖ξ - 0‖ ^ 2 / (1 : ℝ) ^ 2)) ∂(Measure.dirac (0 : Rd 1)) = 1 := by
    rw [integral_dirac]; simp
  rw [h1] at this
  have h2 : (1 : ℝ) = 2 * Real.sqrt Real.pi := by exact_mod_cast this
  have h3 : 1 < Real.sqrt Real.pi := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith [Real.pi_gt_three])
  linarith

/-- The package identity at the same point. -/
theorem transform_factor_contrast :
    ((∫ ξ, Real.exp (-(‖ξ - 0‖ ^ 2 / (1 : ℝ) ^ 2)) ∂(Measure.dirac (0 : Rd 1)) : ℝ) : ℂ) =
      (((1 / (2 * Real.sqrt Real.pi)) ^ 1 : ℝ) : ℂ) *
        ∫ x : Rd 1, (Real.exp (-((1 : ℝ) ^ 2 * ‖x‖ ^ 2 / 4)) : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ (0 : Rd 1) x : ℝ))) :=
  masked_gaussian_transform leb_spectral 0 1 one_pos

end Refutations.MaskedSpectralGrowth
