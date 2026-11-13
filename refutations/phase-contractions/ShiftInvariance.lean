/-
Refutation for the Gaussian Fourier pairing step of `L:phase-contractions`
(main TeX lines 2090-2098 at a284420), package theorem
`StratonovichHAMSecondMoment.PhaseContractions.gauss_shift_le`.

Wrong variant: the comparison is an equality (shift invariance of the
Gaussian weighting of the spectral measure), i.e. for every pair with the
spectral convention, `∫ e^{-s|q+ξ|²} μ(dξ) = ∫ e^{-s|ξ|²} μ(dξ)`.
Counterexample: `d = 1`, `Γ` = Lebesgue measure, `μ = δ_0` (the spectral
convention holds), `s = 1`, `|q| = 1`: the left side is `e^{-1}`, the right
side `1`.  `shift_invariance_contrast` is the package inequality at the same
point (`e^{-1} ≤ 1`).  No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.PhaseContractions

set_option autoImplicit false

open MeasureTheory Real
open StratonovichHAMSecondMoment HomogHypothesis PhaseContractions

namespace Refutations.PhaseContractions

/-- Lebesgue measure on `ℝ¹` has spectral measure `δ_0`. -/
theorem leb_spectral : IsSpectralMeasure (volume : Measure (Rd 1)) (Measure.dirac 0) := by
  intro φ
  rw [integral_dirac]
  simp

/-- A unit vector of `ℝ¹`. -/
theorem exists_unit : ∃ q : Rd 1, ‖q‖ = 1 := exists_norm_eq (Rd 1) zero_le_one

/-- Shift invariance of the Gaussian-weighted spectral mass is false. -/
theorem shift_invariance_refuted :
    ¬ (∀ (Γ μ : Measure (Rd 1)), IsSpectralMeasure Γ μ → ∀ s : ℝ, 0 < s → ∀ q : Rd 1,
        ∫ ξ, Real.exp (-(s * ‖q + ξ‖ ^ 2)) ∂μ = ∫ ξ, Real.exp (-(s * ‖ξ‖ ^ 2)) ∂μ) := by
  intro h
  obtain ⟨q, hq⟩ := exists_unit
  have h1 := h volume (Measure.dirac 0) leb_spectral 1 one_pos q
  rw [integral_dirac, integral_dirac] at h1
  simp only [add_zero, hq, norm_zero] at h1
  norm_num at h1

/-- The package inequality at the same point. -/
theorem shift_invariance_contrast (q : Rd 1) :
    ∫ ξ, Real.exp (-(1 * ‖q + ξ‖ ^ 2)) ∂(Measure.dirac (0 : Rd 1)) ≤
      ∫ ξ, Real.exp (-(1 * ‖ξ‖ ^ 2)) ∂(Measure.dirac (0 : Rd 1)) :=
  gauss_shift_le leb_spectral 1 one_pos q

end Refutations.PhaseContractions
