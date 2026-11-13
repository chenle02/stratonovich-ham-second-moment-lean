/-
Refutation for the `d = 2` Fourier identity of `WaveGreenFourier`, package
theorem `StratonovichHAMSecondMoment.WaveGreenFourier.waveGreen_fourier_two`
(`∫ e^{iξ·x} G_s(dx) = s sinc(s|ξ|) = sin(s|ξ|)/|ξ|`, main TeX lines 777-778,
4741).

Wrong variant: `Ĝ_s(ξ) = s cos(s|ξ|)` (the transform of the time derivative of
the `d = 1` kernel, a plausible confusion).  Counterexample: `s = 1`, `ξ = π e₀`,
where the package value is `sinc π = 0` while `cos π = -1`.
`cosine_variant_contrast` is the package identity at that point.
No junk-value reliance (`s > 0`, `ξ ≠ 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.WaveGreenFourier

set_option autoImplicit false

open MeasureTheory Real

namespace Refutations.WaveGreenFourier

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.HomogHypothesis
  StratonovichHAMSecondMoment.WaveGreen StratonovichHAMSecondMoment.WaveGreenFourier

/-- The point `π e₀ ∈ ℝ²`. -/
theorem norm_pi_single : ‖EuclideanSpace.single (0 : Fin 2) π‖ = π := by
  simp [abs_of_pos Real.pi_pos]

/-- `Ĝ_s(ξ) = s cos(s|ξ|)` is false in `d = 2`. -/
theorem cosine_variant_refuted :
    ¬ (∀ s : ℝ, 0 < s → ∀ ξ : Rd 2,
        ∫ x, Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)) ∂(waveGreen 2 s) =
          ((s * Real.cos (s * ‖ξ‖) : ℝ) : ℂ)) := by
  intro h
  have h1 := h 1 one_pos (EuclideanSpace.single 0 π)
  rw [(waveGreen_fourier_two 1 one_pos _).2] at h1
  have h2 := Complex.ofReal_injective h1
  simp only [WaveKernel.waveHat, norm_pi_single, one_mul,
    Real.sinc_of_ne_zero Real.pi_pos.ne', Real.sin_pi, zero_div, Real.cos_pi] at h2
  norm_num at h2

/-- The package value at `s = 1`, `ξ = π e₀`: `sinc π = 0`. -/
theorem cosine_variant_contrast :
    ∫ x, Complex.exp (Complex.I * ((inner ℝ (EuclideanSpace.single (0 : Fin 2) π) x : ℝ) : ℂ))
        ∂(waveGreen 2 1) = 0 := by
  rw [(waveGreen_fourier_two 1 one_pos _).2]
  simp [WaveKernel.waveHat, Real.sinc_of_ne_zero Real.pi_pos.ne']

end Refutations.WaveGreenFourier
