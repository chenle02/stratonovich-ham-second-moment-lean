/-
Refutation for the sphere Fourier identity of `WaveGreenFourier`, package
theorem `StratonovichHAMSecondMoment.WaveGreenFourier.sphere_fourier`
(`∫_{S²} e^{iξ·ω} σ(dω) = 4π sinc|ξ|`, the `d = 3` core of the Fourier identity
at main TeX lines 777-778 and 4741).

Wrong variant: the constant `2π` in place of `4π`, i.e.
`∫_{S²} e^{iξ·ω} σ(dω) = 2π sinc|ξ|` for every `ξ`.  Counterexample: `ξ = 0`,
where the package value is `4π` (the total mass of `σ`) and `4π ≠ 2π`.
`sphere_constant_contrast` is the package identity at `ξ = 0`.
No junk-value reliance (`sinc 0 = 1` is the genuine limit value).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.WaveGreenFourier

set_option autoImplicit false

open MeasureTheory Real

namespace Refutations.WaveGreenFourier

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.HomogHypothesis
  StratonovichHAMSecondMoment.WaveGreenFourier

/-- The constant `2π` in the sphere Fourier identity is false. -/
theorem sphere_constant_refuted :
    ¬ (∀ ξ : Rd 3, ∫ ω : Metric.sphere (0 : Rd 3) 1,
        Complex.exp (Complex.I * ((inner ℝ ξ (ω : Rd 3) : ℝ) : ℂ))
          ∂(volume : Measure (Rd 3)).toSphere = ((2 * π * Real.sinc ‖ξ‖ : ℝ) : ℂ)) := by
  intro h
  have h1 := h 0
  rw [(sphere_fourier 0).2] at h1
  have h2 : (4 * π * Real.sinc ‖(0 : Rd 3)‖ : ℝ) = 2 * π * Real.sinc ‖(0 : Rd 3)‖ :=
    Complex.ofReal_injective h1
  simp only [norm_zero, Real.sinc_zero, mul_one] at h2
  linarith [Real.pi_pos]

/-- The package identity at `ξ = 0`: the value is `4π`. -/
theorem sphere_constant_contrast :
    ∫ ω : Metric.sphere (0 : Rd 3) 1,
        Complex.exp (Complex.I * ((inner ℝ (0 : Rd 3) (ω : Rd 3) : ℝ) : ℂ))
          ∂(volume : Measure (Rd 3)).toSphere = ((4 * π : ℝ) : ℂ) := by
  rw [(sphere_fourier 0).2]; simp

end Refutations.WaveGreenFourier
