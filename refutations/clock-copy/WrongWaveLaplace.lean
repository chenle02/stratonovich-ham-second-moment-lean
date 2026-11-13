import StratonovichHAMSecondMoment.WaveKernel

/-!
Refutation for `StratonovichHAMSecondMoment.WaveKernel.waveHat_laplace`
(the elementary wave Laplace transform, main TeX lines 794-795):
`∫_0^∞ e^{-as} Ĝ_s(ξ) ds = (a²+|ξ|²)⁻¹`.

Wrong variant: the value `(a+|ξ|)⁻²` (the transform of `s e^{-|ξ|s}`-type
kernels), same binders and hypotheses. Witness: `d = 1`, `a = 1`, `ξ = e₀`
(`|ξ| = 1`): the package value is `1/2`, the wrong value `1/4`. No junk value
is used (the package states integrability).
The contrast theorem applies the package theorem at the witness.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory Set

namespace Refutations.WaveKernel

open StratonovichHAMSecondMoment.HomogHypothesis StratonovichHAMSecondMoment.WaveKernel

/-- The unit vector `e₀` of `ℝ¹` (a test point, not a package definition). -/
noncomputable def e0 : Rd 1 := EuclideanSpace.single 0 1

theorem norm_e0 : ‖e0‖ = 1 := by simp [e0]

/-- Contrast: at the witness, `(a+|ξ|)⁻² < ∫ e^{-as} Ĝ_s(ξ) ds`. -/
theorem wave_laplace_contrast :
    1 / (1 + ‖e0‖) ^ 2 < ∫ s in Ioi (0 : ℝ), Real.exp (-(1 * s)) * waveHat s e0 := by
  rw [(waveHat_laplace 1 one_pos e0).2, norm_e0]
  norm_num

/-- The wrong value `(a+|ξ|)⁻²` is false. -/
theorem wave_laplace_wrong :
    ¬ (∀ (d : ℕ) (a : ℝ), 0 < a → ∀ ξ : Rd d,
      ∫ s in Ioi (0 : ℝ), Real.exp (-(a * s)) * waveHat s ξ = 1 / (a + ‖ξ‖) ^ 2) := by
  intro h
  have := wave_laplace_contrast
  rw [h 1 1 one_pos e0] at this
  exact lt_irrefl _ this

end Refutations.WaveKernel
