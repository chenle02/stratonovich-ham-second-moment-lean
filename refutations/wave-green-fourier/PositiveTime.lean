/-
Refutation for the unified Fourier identity of `WaveGreenFourier`, package
theorem `StratonovichHAMSecondMoment.WaveGreenFourier.waveGreen_fourier`
(`∫ e^{iξ·x} G_s(dx) = waveHat s ξ` for `d ∈ {1,2,3}` and `s > 0`).

Wrong variant: the identity with `s > 0` dropped (all real `s`).
Counterexample: `d = 3`, `s = -1`, `ξ = 0`.  The measure `waveGreen 3 (-1)` is
zero (`WaveGreen.waveGreen_of_nonpos`), so the integral is `0`, while
`waveHat (-1) 0 = -1 · sinc 0 = -1`.  This relies on the package convention that
`waveGreen d s = 0` for `s ≤ 0` (the manuscript has `s ≥ 0` only); the
refutation shows that the hypothesis `s > 0` is needed for the statement as
written, not a property of the TeX's measures.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.WaveGreenFourier

set_option autoImplicit false

open MeasureTheory Real

namespace Refutations.WaveGreenFourier

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.HomogHypothesis
  StratonovichHAMSecondMoment.WaveGreen StratonovichHAMSecondMoment.WaveGreenFourier

/-- Dropping `s > 0` from the Fourier identity is false. -/
theorem positive_time_refuted :
    ¬ (∀ s : ℝ, ∀ ξ : Rd 3,
        ∫ x, Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)) ∂(waveGreen 3 s) =
          (WaveKernel.waveHat s ξ : ℂ)) := by
  intro h
  have h1 := h (-1) 0
  rw [waveGreen_of_nonpos 3 (-1) (by norm_num)] at h1
  simp [WaveKernel.waveHat] at h1

end Refutations.WaveGreenFourier
