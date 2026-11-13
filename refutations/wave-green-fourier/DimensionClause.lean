/-
Refutation for the Fourier input of `DampedMultiplier` discharged in
`WaveGreenFourier`, package theorem
`StratonovichHAMSecondMoment.WaveGreenFourier.greenFourier`
(`GreenFourier (waveGreen d)` for `d ∈ {1,2,3}`).

Wrong variant: the dimension clause dropped, `GreenFourier (waveGreen d)` for
every `d`.  Counterexample: `d = 4`, where `waveGreen 4 s` is the zero measure
(the package convention outside `d ∈ {1,2,3}`; the manuscript has `d ≤ 3`), so
its characteristic function at `ξ = 0` is `0`, while `waveHat 1 0 = 1`.  This
relies on that convention; it records that the clause `d ∈ {1,2,3}` (from
`H:homog`) is needed.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.WaveGreenFourier

set_option autoImplicit false

open MeasureTheory Real

namespace Refutations.WaveGreenFourier

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.HomogHypothesis
  StratonovichHAMSecondMoment.WaveGreen StratonovichHAMSecondMoment.DampedMultiplier

/-- `GreenFourier (waveGreen d)` fails for `d = 4`. -/
theorem dimension_clause_refuted : ¬ (∀ d : ℕ, GreenFourier (waveGreen d)) := by
  intro h
  have h1 := (h 4).fourier 1 one_pos 0
  rw [waveGreen_other 4 (by norm_num) (by norm_num) (by norm_num) 1] at h1
  simp [WaveKernel.waveHat, MeasureTheory.charFun_apply] at h1

end Refutations.WaveGreenFourier
