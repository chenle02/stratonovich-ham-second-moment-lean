module
import StratonovichHAMSecondMoment.WaveKernel
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.WaveKernel.waveHat
#print axioms StratonovichHAMSecondMoment.WaveKernel.waveHat
#check @StratonovichHAMSecondMoment.WaveKernel.waveHat_continuous
#print axioms StratonovichHAMSecondMoment.WaveKernel.waveHat_continuous
#check @StratonovichHAMSecondMoment.WaveKernel.waveHat_zero
#print axioms StratonovichHAMSecondMoment.WaveKernel.waveHat_zero
#check @StratonovichHAMSecondMoment.WaveKernel.waveHat_of_ne_zero
#print axioms StratonovichHAMSecondMoment.WaveKernel.waveHat_of_ne_zero
#check @StratonovichHAMSecondMoment.WaveKernel.abs_waveHat_le
#print axioms StratonovichHAMSecondMoment.WaveKernel.abs_waveHat_le
#check @StratonovichHAMSecondMoment.WaveKernel.abs_waveHat_le_inv
#print axioms StratonovichHAMSecondMoment.WaveKernel.abs_waveHat_le_inv
#check @StratonovichHAMSecondMoment.WaveKernel.abs_waveHat_le_min
#print axioms StratonovichHAMSecondMoment.WaveKernel.abs_waveHat_le_min
#check @StratonovichHAMSecondMoment.WaveKernel.waveHat_scaling
#print axioms StratonovichHAMSecondMoment.WaveKernel.waveHat_scaling
#check @StratonovichHAMSecondMoment.WaveKernel.abs_waveHat_mul_le
#print axioms StratonovichHAMSecondMoment.WaveKernel.abs_waveHat_mul_le
#check @StratonovichHAMSecondMoment.WaveKernel.waveHat_laplace
#print axioms StratonovichHAMSecondMoment.WaveKernel.waveHat_laplace
open MeasureTheory Set in
/-- Consumer: the wave Laplace transform at `ξ = 0` is `a⁻²`, and the kernel
there is the time variable. -/
private theorem wave_laplace_consumer (a : ℝ) (ha : 0 < a) :
    ∫ s in Ioi (0 : ℝ), Real.exp (-(a * s)) *
        StratonovichHAMSecondMoment.WaveKernel.waveHat s
          (0 : StratonovichHAMSecondMoment.HomogHypothesis.Rd 1) = 1 / a ^ 2 := by
  rw [(StratonovichHAMSecondMoment.WaveKernel.waveHat_laplace a ha _).2]
  simp
#check @wave_laplace_consumer
#print axioms wave_laplace_consumer
example : StratonovichHAMSecondMoment.WaveKernel.waveHat (2 : ℝ)
    (0 : StratonovichHAMSecondMoment.HomogHypothesis.Rd 1) = 2 :=
  StratonovichHAMSecondMoment.WaveKernel.waveHat_zero 2
