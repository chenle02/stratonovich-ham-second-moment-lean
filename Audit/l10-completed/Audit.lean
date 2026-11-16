module
import StratonovichHAMSecondMoment.L10Completed
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.L10Completed.spectralPairing_holds
#print axioms StratonovichHAMSecondMoment.L10Completed.spectralPairing_holds
#check @StratonovichHAMSecondMoment.L10Completed.waveGreenFourier_holds
#print axioms StratonovichHAMSecondMoment.L10Completed.waveGreenFourier_holds
#check @StratonovichHAMSecondMoment.L10Completed.alpha_one_convolution_completed
#print axioms StratonovichHAMSecondMoment.L10Completed.alpha_one_convolution_completed
#check @StratonovichHAMSecondMoment.L10Completed.alpha_one_convolution_paper_completed
#print axioms StratonovichHAMSecondMoment.L10Completed.alpha_one_convolution_paper_completed

namespace StratonovichHAMSecondMoment.Audit.L10Completed

open StratonovichHAMSecondMoment

/-- Consumer: under `H:homog` with `α = 1` alone, the smoothed pairing is bounded by `πV/2`
for `h = ε = η = 1`, `z = 0`, with no supplied input. -/
private theorem audit_consumer {d : ℕ} {alpha0 : ℝ}
    {Γ μ : MeasureTheory.Measure (HomogHypothesis.Rd d)}
    (hH : HomogHypothesis.HomogCovariance d 1 alpha0 Γ μ) :
    ∫ y, VariationalDilation.conv Γ (VariationalMean.heatK 1) (y + 0)
        ∂(LowAlphaConvolution.smoothedGreen (WaveGreen.waveGreen d) 1 1) ≤
      Real.pi * (μ (Metric.closedBall 0 1)).toReal / 2 :=
  ((L10Completed.alpha_one_convolution_paper_completed hH).2 1 one_pos 1 one_pos 1
    zero_le_one 0).2.2.2.2.2

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.L10Completed
