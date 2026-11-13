namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveGreenFourier
open MeasureTheory Set Real Metric Filter ProbabilityTheory
open scoped ENNReal NNReal Pointwise Topology
open HomogHypothesis TimeFractional WaveKernel DampedNorms DampedNormsHomog WaveGreen
-- Statement copied from the source (the printed type elaborates the measurable space on `ℝ` as `Real.measurableSpace`, the declaration through `MeasureSpace.toMeasurableSpace`).
/-- For e in R^3 with |e| = 1: the image of volume.toSphere under omega -> <e,omega> is ofReal(2 pi) times Lebesgue measure restricted to [-1, 1]. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.WaveGreenFourier.archimedes (e : Rd 3) (he : ‖e‖ = 1) :
    ((volume : Measure (Rd 3)).toSphere).map
        (fun ω : sphere (0 : Rd 3) 1 => inner ℝ e (ω : Rd 3)) =
      ENNReal.ofReal (2 * π) • (volume : Measure ℝ).restrict (Icc (-1) 1) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveGreenFourier
