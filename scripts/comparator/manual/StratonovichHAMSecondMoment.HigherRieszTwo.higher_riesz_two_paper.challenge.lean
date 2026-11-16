namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HigherRieszTwo
open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal Pointwise Topology
open HomogHypothesis (Rd HomogCovariance)
open VariationalMean (heatK)
open WaveGreen (waveGreen)
-- Statement copied from the source (the printed type elaborates the measurable space on `Rd d` as `WithLp.measurableSpace`, the declaration through `MeasureSpace.toMeasurableSpace`).
-- The section variables of the source, as there:
variable {d : ℕ}
/-- Under HomogCovariance 2 alpha alpha0 (volume.withDensity (riesz c alpha)) mu (carried, unused), c > 0, 1 < alpha < 3/2: SpatialMaximum 2 (riesz c alpha) (alpha - 1) (M2 c alpha). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.HigherRieszTwo.higher_riesz_two_paper {c α α₀ : ℝ} {μ : Measure (Rd 2)}
    (_hH : HomogCovariance 2 α α₀ (volume.withDensity (riesz c α)) μ) (hc : 0 < c)
    (hα1 : 1 < α) (hα : α < 3 / 2) :
    SpatialMaximum 2 (riesz c α) (α - 1) (M2 c α) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HigherRieszTwo
