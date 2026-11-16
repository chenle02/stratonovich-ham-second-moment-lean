namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HigherRieszThree
open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal Topology
open HomogHypothesis (Rd HomogCovariance)
open VariationalMean (heatK)
open WaveGreen (waveGreen)
open HigherRieszTwo
-- Statement copied from the source (the printed type elaborates the measurable space on `Rd d` as `WithLp.measurableSpace`, the declaration through `MeasureSpace.toMeasurableSpace`).
/-- Under HomogCovariance 3 alpha alpha0 (volume.withDensity (riesz c alpha)) mu, c > 0, 1 < alpha: SpatialMaximum 3 (riesz c alpha) (alpha - 1) (M3 c alpha), and M3 c alpha <= M for every admissible M. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.HigherRieszThree.higher_riesz_three_paper {c α α₀ : ℝ} {μ : Measure (Rd 3)}
    (hH : HomogCovariance 3 α α₀ (volume.withDensity (riesz c α)) μ) (hc : 0 < c)
    (hα1 : 1 < α) :
    SpatialMaximum 3 (riesz c α) (α - 1) (M3 c α) ∧
      ∀ M : ℝ, SpatialMaximum 3 (riesz c α) (α - 1) M → M3 c α ≤ M := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HigherRieszThree
