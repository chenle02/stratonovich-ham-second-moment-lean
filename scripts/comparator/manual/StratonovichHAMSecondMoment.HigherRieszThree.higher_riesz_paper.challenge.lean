namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HigherRieszThree
open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal Topology
open HomogHypothesis (Rd HomogCovariance)
open VariationalMean (heatK)
open WaveGreen (waveGreen)
open HigherRieszTwo
-- Statement copied from the source (the printed type elaborates the measurable space on `Rd d` as `WithLp.measurableSpace`, the declaration through `MeasureSpace.toMeasurableSpace`).
/-- Under HomogCovariance d alpha alpha0 (volume.withDensity (riesz c alpha)) mu, d in {2,3}, c > 0, 1 < alpha, alpha < 3/2 if d = 2: SpatialMaximum d (riesz c alpha) (alpha - 1) (Md d c alpha); if d = 3, Md d c alpha <= M for every admissible M. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.HigherRieszThree.higher_riesz_paper {d : ℕ} {c α α₀ : ℝ} {μ : Measure (Rd d)}
    (hH : HomogCovariance d α α₀ (volume.withDensity (riesz c α)) μ) (hd : d = 2 ∨ d = 3)
    (hc : 0 < c) (hα1 : 1 < α) (hα2 : d = 2 → α < 3 / 2) :
    SpatialMaximum d (riesz c α) (α - 1) (Md d c α) ∧
      (d = 3 → ∀ M : ℝ, SpatialMaximum d (riesz c α) (α - 1) M → Md d c α ≤ M) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HigherRieszThree
