namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal Pointwise Topology FourierTransform InnerProductSpace
open HomogHypothesis (Rd IsTempered IsEven IsPosDefDistr IsSpectralMeasure)
open VariationalMean (heatK)
variable {n : ℕ}
/-- planeMeasure c 0 = ofReal c * (volume on R^2).map planeEmb (the low endpoint c m). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.EndpointLemmas.planeMeasure_zero (c : ℝ) :
    planeMeasure c 0 = ENNReal.ofReal c • (volume : Measure (Rd 2)).map planeEmb := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.EndpointLemmas.planeMeasure_zero
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas
