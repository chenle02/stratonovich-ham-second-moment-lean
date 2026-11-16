namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal Pointwise Topology FourierTransform InnerProductSpace
open HomogHypothesis (Rd IsTempered IsEven IsPosDefDistr IsSpectralMeasure)
open VariationalMean (heatK)
variable {n : ℕ}
/-- For g measurable on R^n: hconv (volume.withDensity g) eps z = HigherRieszTwo.smoothCov g eps z. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.EndpointLemmas.hconv_withDensity_eq_smoothCov {g : Rd n → ℝ≥0∞} (hg : Measurable g) (ε : ℝ)
    (z : Rd n) :
    hconv ((volume : Measure (Rd n)).withDensity g) ε z = HigherRieszTwo.smoothCov g ε z := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.EndpointLemmas.hconv_withDensity_eq_smoothCov
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas
