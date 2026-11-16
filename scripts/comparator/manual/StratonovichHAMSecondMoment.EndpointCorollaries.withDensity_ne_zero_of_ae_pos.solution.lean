namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointCorollaries
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal Pointwise Topology
open HomogHypothesis (Rd IsTempered IsEven IsPosDefDistr IsSpectralMeasure)
open EndpointLemmas
open HigherRieszTwo (riesz)
/-- For f measurable on R^m with 0 < f x for almost every x: volume.withDensity f is nonzero. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.EndpointCorollaries.withDensity_ne_zero_of_ae_pos {m : ℕ} {f : Rd m → ℝ≥0∞} (hf : Measurable f)
    (hpos : ∀ᵐ x ∂(volume : Measure (Rd m)), 0 < f x) :
    (volume : Measure (Rd m)).withDensity f ≠ 0 := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.EndpointCorollaries.withDensity_ne_zero_of_ae_pos
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointCorollaries
