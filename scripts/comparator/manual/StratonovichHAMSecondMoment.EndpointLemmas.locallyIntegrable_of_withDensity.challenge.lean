namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal Pointwise Topology FourierTransform InnerProductSpace
open HomogHypothesis (Rd IsTempered IsEven IsPosDefDistr IsSpectralMeasure)
open VariationalMean (heatK)
variable {n : ℕ}
/-- For f : R^n -> R measurable, f >= 0, with volume.withDensity (ofReal o f) locally finite: f is locally integrable. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.EndpointLemmas.locallyIntegrable_of_withDensity {f : Rd n → ℝ} (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x)
    (hlf : IsLocallyFiniteMeasure ((volume : Measure (Rd n)).withDensity
      fun x => ENNReal.ofReal (f x))) : LocallyIntegrable f := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas
