namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal Pointwise Topology FourierTransform InnerProductSpace
open HomogHypothesis (Rd IsTempered IsEven IsPosDefDistr IsSpectralMeasure)
open VariationalMean (heatK)
variable {n : ℕ}
/-- For f measurable on R^n with f(r x) = ofReal(r^(-s)) f x for all r > 0 and x: Scaling (volume.withDensity f) (n - s). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.EndpointLemmas.scaling_withDensity {f : Rd n → ℝ≥0∞} (hf : Measurable f) {s : ℝ}
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, f (r • x) = ENNReal.ofReal (r ^ (-s)) * f x) :
    Scaling ((volume : Measure (Rd n)).withDensity f) (n - s) := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.EndpointLemmas.scaling_withDensity
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas
