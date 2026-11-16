namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal Pointwise Topology FourierTransform InnerProductSpace
open HomogHypothesis (Rd IsTempered IsEven IsPosDefDistr IsSpectralMeasure)
open VariationalMean (heatK)
variable {n : ℕ}
/-- For c >= 0 and 0 <= e j < 1: gamma_e dx is locally finite, even, tempered, gamma_e is locally integrable, and Scaling (gamma_e dx) (n - sum_j e j). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.EndpointLemmas.prodRiesz_props {c : ℝ} (hc : 0 ≤ c) {e : Fin n → ℝ}
    (he : ∀ j, 0 ≤ e j ∧ e j < 1) :
    IsLocallyFiniteMeasure (prodRieszMeasure c e) ∧ IsEven (prodRieszMeasure c e) ∧
      IsTempered (prodRieszMeasure c e) ∧ LocallyIntegrable (prodRieszReal c e) ∧
      Scaling (prodRieszMeasure c e) (n - ∑ j, e j) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas
