namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal Pointwise Topology FourierTransform InnerProductSpace
open HomogHypothesis (Rd IsTempered IsEven IsPosDefDistr IsSpectralMeasure)
open VariationalMean (heatK)
variable {n : ℕ}
/-- For a linear map f : R^m -> R^n and r != 0: f^(-1)(r A) = r f^(-1)(A). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.EndpointLemmas.preimage_smul_set_linear {m : ℕ} (f : Rd m →ₗ[ℝ] Rd n) {r : ℝ} (hr : r ≠ 0)
    (A : Set (Rd n)) : f ⁻¹' (r • A) = r • (f ⁻¹' A) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas
