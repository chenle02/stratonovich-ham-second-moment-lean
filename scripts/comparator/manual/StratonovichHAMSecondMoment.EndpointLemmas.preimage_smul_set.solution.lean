namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal Pointwise Topology FourierTransform InnerProductSpace
open HomogHypothesis (Rd IsTempered IsEven IsPosDefDistr IsSpectralMeasure)
open VariationalMean (heatK)
variable {n : ℕ}
/-- For a linear equivalence T of R^n and r != 0: T^(-1)(r A) = r T^(-1)(A). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.EndpointLemmas.preimage_smul_set (T : Rd n ≃L[ℝ] Rd n) {r : ℝ} (hr : r ≠ 0) (A : Set (Rd n)) :
    T ⁻¹' (r • A) = r • (T ⁻¹' A) := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.EndpointLemmas.preimage_smul_set
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas
