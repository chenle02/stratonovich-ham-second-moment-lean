namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialFourierBound
open MeasureTheory Set Real Filter Metric
open scoped ContDiff Convolution ENNReal ComplexConjugate
open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure)
-- Statement copied from the source (the printed type writes `ContDiff ℝ (↑⊤)` for the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`)).
-- The section variables used, written as binders: {d : ℕ}.
/-- If Q is C^infinity with compact support, autocorr Q is C^infinity. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SpatialFourierBound.autocorr_contDiff {d : ℕ} {Q : Rd d → ℝ} (hQ : ContDiff ℝ ∞ Q) (hc : HasCompactSupport Q) :
    ContDiff ℝ ∞ (autocorr Q) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialFourierBound
