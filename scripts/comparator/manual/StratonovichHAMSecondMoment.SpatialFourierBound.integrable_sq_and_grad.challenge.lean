namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialFourierBound
open MeasureTheory Set Real Filter Metric
open scoped ContDiff Convolution ENNReal ComplexConjugate
open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure)
-- Statement copied from the source (the printed type writes `ContDiff ℝ (↑⊤)` for the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`)).
-- The section variables used, written as binders: {d : ℕ}.
/-- If g is C^infinity with compact support: x -> g x^2 and x -> norm(fderiv R g x)^2 are integrable. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SpatialFourierBound.integrable_sq_and_grad {d : ℕ} {g : Rd d → ℝ} (hs : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    Integrable (fun x => g x ^ 2) volume ∧ Integrable (fun x => ‖fderiv ℝ g x‖ ^ 2) volume := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialFourierBound
