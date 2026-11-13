namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialFourierBound
open MeasureTheory Set Real Filter Metric
open scoped ContDiff Convolution ENNReal ComplexConjugate
open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure)
-- Statement copied from the source (the printed type writes `ContDiff ℝ (↑⊤)` for the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`)).
-- The section variables used, written as binders: {d : ℕ}.
/-- If IsSpectralMeasure Gamma mu and Q is C^infinity with compact support: integral of autocorr Q over Gamma = integral of norm(fourierQ Q xi)^2 over mu (Bochner integrals; no integrability asserted). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SpatialFourierBound.integral_autocorr_eq_spectral {d : ℕ} {Γ μ : Measure (Rd d)} (hsp : IsSpectralMeasure Γ μ)
    {Q : Rd d → ℝ} (hQ : ContDiff ℝ ∞ Q) (hc : HasCompactSupport Q) :
    ∫ y, autocorr Q y ∂Γ = ∫ ξ, ‖fourierQ Q ξ‖ ^ 2 ∂μ := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialFourierBound
