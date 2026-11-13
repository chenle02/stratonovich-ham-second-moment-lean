namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryNorm
open MeasureTheory Real Metric
open scoped ENNReal NNReal FourierTransform
open StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpectralHomog StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedSpectralGrowth
-- Statement copied from the source (the printed type does not round-trip syntactically).
-- The section variables used, written as binders: {d : ℕ} {μ : Measure (Rd d)} {ζ : SchwartzMap (Rd d) ℝ} {R : ℝ}.
/-- For mu s-finite, R != 0 and measurable w : R^d -> [0, inf]: lintegral of w d(nu mu zeta R) = ofReal(cd d^2 * Lz zeta) * lintegral over mu(dxi) of lintegral over d eta of w eta * enorm(kR zeta R (xi - eta)). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MaskedAuxiliaryNorm.lintegral_nu {d : ℕ} {μ : Measure (Rd d)} {ζ : SchwartzMap (Rd d) ℝ} {R : ℝ} [SFinite μ] (hR : R ≠ 0) {w : Rd d → ℝ≥0∞} (hw : Measurable w) :
    ∫⁻ η, w η ∂nu μ ζ R = ENNReal.ofReal (cd d ^ 2 * Lz ζ) *
      ∫⁻ ξ, ∫⁻ η, w η * ‖kR ζ R (ξ - η)‖ₑ ∂volume ∂μ := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryNorm
