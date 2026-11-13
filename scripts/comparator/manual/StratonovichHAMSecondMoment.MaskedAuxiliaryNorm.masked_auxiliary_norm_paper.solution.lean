namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryNorm
open MeasureTheory Real Metric
open scoped ENNReal NNReal FourierTransform
open StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpectralHomog StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedSpectralGrowth
-- Statement copied from the source (the printed type round-trips only up to definitional equality (`Rd d` printed as `WithLp 2 ..`)).
-- The section variables used, written as binders: {d : ℕ}.
/-- Under HomogCovariance d alpha alpha0 Gamma mu, Gamma != 0, a real Schwartz zeta != 0, H a separable complex Hilbert space and F : R^d -> H Schwartz: the conclusions of masked_auxiliary_norm (for every R > 0). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MaskedAuxiliaryNorm.masked_auxiliary_norm_paper {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) (_hΓ : Γ ≠ 0) (ζ : SchwartzMap (Rd d) ℝ)
    (hζ : ζ ≠ 0) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (F : SchwartzMap (Rd d) H) :
    (Integrable (paperHat (fun x => (ζ x : ℂ))) ∧ 0 < Lz ζ) ∧
      ∀ R : ℝ, 0 < R →
        (Integrable (kR ζ R) ∧ ∫ u, ‖kR ζ R u‖ = Lz ζ) ∧
        IsEven (nu μ ζ R) ∧ IsTempered (nu μ ζ R) ∧ IsLocallyFiniteMeasure (nu μ ζ R) ∧
        (∀ y : Rd d, ∀ r : ℝ, 0 < r →
          nu μ ζ R (ball y r) ≤ ENNReal.ofReal (cd d ^ 2 * Lz ζ ^ 2 * CGamma Γ * r ^ alpha) ∧
          nu μ ζ R (closedBall y r) ≤
            ENNReal.ofReal (cd d ^ 2 * Lz ζ ^ 2 * CGamma Γ * r ^ alpha)) ∧
        (Integrable (fun ξ => ‖paperHat (fun x => (zetaR ζ R x : ℂ) • F x) ξ‖ ^ 2) μ ∧
          Integrable (fun η => ‖paperHat (F : Rd d → H) η‖ ^ 2) (nu μ ζ R) ∧
          ∫⁻ ξ, ‖paperHat (fun x => (zetaR ζ R x : ℂ) • F x) ξ‖ₑ ^ 2 ∂μ ≤
            ∫⁻ η, ‖paperHat (F : Rd d → H) η‖ₑ ^ 2 ∂nu μ ζ R ∧
          ∫⁻ η, ‖paperHat (F : Rd d → H) η‖ₑ ^ 2 ∂nu μ ζ R < ⊤ ∧
          ∫ ξ, ‖paperHat (fun x => (zetaR ζ R x : ℂ) • F x) ξ‖ ^ 2 ∂μ ≤
            ∫ η, ‖paperHat (F : Rd d → H) η‖ ^ 2 ∂nu μ ζ R) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.MaskedAuxiliaryNorm.masked_auxiliary_norm_paper
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryNorm
