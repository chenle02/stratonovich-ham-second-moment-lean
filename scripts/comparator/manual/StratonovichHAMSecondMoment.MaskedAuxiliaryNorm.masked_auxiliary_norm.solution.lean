namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryNorm
open MeasureTheory Real Metric
open scoped ENNReal NNReal FourierTransform
open StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpectralHomog StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedSpectralGrowth
-- Statement copied from the source (the printed type round-trips only up to definitional equality (`Rd d` printed as `WithLp 2 ..`)).
-- The section variables used, written as binders: {d : ℕ}.
/-- If mu is s-finite, tempered, even, IsSpectralMeasure Gamma mu, SpectralHomogeneous Gamma (d-alpha), zeta != 0, E complex Banach, F Schwartz: zeta-hat integrable, Lz > 0; for R > 0: norm(k_R)_1 = Lz, nu_R even, tempered, locally finite, both ball bounds, masked_hilbert_fourier. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MaskedAuxiliaryNorm.masked_auxiliary_norm {d : ℕ} {Γ μ : Measure (Rd d)} {alpha : ℝ} [SFinite μ]
    (hμt : IsTempered μ) (hμe : IsEven μ) (hsp : IsSpectralMeasure Γ μ)
    (hΓs : SpectralHomogeneous Γ ((d : ℝ) - alpha)) (ζ : SchwartzMap (Rd d) ℝ) (hζ : ζ ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (F : SchwartzMap (Rd d) E) :
    (Integrable (paperHat (fun x => (ζ x : ℂ))) ∧ 0 < Lz ζ) ∧
      ∀ R : ℝ, 0 < R →
        (Integrable (kR ζ R) ∧ ∫ u, ‖kR ζ R u‖ = Lz ζ) ∧
        IsEven (nu μ ζ R) ∧ IsTempered (nu μ ζ R) ∧ IsLocallyFiniteMeasure (nu μ ζ R) ∧
        (∀ y : Rd d, ∀ r : ℝ, 0 < r →
          nu μ ζ R (ball y r) ≤ ENNReal.ofReal (cd d ^ 2 * Lz ζ ^ 2 * CGamma Γ * r ^ alpha) ∧
          nu μ ζ R (closedBall y r) ≤
            ENNReal.ofReal (cd d ^ 2 * Lz ζ ^ 2 * CGamma Γ * r ^ alpha)) ∧
        (Integrable (fun ξ => ‖paperHat (fun x => (zetaR ζ R x : ℂ) • F x) ξ‖ ^ 2) μ ∧
          Integrable (fun η => ‖paperHat (F : Rd d → E) η‖ ^ 2) (nu μ ζ R) ∧
          ∫⁻ ξ, ‖paperHat (fun x => (zetaR ζ R x : ℂ) • F x) ξ‖ₑ ^ 2 ∂μ ≤
            ∫⁻ η, ‖paperHat (F : Rd d → E) η‖ₑ ^ 2 ∂nu μ ζ R ∧
          ∫⁻ η, ‖paperHat (F : Rd d → E) η‖ₑ ^ 2 ∂nu μ ζ R < ⊤ ∧
          ∫ ξ, ‖paperHat (fun x => (zetaR ζ R x : ℂ) • F x) ξ‖ ^ 2 ∂μ ≤
            ∫ η, ‖paperHat (F : Rd d → E) η‖ ^ 2 ∂nu μ ζ R) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.MaskedAuxiliaryNorm.masked_auxiliary_norm
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryNorm
