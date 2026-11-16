namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Real Metric
open scoped ENNReal NNReal ComplexConjugate
open HomogHypothesis SpectralHomog MaskedSpectralGrowth MaskedAuxiliaryNorm
open Cx
/-- mu s-finite, tempered, even, IsSpectralMeasure Gamma mu, SpectralHomogeneous Gamma (d - alpha), zeta != 0 real Schwartz, H complete real inner product space, F Schwartz: Cx H complete, iota isometric, the norm and transform identities, and masked_auxiliary_norm for cxS F. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.masked_auxiliary_norm_real {d : ℕ} {Γ μ : Measure (Rd d)} {alpha : ℝ} [SFinite μ]
    (hμt : IsTempered μ) (hμe : IsEven μ) (hsp : IsSpectralMeasure Γ μ)
    (hΓs : SpectralHomogeneous Γ ((d : ℝ) - alpha)) (ζ : SchwartzMap (Rd d) ℝ) (hζ : ζ ≠ 0)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (F : SchwartzMap (Rd d) H) :
    CompleteSpace (Cx H) ∧ (∀ v : H, ‖ofRealCLM v‖ = ‖v‖) ∧
      (∀ z : Cx H, ‖z‖ ^ 2 = ‖z.re‖ ^ 2 + ‖z.im‖ ^ 2) ∧
      (∀ ξ : Rd d, ‖paperHat (cxS F : Rd d → Cx H) ξ‖ ^ 2 =
        cd d ^ 2 * (‖∫ x, Real.cos (inner ℝ ξ x) • F x‖ ^ 2 +
          ‖∫ x, Real.sin (inner ℝ ξ x) • F x‖ ^ 2)) ∧
      (∀ R : ℝ, (fun x => (zetaR ζ R x : ℂ) • cxS F x) =
        fun x => ofRealCLM (zetaR ζ R x • F x)) ∧
      (Integrable (paperHat (fun x => (ζ x : ℂ))) ∧ 0 < Lz ζ) ∧
      ∀ R : ℝ, 0 < R →
        (Integrable (kR ζ R) ∧ ∫ u, ‖kR ζ R u‖ = Lz ζ) ∧
        IsEven (nu μ ζ R) ∧ IsTempered (nu μ ζ R) ∧ IsLocallyFiniteMeasure (nu μ ζ R) ∧
        (∀ y : Rd d, ∀ r : ℝ, 0 < r →
          nu μ ζ R (ball y r) ≤ ENNReal.ofReal (cd d ^ 2 * Lz ζ ^ 2 * CGamma Γ * r ^ alpha) ∧
          nu μ ζ R (closedBall y r) ≤
            ENNReal.ofReal (cd d ^ 2 * Lz ζ ^ 2 * CGamma Γ * r ^ alpha)) ∧
        (Integrable (fun ξ => ‖paperHat (fun x => (zetaR ζ R x : ℂ) • cxS F x) ξ‖ ^ 2) μ ∧
          Integrable (fun η => ‖paperHat (cxS F : Rd d → Cx H) η‖ ^ 2) (nu μ ζ R) ∧
          ∫⁻ ξ, ‖paperHat (fun x => (zetaR ζ R x : ℂ) • cxS F x) ξ‖ₑ ^ 2 ∂μ ≤
            ∫⁻ η, ‖paperHat (cxS F : Rd d → Cx H) η‖ₑ ^ 2 ∂nu μ ζ R ∧
          ∫⁻ η, ‖paperHat (cxS F : Rd d → Cx H) η‖ₑ ^ 2 ∂nu μ ζ R < ⊤ ∧
          ∫ ξ, ‖paperHat (fun x => (zetaR ζ R x : ℂ) • cxS F x) ξ‖ ^ 2 ∂μ ≤
            ∫ η, ‖paperHat (cxS F : Rd d → Cx H) η‖ ^ 2 ∂nu μ ζ R) := by
  bridge_revert_all
  intro d Γ μ alpha _ hμt hμe hsp hΓs ζ hζ H _ _ _ F
  haveI := StratonovichHamSecondMomentLeanAuditBridge.MaskedAuxiliaryReal.cx_completeSpace (H := H)
  exact ⟨StratonovichHamSecondMomentLeanAuditBridge.MaskedAuxiliaryReal.cx_completeSpace, fun v => StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx.norm_ofReal v,
    fun z => StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx.norm_sq_eq z, StratonovichHamSecondMomentLeanAuditBridge.MaskedAuxiliaryReal.norm_sq_paperHat_cx F, fun R => StratonovichHamSecondMomentLeanAuditBridge.MaskedAuxiliaryReal.mask_cxS ζ R F,
    _root_.StratonovichHAMSecondMoment.MaskedAuxiliaryNorm.masked_auxiliary_norm hμt hμe hsp hΓs ζ hζ
      (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.cxS F)⟩
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal
