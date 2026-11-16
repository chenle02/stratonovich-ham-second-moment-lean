namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Real Metric
open scoped ENNReal NNReal ComplexConjugate
open HomogHypothesis SpectralHomog MaskedSpectralGrowth MaskedAuxiliaryNorm
open Cx
/-- H:homog, Gamma != 0 (unused), zeta != 0 real Schwartz, H a complete separable real inner product space, F H-valued Schwartz: Cx H complete and separable, iota isometric, norm and transform identities, mask identity, and masked_auxiliary_norm_paper for cxS F. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.masked_auxiliary_norm_real_paper {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) (ζ : SchwartzMap (Rd d) ℝ)
    (hζ : ζ ≠ 0) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (F : SchwartzMap (Rd d) H) :
    CompleteSpace (Cx H) ∧ TopologicalSpace.SeparableSpace (Cx H) ∧
      (∀ v : H, ‖ofRealCLM v‖ = ‖v‖) ∧
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
  intro d alpha alpha0 Γ μ h hΓ ζ hζ H _ _ _ _ F
  haveI := StratonovichHamSecondMomentLeanAuditBridge.MaskedAuxiliaryReal.cx_completeSpace (H := H)
  haveI := StratonovichHamSecondMomentLeanAuditBridge.MaskedAuxiliaryReal.cx_separableSpace (H := H)
  exact ⟨StratonovichHamSecondMomentLeanAuditBridge.MaskedAuxiliaryReal.cx_completeSpace, StratonovichHamSecondMomentLeanAuditBridge.MaskedAuxiliaryReal.cx_separableSpace, fun v => StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx.norm_ofReal v,
    fun z => StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx.norm_sq_eq z, StratonovichHamSecondMomentLeanAuditBridge.MaskedAuxiliaryReal.norm_sq_paperHat_cx F, fun R => StratonovichHamSecondMomentLeanAuditBridge.MaskedAuxiliaryReal.mask_cxS ζ R F,
    _root_.StratonovichHAMSecondMoment.MaskedAuxiliaryNorm.masked_auxiliary_norm_paper
      (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP h) hΓ ζ hζ (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.cxS F)⟩
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal
