-- Printed type replaced by the source's statement in its scope (the printed type drops the universe of the .{u} targets, so it does not elaborate to the claimed type).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFinal
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
universe u
open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open DiagramModel (Pi2 diagram covEps diagramLim coeffA coeffALim MixedMoment)
open SourceInterface
open HomogeneousEnvelope (BK termBK)
open LowAlphaUpper (FirstMomentSeries C1 C2 Kgen)
open LowAlphaConvolution (specV)
open TwoSimplexTime (Zc)
open D1Spatial (Ksp)
open HigherRieszTwo (riesz)
/-- Under HomogCovariance d alpha alpha0 Gamma mu (d = 1, 2, 3): some C, theta0 > 0 such that for t > 0, every source field and x: E srcX_n^2 <= e^(2 theta0 t) C^n t^(2n)/n! (n >= 1) and E srcU^2 <= 2 e^(2 theta0 t + 2 C t^2) (TeX 1978-2054). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceFinal.crude_corrected_paper_l19 {d : ℕ} {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) :
    ∃ C θ₀ : ℝ, 0 < C ∧ 0 < θ₀ ∧ ∀ (t : ℝ) (ht : 0 < t) {Ω : Type u} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (W : SrcPt d → Ω → ℝ) (hW : SourceField α₀ Γ P W)
      (x : Rd d),
      (∀ n : ℕ, 1 ≤ n → ∫ ω, srcX hW t ht.le x n ω ^ 2 ∂P ≤
        Real.exp (2 * θ₀ * t) * C ^ n * t ^ (2 * n) / n !) ∧
      ∫ ω, srcU hW t ht.le x ω ^ 2 ∂P ≤ 2 * Real.exp (2 * θ₀ * t + 2 * C * t ^ 2) := by
  obtain ⟨C, θ₀, hC, hθ, h⟩ := _root_.StratonovichHAMSecondMoment.SourceFinal.crude_corrected_paper_l19.{u}
    (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)
  refine ⟨C, θ₀, hC, hθ, fun t ht Ω _ P _ W hW x => ?_⟩
  have h' := h t ht P W (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW) x
  simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq]
  exact h'
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFinal
