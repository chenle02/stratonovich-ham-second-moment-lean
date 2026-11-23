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
/-- Under HomogCovariance d alpha alpha0 Gamma mu, alpha <= 1, V = specV mu > 0 (carried, unused), t > 0, every source field, x: sum_m E[X_m X_(2k-m)] <= (2 Z Kgen)^k t^(beta k)/(k! k^((2-alpha)k)) (k >= 1) and E srcU^2 <= exp(C2 t^kappa). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceFinal.low_alpha_upper_moment_paper_l19 {d : ℕ} {α α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d α α₀ Γ μ) (hα1 : α ≤ 1) (hV : 0 < (specV μ).toReal) {Ω : Type u}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {W : SrcPt d → Ω → ℝ}
    (hW : SourceField α₀ Γ P W) {t : ℝ} (ht : 0 < t) (x : Rd d) :
    (∀ k : ℕ, 1 ≤ k →
      ∑ m ∈ Finset.range (2 * k + 1),
          ∫ ω, srcX hW t ht.le x m ω * srcX hW t ht.le x (2 * k - m) ω ∂P ≤
        (2 * Zc α₀ * Kgen α (specV μ).toReal) ^ k * t ^ ((4 - α - α₀) * k) /
          ((k ! : ℝ) * (k : ℝ) ^ ((2 - α) * k))) ∧
    ∫ ω, srcU hW t ht.le x ω ^ 2 ∂P ≤
      Real.exp (C2 α α₀ (Kgen α (specV μ).toReal) * t ^ LowAlphaUpper.kappa α α₀) := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto19 _root_.StratonovichHAMSecondMoment.SourceFinal.low_alpha_upper_moment_paper_l19)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFinal
