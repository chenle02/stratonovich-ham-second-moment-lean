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
/-- Under HomogCovariance, alpha <= 1, V > 0, t > 0, every source field, x: E srcX_(2k) <= (Z Kgen/2^(3-alpha))^k t^(beta k)/(k! k^(bk)) <= .../(k!)^(3-alpha), E srcU <= exp(C1 t^kappa), C1 = C2/2^((4-alpha)/(3-alpha)), 2 C1 < C2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceFinal.first_calibration_paper_l19 {d : ℕ} {α α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d α α₀ Γ μ) (hα1 : α ≤ 1) (hV : 0 < (specV μ).toReal) {Ω : Type u}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {W : SrcPt d → Ω → ℝ}
    (hW : SourceField α₀ Γ P W) {t : ℝ} (ht : 0 < t) (x : Rd d) :
    (∀ k : ℕ, 1 ≤ k → ∫ ω, srcX hW t ht.le x (2 * k) ω ∂P ≤
      (Zc α₀ * Kgen α (specV μ).toReal / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) /
        ((k ! : ℝ) * (k : ℝ) ^ ((2 - α) * k)) ∧
      (Zc α₀ * Kgen α (specV μ).toReal / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) /
          ((k ! : ℝ) * (k : ℝ) ^ ((2 - α) * k)) ≤
        (Zc α₀ * Kgen α (specV μ).toReal / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! : ℝ) ^ (3 - α)) ∧
    ∫ ω, srcU hW t ht.le x ω ∂P ≤
      Real.exp (C1 α α₀ (Kgen α (specV μ).toReal) * t ^ LowAlphaUpper.kappa α α₀) ∧
    C1 α α₀ (Kgen α (specV μ).toReal) =
      C2 α α₀ (Kgen α (specV μ).toReal) / 2 ^ ((4 - α) / (3 - α)) ∧
    2 * C1 α α₀ (Kgen α (specV μ).toReal) < C2 α α₀ (Kgen α (specV μ).toReal) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFinal
