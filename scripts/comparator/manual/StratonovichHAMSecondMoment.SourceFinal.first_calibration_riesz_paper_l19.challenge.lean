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
/-- Riesz case, d = 1, Gamma = c|y|^(-alpha) dy, 0 < alpha, alpha0 < 1, c > 0, t > 0, kept hypothesis hH: the conclusions of first_calibration_paper_l19 with K = Ksp c alpha, for every source field (MixedMoment, FirstMomentSeries discharged). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceFinal.first_calibration_riesz_paper_l19 {c α α₀ : ℝ} {μ : Measure (Rd 1)}
    (hH : HomogCovariance 1 α α₀ (volume.withDensity (riesz c α)) μ) (hc : 0 < c)
    (hα0 : 0 < α) (hα1 : α < 1) (hα₀0 : 0 < α₀) (hα₀1 : α₀ < 1) {Ω : Type u}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {W : SrcPt 1 → Ω → ℝ}
    (hW : SourceField α₀ (volume.withDensity (riesz c α)) P W) {t : ℝ} (ht : 0 < t)
    (x : Rd 1) :
    (∀ k : ℕ, 1 ≤ k → ∫ ω, srcX hW t ht.le x (2 * k) ω ∂P ≤
      (Zc α₀ * Ksp c α / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) /
        ((k ! : ℝ) * (k : ℝ) ^ ((2 - α) * k)) ∧
      (Zc α₀ * Ksp c α / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) /
          ((k ! : ℝ) * (k : ℝ) ^ ((2 - α) * k)) ≤
        (Zc α₀ * Ksp c α / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) / (k ! : ℝ) ^ (3 - α)) ∧
    ∫ ω, srcU hW t ht.le x ω ∂P ≤ Real.exp (C1 α α₀ (Ksp c α) * t ^ LowAlphaUpper.kappa α α₀) ∧
    C1 α α₀ (Ksp c α) = C2 α α₀ (Ksp c α) / 2 ^ ((4 - α) / (3 - α)) ∧
    2 * C1 α α₀ (Ksp c α) < C2 α α₀ (Ksp c α) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFinal
