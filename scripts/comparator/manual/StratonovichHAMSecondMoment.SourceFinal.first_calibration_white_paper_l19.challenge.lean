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
/-- White case, d = 1, Gamma = whiteCov c, c > 0, 0 < alpha0 < 1, t > 0, every source field: the conclusions of first_calibration_paper_l19 with alpha = 1, K = c; H:homog discharged by white_homogCovariance. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceFinal.first_calibration_white_paper_l19 {c α₀ : ℝ} (hc : 0 < c) (hα₀0 : 0 < α₀)
    (hα₀1 : α₀ < 1) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : SrcPt 1 → Ω → ℝ} (hW : SourceField α₀ (WhiteModel.whiteCov c) P W) {t : ℝ}
    (ht : 0 < t) (x : Rd 1) :
    (∀ k : ℕ, 1 ≤ k → ∫ ω, srcX hW t ht.le x (2 * k) ω ∂P ≤
      (Zc α₀ * c / 2 ^ (3 - 1 : ℝ)) ^ k * t ^ ((4 - 1 - α₀) * k) /
        ((k ! : ℝ) * (k : ℝ) ^ ((2 - 1 : ℝ) * k)) ∧
      (Zc α₀ * c / 2 ^ (3 - 1 : ℝ)) ^ k * t ^ ((4 - 1 - α₀) * k) /
          ((k ! : ℝ) * (k : ℝ) ^ ((2 - 1 : ℝ) * k)) ≤
        (Zc α₀ * c / 2 ^ (3 - 1 : ℝ)) ^ k * t ^ ((4 - 1 - α₀) * k) / (k ! : ℝ) ^ (3 - 1 : ℝ)) ∧
    ∫ ω, srcU hW t ht.le x ω ∂P ≤ Real.exp (C1 1 α₀ c * t ^ LowAlphaUpper.kappa 1 α₀) ∧
    C1 1 α₀ c = C2 1 α₀ c / 2 ^ ((4 - 1 : ℝ) / (3 - 1)) ∧
    2 * C1 1 α₀ c < C2 1 α₀ c := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFinal
