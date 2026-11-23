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
/-- L:white-test (TeX 940-949) for every source field with Gamma = dirac 0 in d = 1, 0 < alpha0 < 1, t > 0: E srcX_1^2 = c0 t^(3 - alpha0), E srcX_2 = c0/2 t^(3 - alpha0), sum_(m <= 2) E[X_m X_(2-m)] = 2 c0 t^(3 - alpha0). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceFinal.white_test_paper_l19 {α₀ : ℝ} (h0 : 0 < α₀) (h1 : α₀ < 1) {Ω : Type u}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {W : SrcPt 1 → Ω → ℝ}
    (hW : SourceField α₀ (Measure.dirac 0) P W) {t : ℝ} (ht : 0 < t) (x : Rd 1) :
    ∫ ω, srcX hW t ht.le x 1 ω ^ 2 ∂P = OrderTwoDiagrams.c0 α₀ * t ^ (3 - α₀) ∧
      ∫ ω, srcX hW t ht.le x 2 ω ∂P = OrderTwoDiagrams.c0 α₀ / 2 * t ^ (3 - α₀) ∧
      ∑ m ∈ Finset.range 3, ∫ ω, srcX hW t ht.le x m ω * srcX hW t ht.le x (2 - m) ω ∂P =
        2 * OrderTwoDiagrams.c0 α₀ * t ^ (3 - α₀) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFinal
