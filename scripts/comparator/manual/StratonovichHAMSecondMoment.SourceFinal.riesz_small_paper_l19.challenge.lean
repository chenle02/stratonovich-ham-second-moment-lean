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
/-- E:riesz-two (TeX 5129-5142) for every source field, d = 1, Gamma = c|y|^(-alpha) dy, 0 < alpha, alpha0 < 1, c > 0, t > 0, kept hypothesis hH (Riesz H:homog): E srcX_2 and E srcX_1^2 by the two displays; their total is E X_1^2 + 2 E X_2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceFinal.riesz_small_paper_l19 {c α α₀ : ℝ} {μ : Measure (Rd 1)}
    (hH : HomogCovariance 1 α α₀ ((volume : Measure (Rd 1)).withDensity (riesz c α)) μ)
    (hc : 0 < c) (hα : 0 < α) (hα1 : α < 1) (hα0 : 0 < α₀) (hα01 : α₀ < 1) {Ω : Type u}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {W : SrcPt 1 → Ω → ℝ}
    (hW : SourceField α₀ ((volume : Measure (Rd 1)).withDensity (riesz c α)) P W) {t : ℝ}
    (ht : 0 < t) (x : Rd 1) :
    ∫ ω, srcX hW t ht.le x 2 ω ∂P = c * t ^ (4 - α - α₀) /
        ((1 - α) * (2 - α - α₀) * (3 - α - α₀) * (4 - α - α₀)) ∧
      ∫ ω, srcX hW t ht.le x 1 ω ^ 2 ∂P =
        c / ((1 - α) * (2 - α)) * ∫ v in (0 : ℝ)..t, v ^ (-α₀) * OrderTwoDiagrams.rbr t α v ∧
      ∑ m ∈ Finset.range 3, ∫ ω, srcX hW t ht.le x m ω * srcX hW t ht.le x (2 - m) ω ∂P =
        ∫ ω, srcX hW t ht.le x 1 ω ^ 2 ∂P + 2 * ∫ ω, srcX hW t ht.le x 2 ω ∂P := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFinal
