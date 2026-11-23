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
/-- Under HomogCovariance (d = 1, 2, 3): some K > 0 such that for t > 0, every source field, x: E[srcX_m srcX_n] <= #Pi2 m n K^k e^(2 theta t) theta^(-(4 - alpha - alpha0) k) (m + n = 2k >= 2, theta > 0) and E srcU^2 <= BK K (4 - alpha - alpha0) t; growth not stated. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceFinal.envelope_paper_l19 {d : ℕ} {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (t : ℝ) (ht : 0 < t) {Ω : Type u} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (W : SrcPt d → Ω → ℝ) (hW : SourceField α₀ Γ P W)
      (x : Rd d),
      (∀ m n k : ℕ, m + n = 2 * k → 1 ≤ k → ∀ θ : ℝ, 0 < θ →
        ∫ ω, srcX hW t ht.le x m ω * srcX hW t ht.le x n ω ∂P ≤
          (Pi2 m n).card * K ^ k * Real.exp (2 * θ * t) * θ ^ (-((4 - alpha - α₀) * k))) ∧
      ∫ ω, srcU hW t ht.le x ω ^ 2 ∂P ≤ BK K (4 - alpha - α₀) t := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFinal
