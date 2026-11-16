namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceHeatGram
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Filter Metric Topology
open scoped ContDiff ENNReal ComplexConjugate
open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure IsEven IsTempered)
open WeakSobolev (IsTestFunction)
open SpatialFourierBound (spatialPair fourierQ ex ex_continuous norm_ex ex_sub)
open LowAlphaConvolution (heatDens gaussFactor gaussFactor_pos gaussFactor_le_one)
variable {d : ℕ}
/-- For tests F, G (smooth, compact support): crossCorr F G is smooth. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceHeatGram.crossCorr_contDiff {F G : Rd d → ℝ} (hF : IsTestFunction F) (hG : IsTestFunction G) :
    ContDiff ℝ ∞ (crossCorr F G) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceHeatGram
