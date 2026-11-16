namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceHeatGram
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Filter Metric Topology
open scoped ContDiff ENNReal ComplexConjugate
open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure IsEven IsTempered)
open WeakSobolev (IsTestFunction)
open SpatialFourierBound (spatialPair fourierQ ex ex_continuous norm_ex ex_sub)
open LowAlphaConvolution (heatDens gaussFactor gaussFactor_pos gaussFactor_le_one)
variable {d : ℕ}
variable {μ : Measure (Rd d)}
/-- For every eps and F in L^2(mu; C): xi -> heatMult eps xi * F xi is in L^2(mu). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceHeatGram.memLp_heatMult (ε : ℝ) (F : Lp ℂ 2 μ) :
    MemLp (fun ξ => (heatMult ε ξ : ℂ) * F ξ) 2 μ := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.SourceHeatGram.memLp_heatMult
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceHeatGram
