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
open SpaceTimePositivity (timeMeasure timeMeasure_eq_Icc)
open TimeSchur (kern kern_nonneg measurable_kern kern_sub_comm)
variable {μ : Measure (Rd d)}
/-- For a finite family k of vectors of a real inner product space: the Gram matrix (<k i, k j>) is positive semidefinite. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceHeatGram.gram_posSemidef {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (k : ι → E) :
    (Matrix.of fun i j => inner ℝ (k i) (k j)).PosSemidef := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceHeatGram
