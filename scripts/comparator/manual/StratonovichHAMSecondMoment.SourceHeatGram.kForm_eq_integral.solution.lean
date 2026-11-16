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
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
/-- kForm a F H is the Bochner integral of |s-t|^(-a) <F s, H t> over I^2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceHeatGram.kForm_eq_integral (a : ℝ) (F H : Lp G 2 timeMeasure) :
    kForm a F H =
      ∫ q, kern a (q.1 - q.2) * inner ℝ (F q.1) (H q.2) ∂(timeMeasure.prod timeMeasure) := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.SourceHeatGram.kForm_eq_integral
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceHeatGram
