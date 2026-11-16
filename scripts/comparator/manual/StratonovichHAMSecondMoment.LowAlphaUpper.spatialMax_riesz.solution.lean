namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.LowAlphaUpper
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology Set
open scoped ENNReal Nat
open HomogHypothesis (Rd HomogCovariance IsEven)
open WaveGreen (waveGreen)
open DiagramModel
open FiniteWick (pairings mem_pairings)
open D1Spatial (closers spatialPair Ksp)
open LowAlphaConvolution (heatDens gammaEps specV)
open TwoSimplexTime (Zc)
/-- For c >= 0 and 0 < alpha < 1: SpatialMax 1 (c|y|^(-alpha) dy) (Ksp c alpha) (2 - alpha). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.LowAlphaUpper.spatialMax_riesz {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) :
    SpatialMax 1 (volume.withDensity (HigherRieszTwo.riesz c α)) (Ksp c α) (2 - α) := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.LowAlphaUpper.spatialMax_riesz
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.LowAlphaUpper
