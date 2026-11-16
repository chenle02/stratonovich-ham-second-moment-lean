namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.D1Spatial
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology Set
open scoped ENNReal
open HomogHypothesis (Rd)
open WaveGreen (waveGreen coordOne)
open DiagramModel
open FiniteWick (pairings mem_pairings)
open LowAlphaConvolution (heatDens)
open VariationalMean (heatK)
open HigherRieszTwo (riesz smoothCov)
open WhiteModel (whiteCov)
/-- covEps (volume.withDensity (riesz c alpha)) eps is measurable on R^1. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.D1Spatial.measurable_covEps_riesz (c α ε : ℝ) :
    Measurable (covEps (volume.withDensity (riesz c α)) ε : Rd 1 → ℝ≥0∞) := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.D1Spatial.measurable_covEps_riesz
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.D1Spatial
