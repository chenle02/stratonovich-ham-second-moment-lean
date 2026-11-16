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
/-- covEps (volume.withDensity (riesz c alpha)) eps (-x) = covEps (volume.withDensity (riesz c alpha)) eps x on R^1. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.D1Spatial.covEps_riesz_neg (c α ε : ℝ) (x : Rd 1) :
    covEps (volume.withDensity (riesz c α)) ε (-x) =
      covEps (volume.withDensity (riesz c α)) ε x := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.D1Spatial
