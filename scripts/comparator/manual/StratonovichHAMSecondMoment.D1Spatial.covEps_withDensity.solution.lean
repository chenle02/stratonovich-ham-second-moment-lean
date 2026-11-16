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
/-- For measurable g : R^d -> [0,infinity] and any eps: covEps (volume.withDensity g) eps = HigherRieszTwo.smoothCov g eps. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.D1Spatial.covEps_withDensity {d : ℕ} {g : Rd d → ℝ≥0∞} (hg : Measurable g) (ε : ℝ) :
    covEps (volume.withDensity g) ε = smoothCov g ε := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.D1Spatial.covEps_withDensity
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.D1Spatial
