namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszFourDiagrams
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology Set
open scoped ENNReal
open HomogHypothesis (Rd)
open WaveGreen (waveGreen)
open VariationalMean (heatK)
open HigherRieszTwo (riesz)
open DiagramModel
open DiagramBridge (e1)
open OrderTwoDiagrams
/-- unifLaw.map e1 = ofReal(1/2) * Lebesgue restricted to (-1,1). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszFourDiagrams.map_e1_unifLaw :
    unifLaw.map e1 = ENNReal.ofReal (1 / 2) • (volume : Measure ℝ).restrict (Ioo (-1) 1) := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.RieszFourDiagrams.map_e1_unifLaw
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszFourDiagrams
