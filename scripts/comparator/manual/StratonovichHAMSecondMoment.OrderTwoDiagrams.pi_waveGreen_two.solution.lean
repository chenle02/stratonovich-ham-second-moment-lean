namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OrderTwoDiagrams
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology Set
open scoped ENNReal
open HomogHypothesis (Rd)
open WaveGreen (waveGreen)
open VariationalMean (heatK)
open HigherRieszTwo (riesz)
open DiagramModel
open DiagramBridge (e1)
/-- Measure.pi of (i -> waveGreen 1 (h i)) over Fin 2 equals Measure.pi of the vector [waveGreen 1 (h 0), waveGreen 1 (h 1)]. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.OrderTwoDiagrams.pi_waveGreen_two (h : Fin 2 → ℝ) :
    Measure.pi (fun i => waveGreen 1 (h i)) =
      Measure.pi ![waveGreen 1 (h 0), waveGreen 1 (h 1)] := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.OrderTwoDiagrams.pi_waveGreen_two
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OrderTwoDiagrams
