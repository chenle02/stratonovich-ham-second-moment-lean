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
/-- covEps (volume.withDensity (riesz c alpha)) eps x = int ofReal(heatK eps z) * riesz c alpha (x - z) dz. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszFourDiagrams.covEps_riesz (c α ε : ℝ) (x : Rd 1) :
    covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε x =
      ∫⁻ z, ENNReal.ofReal (heatK ε z) * riesz c α (x - z) := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.RieszFourDiagrams.covEps_riesz
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszFourDiagrams
