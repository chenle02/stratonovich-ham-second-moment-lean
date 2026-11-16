namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.DiagramBridge
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology
open scoped ENNReal
open HomogHypothesis (Rd)
open WaveGreen (waveGreen)
open DiagramModel
/-- For h : Fin N -> R: Measure.pi (fun i => waveGreen 1 (h i)) = ofReal (1/2)^N times Lebesgue restricted to the box prod_i (-h i, h i). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.DiagramBridge.pi_waveGreen_one {N : ℕ} (h : Fin N → ℝ) :
    Measure.pi (fun i => waveGreen 1 (h i)) =
      ENNReal.ofReal (1 / 2) ^ N •
        (volume : Measure (Fin N → Rd 1)).restrict
          (Set.univ.pi fun i => Metric.ball (0 : Rd 1) (h i)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.DiagramBridge
