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
/-- For 0 <= c, 0 < alpha < 1, 0 < eps, 0 <= h and z: int covEps (withDensity (riesz c alpha)) eps (z - v) d(waveGreen 1 h)(v) <= ofReal (c h^(1-alpha)/(1-alpha)). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.D1Spatial.riesz_eps_conv_le {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) {ε : ℝ}
    (hε : 0 < ε) {h : ℝ} (hh : 0 ≤ h) (z : Rd 1) :
    ∫⁻ v, covEps (volume.withDensity (riesz c α)) ε (z - v) ∂waveGreen 1 h ≤
      ENNReal.ofReal (c * h ^ (1 - α) / (1 - α)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.D1Spatial
