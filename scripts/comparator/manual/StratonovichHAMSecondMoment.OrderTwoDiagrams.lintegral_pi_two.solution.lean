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
/-- For sigma-finite mu, nu and measurable g: int g(w 0, w 1) d(Measure.pi [mu, nu]) = int int g(x, y) dnu dmu. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.OrderTwoDiagrams.lintegral_pi_two {α : Type*} [MeasurableSpace α] (μ ν : Measure α) [SigmaFinite μ]
    [SigmaFinite ν] {g : α × α → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ w, g (w 0, w 1) ∂Measure.pi ![μ, ν] = ∫⁻ x, ∫⁻ y, g (x, y) ∂ν ∂μ := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.OrderTwoDiagrams.lintegral_pi_two
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OrderTwoDiagrams
