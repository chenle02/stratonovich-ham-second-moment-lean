namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.D1Spatial
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
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
/-- If D i != i for all i then {i | not (D i < i)} = openers D. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.D1Spatial.filter_not_closing {N : ℕ} {D : Fin N → Fin N} (hne : ∀ i, D i ≠ i) :
    (Finset.univ.filter fun i => ¬ D i < i) = openers D := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.D1Spatial
