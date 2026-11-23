-- Printed type replaced by the source's statement in its scope (the printed type drops the universe of the .{u} targets, so it does not elaborate to the claimed type).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceReversal
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal
universe u
open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open FiniteWick (pairWeight)
open TerminalWick (Pt chainWeightReal)
open TerminalWickInputs (chainMeasure chainMeasureRaw chainMap chainPoint timeMeasure gap toPt OpenSimplex)
open WickInterface (kerA capSet capDom wickF wickJ pairTime covW posOrthant horizon gapTime)
open LowAlphaConvolution (gammaEps)
open DiagramModel (Pi2 openers covEps rev revPairing SameChain pred predVal incr pos twoSimplex)
open SourceInterface SourceWick
variable {d : ℕ}
/-- TerminalMixedMomentTarget d given hcont : SourceCovContinuousTarget d (item B): under H:homog, any source field, t > 0, x, a, b: Y_m^a Y_n^b integrable and E[Y_m^a Y_n^b] = sum over D in Pi2 m n of toReal F at eps o rho, delta o rho, D, (t,t). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceReversal.terminal_mixed_moment (d : ℕ) (hcont : SourceCovContinuousTarget d) :
    TerminalMixedMomentTarget.{u} d := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceReversal
