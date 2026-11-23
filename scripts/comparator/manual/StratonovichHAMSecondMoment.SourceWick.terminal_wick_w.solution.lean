-- Printed type replaced by the source's statement in its scope (the printed type drops the universe of the .{u} targets, so it does not elaborate to the claimed type).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceWick
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal
universe u
open HomogHypothesis (Rd HomogCovariance)
open FiniteWick (CenteredGaussianField pairWeight wickSum pairings)
open TerminalWick (Pt prodL2)
open TerminalWickInputs (chainMeasure fieldL2)
open WickInterface (kerA capSet)
open LowAlphaConvolution (gammaEps gaussFactor)
open DiagramModel (Pi2 openers covEps)
open SourceInterface
variable {d : ℕ}
/-- TerminalWickWTarget d given hcont : SourceCovContinuousTarget d (item B): under H:homog, for every source field, t > 0, x, widths a, b: Y_m^a Y_n^b is integrable and E[Y_m^a Y_n^b] = sum over D in Pi2 m n of srcPairing (TeX 871-872, 1643-1650). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceWick.terminal_wick_w (d : ℕ) (hcont : SourceCovContinuousTarget d) :
    TerminalWickWTarget.{u} d := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto19 _root_.StratonovichHAMSecondMoment.SourceWick.terminal_wick_w)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceWick
