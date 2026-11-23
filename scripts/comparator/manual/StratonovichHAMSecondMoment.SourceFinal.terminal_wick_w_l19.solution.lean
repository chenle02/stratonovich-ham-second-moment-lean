-- Printed type replaced by the source's statement in its scope (the printed type drops the universe of the .{u} targets, so it does not elaborate to the claimed type).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFinal
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
universe u
open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open DiagramModel (Pi2 diagram covEps diagramLim coeffA coeffALim MixedMoment)
open SourceInterface
open HomogeneousEnvelope (BK termBK)
open LowAlphaUpper (FirstMomentSeries C1 C2 Kgen)
open LowAlphaConvolution (specV)
open TwoSimplexTime (Zc)
open D1Spatial (Ksp)
open HigherRieszTwo (riesz)
/-- For every d, nothing supplied: TerminalWickWTarget d: under H:homog, t > 0, widths a, b: Y^a Y^b is integrable and E[Y^a Y^b] = sum over Pi2 m n of srcPairing (TeX 858-882, 1643-1650); B's covariance continuity discharged. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceFinal.terminal_wick_w_l19 (d : ℕ) : TerminalWickWTarget.{u} d := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto19 _root_.StratonovichHAMSecondMoment.SourceFinal.terminal_wick_w_l19)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFinal
