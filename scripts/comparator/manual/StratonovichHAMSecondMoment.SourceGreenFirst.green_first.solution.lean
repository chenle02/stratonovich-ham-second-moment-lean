-- Printed type replaced by the source's statement in its scope (the printed type drops the universe of the .{u} targets, so it does not elaborate to the claimed type).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceGreenFirst
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
universe u
open HomogHypothesis (Rd HomogCovariance)
open FiniteWick (CenteredGaussianField)
open TerminalWick (Pt prodL2)
open TerminalWickInputs (chainMeasure fieldL2)
open TerminalWickRegularization (chainMeasureReg noiseMeasure regPt)
open LowAlphaConvolution (gammaEps)
open SourceInterface
variable {d : ℕ}
/-- For every d, hypothesis hcont : SourceCovContinuousTarget d (item B): GreenFirstTarget d: under H:homog, source field, t > 0, x, fixed width pairs a: YaReg a eta -> Ya a in L^2 as eta -> 0+ (TeX 1651-1655, 1860-1861, 1960-1963; the TeX sentence is d = 3). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceGreenFirst.green_first (d : ℕ) (hcont : SourceCovContinuousTarget d) : GreenFirstTarget.{u} d := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto19 _root_.StratonovichHAMSecondMoment.SourceGreenFirst.green_first)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceGreenFirst
