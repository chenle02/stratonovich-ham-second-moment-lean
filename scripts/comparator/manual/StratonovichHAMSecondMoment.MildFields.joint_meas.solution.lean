-- Printed type replaced by the source's statement in its scope (the printed type drops the universe of the .{u} targets, so it does not elaborate to the claimed type).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildFields
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
universe u
open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open FiniteWick (CenteredGaussianField)
open TerminalWick (Pt prodL2 chainWeightReal)
open TerminalWickInputs (chainMeasure chainMeasureRaw chainMap chainPoint toPt timeMeasure fieldL2 gap)
open SourceInterface
open MildInterface
variable {d : ℕ}
/-- JointMeasTarget d (TeX 2213-2219): under H:homog, for every source field on a probability space, the total fields W_a, Y_n^b, X_n and u on R x R^d (0 for s < 0) are strongly measurable into L2(Omega); X_n via widths 1/(k+1), u via partial sums. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildFields.joint_meas (d : ℕ) : JointMeasTarget.{u} d := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.MildFields.joint_meas)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildFields
