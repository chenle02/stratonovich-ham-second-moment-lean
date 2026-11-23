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
/-- L20-C headline, no hypothesis beyond the targets' own H:homog: FieldMeasTarget d = JointMeasTarget d and FieldContTarget d, Step 2 of P:mild-construction (TeX 2204-2230), for every d. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildFields.field_meas (d : ℕ) : FieldMeasTarget.{u} d := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.MildFields.field_meas)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildFields
