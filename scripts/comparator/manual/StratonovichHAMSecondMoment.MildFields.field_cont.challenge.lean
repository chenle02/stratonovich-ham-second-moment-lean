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
/-- FieldContTarget d (TeX 2219-2230): under H:homog, source field, s >= 0: y -> Y_n^b(s,y), X_n(s,y), u(s,y) continuous into L2, and ||Y_n^b(s,y) - X_n(s,y)|| = ||Y_n^b(s,0) - X_n(s,0)|| for b of length n (2224-2227). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildFields.field_cont (d : ℕ) : FieldContTarget.{u} d := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildFields
