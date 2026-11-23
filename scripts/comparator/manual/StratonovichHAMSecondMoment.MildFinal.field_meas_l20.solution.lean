-- Printed type replaced by the source's statement in its scope (the printed type drops the universe of the .{u} targets, so it does not elaborate to the claimed type).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildFinal
set_option autoImplicit false
universe u v
open MildInterface
/-- For every d, nothing supplied: FieldMeasTarget d: under H:homog, W_a, Y_n^b, X_n, u are strongly measurable on R x R^d; Y_n^b, X_n, u are L^2-continuous in y at each s >= 0, with the stationarity identity (Step 2, TeX 2204-2230). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildFinal.field_meas_l20 (d : ℕ) : FieldMeasTarget.{u} d := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.MildFinal.field_meas_l20)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildFinal
