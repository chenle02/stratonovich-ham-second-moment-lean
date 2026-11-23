-- Printed type replaced by the source's statement (the printed type drops the universe of the .{u} target).
/-- Field: JointMeasTarget d. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildInterface.JointMeasurability.holds.{u} :
    ∀ {d : ℕ}, StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.JointMeasurability.{u} d → StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.JointMeasTarget.{u} d := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  bridge_auto20 _root_.StratonovichHAMSecondMoment.MildInterface.JointMeasurability.holds
