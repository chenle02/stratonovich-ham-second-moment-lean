-- Printed type replaced by the source's statement (the printed type drops the universe of the .{u} target).
/-- Field: TerminalFubiniTarget d. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildInterface.TerminalFubini.holds.{u} :
    ∀ {d : ℕ}, StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.TerminalFubini.{u} d → StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.TerminalFubiniTarget.{u} d := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  bridge_auto20 _root_.StratonovichHAMSecondMoment.MildInterface.TerminalFubini.holds
