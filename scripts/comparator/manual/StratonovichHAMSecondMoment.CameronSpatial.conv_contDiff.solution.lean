-- Printed type with the printed `ContDiff ℝ (↑⊤)` written as the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, scope `ContDiff`).
open scoped ContDiff in
/-- For a real test q, Gamma * q is C^infinity. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.CameronSpatial.conv_contDiff :
    ∀ {d : ℕ} {S : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.SpData d}
      {q : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ},
      StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.IsTestFunction q →
        ContDiff ℝ ∞ (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalDilation.conv S.Γ q) := by
  bridge_auto _root_.StratonovichHAMSecondMoment.CameronSpatial.conv_contDiff
