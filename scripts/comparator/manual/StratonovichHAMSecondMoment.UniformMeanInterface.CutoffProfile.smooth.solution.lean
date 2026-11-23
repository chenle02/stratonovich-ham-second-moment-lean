-- Printed type with the printed `ContDiff ℝ (↑⊤)` written as the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, scope `ContDiff`).
open scoped ContDiff in
/-- Field: eta is C^infinity. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile.smooth :
    ∀ {d : ℕ} (self : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d),
      ContDiff ℝ ∞ self.η := by
  bridge_auto _root_.StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile.smooth
