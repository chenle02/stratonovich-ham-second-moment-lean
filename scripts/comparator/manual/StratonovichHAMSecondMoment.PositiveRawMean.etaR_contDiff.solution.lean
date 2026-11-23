-- Printed type with the printed `ContDiff ℝ (↑⊤)` written as the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, scope `ContDiff`).
open scoped ContDiff in
/-- eta_R is C^infinity. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.PositiveRawMean.etaR_contDiff :
    ∀ {d : ℕ} (η : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d) (R : ℝ),
      ContDiff ℝ ∞ (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.etaR η R) := by
  bridge_auto _root_.StratonovichHAMSecondMoment.PositiveRawMean.etaR_contDiff
