-- Printed type with the printed `ContDiff ℝ (↑⊤)` written as the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, scope `ContDiff`).
open scoped ContDiff in
/-- S_J is C^infinity. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.CameronProducts.lpS_contDiff :
    ∀ {d : ℕ} (J : ℕ),
      ContDiff ℝ (E := StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d) ∞
        (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronProducts.lpS J) := by
  bridge_auto _root_.StratonovichHAMSecondMoment.CameronProducts.lpS_contDiff
