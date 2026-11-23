-- Printed type with the printed `ContDiff ℝ (↑⊤)` written as the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, scope `ContDiff`).
open scoped ContDiff in
/-- chi is C^infinity on R^d. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.CameronProducts.lpChi_contDiff :
    ∀ {d : ℕ},
      ContDiff ℝ (E := StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d) ∞
        StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronProducts.lpChi := by
  bridge_auto _root_.StratonovichHAMSecondMoment.CameronProducts.lpChi_contDiff
