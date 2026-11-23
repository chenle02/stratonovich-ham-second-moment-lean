-- Printed type with the printed `ContDiff ℝ (↑⊤)` written as the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, scope `ContDiff`).
open scoped ContDiff in
/-- A C^infinity function times a real test function is a test function. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.UniformMeanInterface.isTest_smooth_mul :
    ∀ {d : ℕ} {V φ : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ},
      ContDiff ℝ ∞ V →
        StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.IsTestFunction φ →
          StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.IsTestFunction (d := d)
            fun (x : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d) => V x * φ x := by
  exact @_root_.StratonovichHAMSecondMoment.UniformMeanInterface.isTest_smooth_mul
