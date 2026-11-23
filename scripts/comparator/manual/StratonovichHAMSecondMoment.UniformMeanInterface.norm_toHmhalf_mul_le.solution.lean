-- Printed type with the printed `ContDiff ℝ (↑⊤)` written as the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, scope `ContDiff`).
open scoped ContDiff in
/-- For V C^infinity with |V| <= C and a real test phi: |[V phi]_(H^(-1/2))| <= C |[phi]_(H^(1/2))|. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.UniformMeanInterface.norm_toHmhalf_mul_le :
    ∀ {d : ℕ} {V : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ},
      ContDiff ℝ ∞ V →
        ∀ {C : ℝ},
          (∀ (x : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d), |V x| ≤ C) →
            ∀ {φ : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ},
              StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.IsTestFunction φ →
                Norm.norm (E := StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.Hmhalf d)
                    (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.toHmhalf
                      fun (x : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d) => V x * φ x) ≤
                  C * ‖StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.toHhalf φ‖ := by
  exact @_root_.StratonovichHAMSecondMoment.UniformMeanInterface.norm_toHmhalf_mul_le
