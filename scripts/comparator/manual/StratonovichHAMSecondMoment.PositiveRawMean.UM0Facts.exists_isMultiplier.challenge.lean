-- Printed type with the printed `ContDiff ℝ (↑⊤)` written as the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, scope `ContDiff`).
open scoped ContDiff in
/-- Field: a smooth V with |V| <= C has a multiplier M with |M| <= C. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.PositiveRawMean.UM0Facts.exists_isMultiplier :
    ∀ {d : ℕ},
      StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PositiveRawMean.UM0Facts d →
        ∀ {V : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ},
          ContDiff ℝ ∞ V →
            ∀ {C : ℝ},
              (∀ (x : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d), |V x| ≤ C) →
                ∃ (M :
                  StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.Hhalf d →L[ℝ]
                    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.Hmhalf d),
                  StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.IsMultiplier V M ∧ ‖M‖ ≤ C := by
  sorry
