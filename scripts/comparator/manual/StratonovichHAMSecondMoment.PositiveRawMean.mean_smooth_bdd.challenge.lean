-- Printed type with the printed `ContDiff ℝ (↑⊤)` written as the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, scope `ContDiff`).
open scoped ContDiff in
/-- Under H:homog with Gamma != 0, for Psi in C_pos and s in [0,1]: h_(Psi,s) is C^infinity and bounded (VariationalMeanDerivatives.variational_global_mean_whole_paper, L:variational-global-mean). -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.PositiveRawMean.mean_smooth_bdd :
    ∀ {d : ℕ} {alpha alpha0 : ℝ}
      {Γ μ : MeasureTheory.Measure (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d)},
      StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ →
        Γ ≠ (0 : MeasureTheory.Measure (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d)) →
          ∀ {Ψ : ℝ × StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ},
            Ψ ∈ StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalDilation.CPos d →
              ∀ {s : ℝ},
                s ∈ Set.Icc (0 : ℝ) (1 : ℝ) →
                  ContDiff ℝ ∞ (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalDilation.mean alpha0 Γ Ψ s) ∧
                    ∃ (C : ℝ),
                      ∀ (x : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d),
                        |StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalDilation.mean alpha0 Γ Ψ s x| ≤ C := by
  sorry
