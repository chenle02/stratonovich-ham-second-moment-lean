-- Printed type with the printed `ContDiff ℝ (↑⊤)` written as the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, scope `ContDiff`).
open scoped ContDiff in
/-- For V C^infinity with |V(x)| <= C for all x: there is M with IsMultiplier V M and |M| <= C (|V phi|_(H^(-1/2)) <= |V phi|_2 <= C |phi|_2 <= C |phi|_(H^(1/2)), then extension from the dense tests; the meaning of B_E(m_R h_(Psi,s)), integrated_intrinsic_constant.tex line 36). -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.UniformMeanInterface.exists_isMultiplier :
    ∀ {d : ℕ} {V : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ},
      ContDiff ℝ ∞ V →
        ∀ {C : ℝ},
          (∀ (x : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d), |V x| ≤ C) →
            ∃ (M :
              StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.Hhalf d →L[ℝ]
                StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.Hmhalf d),
              StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.IsMultiplier V M ∧ ‖M‖ ≤ C := by
  sorry
