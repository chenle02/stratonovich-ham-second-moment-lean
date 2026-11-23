-- Printed type with the printed `ContDiff ℝ (↑⊤)` written as the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, scope `ContDiff`).
open scoped ContDiff in
/-- Given UM0Facts, a regulator Ureg for p, S, eta, r, and the hypothesis that h_(Psi,s) is C^infinity and bounded for every Psi in C_pos and s in (0,1): PositiveRawMeanTarget Ureg (TeX lines 32-39, proof 42-132). Named input supplied: UniformMeanRegulator, CameronSpatialMap. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.PositiveRawMean.positive_raw_mean_of :
    ∀ {d : ℕ} {p : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.TParams}
      {S : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.SpData d},
      StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PositiveRawMean.UM0Facts d →
        ∀ {η : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d} {r : ENNReal}
          [inst : Fact ((1 : ENNReal) ≤ r)]
          (Ureg : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.UniformMeanRegulator p S η r),
          (∀ Ψ ∈ StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalDilation.CPos d,
              ∀ s ∈ Set.Ioo (0 : ℝ) (1 : ℝ),
                ContDiff ℝ ∞ (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalDilation.mean p.a S.Γ Ψ s) ∧
                  ∃ (C : ℝ),
                    ∀ (x : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d),
                      |StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalDilation.mean p.a S.Γ Ψ s x| ≤ C) →
            StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.PositiveRawMeanTarget Ureg := by
  sorry
