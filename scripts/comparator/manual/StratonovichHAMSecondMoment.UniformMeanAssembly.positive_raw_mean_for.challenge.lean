-- Printed type with the printed `ContDiff ℝ (↑⊤)` written as the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, scope `ContDiff`).
open scoped ContDiff in
/-- Given UM0Facts d, T_R (R >= 1) with IsSpatialMeanMap, U with UTensorSpec, 2 <= r and h_(Psi,s) smooth and bounded: PositiveRawMeanFor eta T U (mean identity of E:positive-raw-mean and canonical version); no compactness. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.UniformMeanAssembly.positive_raw_mean_for :
    ∀ {d : ℕ} {p : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.TParams}
      {S : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.SpData d},
      StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PositiveRawMean.UM0Facts d →
        ∀ {η : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d} {r : ENNReal}
          [inst : Fact ((1 : ENNReal) ≤ r)]
          {T :
            (R : ℝ) →
              (1 : ℝ) ≤ R →
                StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.Hsp S →L[ℝ]
                  StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.E d →L[ℝ]
                    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.E d},
          (∀ (R : ℝ) (hR : (1 : ℝ) ≤ R),
              StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.IsSpatialMeanMap S η R (T R hR)) →
            ∀
              {U :
                StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.HI p S →L[ℝ]
                  ↥(MeasureTheory.Lp (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.Hsp S) r
                      StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.timeMeasure)},
              StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.UTensorSpec p S r U →
                (2 : ENNReal) ≤ r →
                  (∀ Ψ ∈ StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalDilation.CPos d,
                      ∀ s ∈ Set.Ioo (0 : ℝ) (1 : ℝ),
                        ContDiff ℝ ∞
                            (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalDilation.mean p.a S.Γ Ψ s) ∧
                          ∃ (C : ℝ),
                            ∀ (x : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d),
                              |StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalDilation.mean p.a S.Γ Ψ s x| ≤
                                C) →
                    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.PositiveRawMeanFor η T U := by
  sorry
