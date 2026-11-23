-- Printed type with the printed `ContDiff ℝ (↑⊤)` written as the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, scope `ContDiff`).
open scoped ContDiff in
/-- Given UM0Facts d, T with IsSpatialMeanMap S eta R T, Psi smooth with compact support, s in [0,1] and IsMultiplier (m_R h_(Psi,s)) M: T(int_I |s-t|^(-a) Psi_t dt) = B_E(M) (integrated_intrinsic_constant.tex lines 114-130 at revision edf7085f). -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.UniformMeanAssembly.T_kBochner_eq :
    ∀ {d : ℕ} {S : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.SpData d},
      StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PositiveRawMean.UM0Facts d →
        ∀ {p : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.TParams}
          {η : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d} {R : ℝ}
          {T :
            StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.Hsp S →L[ℝ]
              StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.E d →L[ℝ]
                StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.E d},
          StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.IsSpatialMeanMap S η R T →
            ∀ {Ψ : ℝ × StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ},
              ContDiff ℝ ∞ Ψ →
                HasCompactSupport Ψ →
                  ∀ {s : ℝ},
                    s ∈ Set.Icc (0 : ℝ) (1 : ℝ) →
                      ∀
                        {M :
                          StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.Hhalf d →L[ℝ]
                            StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.Hmhalf d},
                        StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.IsMultiplier
                            (fun (x : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d) =>
                              StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.mR η R x *
                                StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalDilation.mean p.a S.Γ Ψ s x)
                            M →
                          T
                              (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PositiveRawMean.kBochner p.a
                                (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.sliceField S Ψ) s) =
                            StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.BE M := by
  sorry
