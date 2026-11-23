-- Printed type with the printed `ContDiff ℝ (↑⊤)` written as the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, scope `ContDiff`).
open scoped ContDiff in
/-- Given UM0Facts, a CameronSpatialMap T, Psi smooth with compact support, s in [0,1] and IsMultiplier (m_R h_(Psi,s)) M: T (int_I |s-t|^(-a) Psi_t dt) = B_E(M) (TeX lines 114-130). Named input supplied: . -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.PositiveRawMean.T_kBochner_eq :
    ∀ {d : ℕ} {S : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.SpData d},
      StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PositiveRawMean.UM0Facts d →
        ∀ {p : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.TParams}
          {η : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d} {R : ℝ}
          (Tc : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.CameronSpatialMap S η R)
          {Ψ : ℝ × StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ},
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
                      Tc.T
                          (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PositiveRawMean.kBochner p.a
                            (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.sliceField S Ψ) s) =
                        StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.BE M := by
  bridge_auto _root_.StratonovichHAMSecondMoment.PositiveRawMean.T_kBochner_eq
