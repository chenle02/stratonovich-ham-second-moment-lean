-- Printed type with the printed `ContDiff ℝ (↑⊤)` written as the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, scope `ContDiff`).
open scoped ContDiff in
/-- For a < 1, Psi smooth with compact support, a real test phi and s in [0,1]: <int_I |s-t|^(-a) Psi_t dt, [phi]>_(H_sp) = int h_(Psi,s) phi (TeX lines 116-122). -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.PositiveRawMean.inner_kBochner_toHsp :
    ∀ {d : ℕ} {S : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.SpData d} {a : ℝ},
      a < (1 : ℝ) →
        ∀ {Ψ : ℝ × StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ},
          ContDiff ℝ ∞ Ψ →
            HasCompactSupport Ψ →
              ∀ {φ : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ},
                StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.IsTestFunction φ →
                  ∀ {s : ℝ},
                    s ∈ Set.Icc (0 : ℝ) (1 : ℝ) →
                      Inner.inner ℝ
                          (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PositiveRawMean.kBochner a
                            (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.sliceField S Ψ) s)
                          (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.toHsp S φ) =
                        @MeasureTheory.integral _ _ _ _ MeasureTheory.MeasureSpace.toMeasurableSpace
                          MeasureTheory.MeasureSpace.volume
                          fun (x : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d) =>
                          StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalDilation.mean a S.Γ Ψ s x * φ x := by
  sorry
