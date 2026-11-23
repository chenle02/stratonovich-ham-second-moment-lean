-- Printed type with the printed `ContDiff ℝ (↑⊤)` written as the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, scope `ContDiff`).
open scoped ContDiff in
/-- For U with UTensorSpec, 2 <= r and Psi smooth with compact support on R x R^d: U(incl Psi)(s) = int_I |s-t|^(-a) Psi_t dt (Bochner integral of the slice field in H_sp) for a.e. s (integrated_intrinsic_constant.tex lines 69-80 at revision edf7085f). -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.UniformMeanAssembly.U_incl_ae :
    ∀ {d : ℕ} {S : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.SpData d}
      {p : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.TParams} {r : ENNReal}
      [inst : Fact ((1 : ENNReal) ≤ r)]
      {U :
        StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.HI p S →L[ℝ]
          ↥(MeasureTheory.Lp (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.Hsp S) r
              StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.timeMeasure)},
      StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.UTensorSpec p S r U →
        (2 : ENNReal) ≤ r →
          ∀ {Ψ : ℝ × StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ},
            ContDiff ℝ ∞ Ψ →
              HasCompactSupport Ψ →
                ↑↑(U
                        (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.incl p S
                          Ψ)) =ᵐ[StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.timeMeasure]
                  StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PositiveRawMean.kBochner p.a
                    (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.sliceField S Ψ) := by
  bridge_auto _root_.StratonovichHAMSecondMoment.UniformMeanAssembly.U_incl_ae
