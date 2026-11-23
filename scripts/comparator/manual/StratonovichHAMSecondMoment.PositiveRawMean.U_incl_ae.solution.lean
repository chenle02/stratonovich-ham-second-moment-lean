-- Printed type with the printed `ContDiff ℝ (↑⊤)` written as the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, scope `ContDiff`).
open scoped ContDiff in
/-- For a regulator Ureg and Psi smooth with compact support: (C_t (x) I)(incl Psi)(s) = int_I |s-t|^(-a) Psi_t dt (Bochner integral of the slice field in H_sp) for a.e. s (TeX lines 69-82). Named input supplied: UniformMeanRegulator, CameronSpatialMap. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.PositiveRawMean.U_incl_ae :
    ∀ {d : ℕ} {S : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.SpData d}
      {p : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.TParams}
      {η : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d} {r : ENNReal}
      [inst : Fact ((1 : ENNReal) ≤ r)]
      (Ureg : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.UniformMeanRegulator p S η r)
      {Ψ : ℝ × StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ},
      ContDiff ℝ ∞ Ψ →
        HasCompactSupport Ψ →
          ↑↑(Ureg.U
                  (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.incl p S
                    Ψ)) =ᵐ[StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.timeMeasure]
            StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PositiveRawMean.kBochner p.a
              (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.sliceField S Ψ) := by
  bridge_auto _root_.StratonovichHAMSecondMoment.PositiveRawMean.U_incl_ae
