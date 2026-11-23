-- Printed type with the inner lower integral parenthesized as in the source (the printer drops the parentheses, so `∂ν` would bind to the inner integral).
/-- For every measure nu and reals L, t, s: kappa_L(t-s) = int over (0,L] of (int h_lambda(t,r) h_lambda(s,r) dr) nu(d lambda) (TeX 1162-1163 with 1214-1220 at edf7085f); no finiteness of nu needed. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.PairingTranslatedCS.kappaCap_eq :
    ∀ (ν : MeasureTheory.Measure ℝ) (L t s : ℝ),
      StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.kappaCap ν L (t - s) =
        ∫⁻ (l : ℝ) in Set.Ioc (0 : ℝ) L,
          (∫⁻ (r : ℝ),
            StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingTranslatedCS.feat (l, t, r) *
              StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingTranslatedCS.feat (l, s, r)) ∂ν := by
  sorry
