-- Printed type with the inner lower integral parenthesized as in the source (the printer drops the parentheses, so `∂ν` would bind to the inner integral).
/-- Route step 2 (Tonelli in [0,infinity]): for s-finite mu, nu restricted to (0,L] s-finite, and measurable F, G >= 0: Q_L(F,G) = int over (0,L] nu(d lambda) int dr B(F h_lambda(.,r), G h_lambda(.,r)). No integrability needed. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.PairingTranslatedCS.QLF_eq_lintegral_Bsp :
    ∀ {d : ℕ} (ν : MeasureTheory.Measure ℝ)
      (μ : MeasureTheory.Measure (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d))
      [MeasureTheory.SFinite μ] (L : ℝ) [MeasureTheory.SFinite (ν.restrict (Set.Ioc (0 : ℝ) L))]
      {F G : ℝ × StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ENNReal},
      Measurable F →
        Measurable G →
          StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingTranslatedCS.QLF ν μ L F G =
            ∫⁻ (l : ℝ) in Set.Ioc (0 : ℝ) L,
              (∫⁻ (r : ℝ),
                StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingTranslatedCS.Bsp μ
                  (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingTranslatedCS.featMul F l r)
                  (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingTranslatedCS.featMul G l r)) ∂ν := by
  exact @_root_.StratonovichHAMSecondMoment.PairingTranslatedCS.QLF_eq_lintegral_Bsp
