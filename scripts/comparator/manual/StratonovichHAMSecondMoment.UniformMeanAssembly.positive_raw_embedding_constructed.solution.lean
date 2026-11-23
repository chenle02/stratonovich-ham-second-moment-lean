-- The statement's type-class and copy unfolding exceeds the default heartbeats.
set_option maxHeartbeats 4000000 in
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.UniformMeanAssembly.positive_raw_embedding_constructed :
    ∀ {d : ℕ} {alpha alpha0 : ℝ}
      {Γ μ : MeasureTheory.Measure (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
      (hH : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ),
      Γ ≠ (0 : MeasureTheory.Measure (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d)) →
        ∀ (η : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d) {r : ENNReal}
          [inst : Fact ((1 : ENNReal) ≤ r)],
          StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.SpatialMeanMapTarget hH η →
            StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.YoungTarget →
              StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.KformAbsTarget
                  (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.TParams.ofHomog hH) →
                StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.PositiveRawEmbeddingTarget hH η r := by
  bridge_auto _root_.StratonovichHAMSecondMoment.UniformMeanAssembly.positive_raw_embedding_constructed
