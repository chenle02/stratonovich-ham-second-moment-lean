-- The statement's type-class and copy unfolding exceeds the default heartbeats.
set_option maxHeartbeats 4000000 in
/-- D target 4: under H:homog, Gamma != 0, given SpatialMeanMapTarget, YoungTarget (unused) and KformAbsTarget: PositiveRawEmbeddingTarget hH eta r (constructed T_R, U with E:positive-raw-mean and canonical version); no compactness. -/
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
  sorry
