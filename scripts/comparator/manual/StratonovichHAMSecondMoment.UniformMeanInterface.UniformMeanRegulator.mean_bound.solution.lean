-- the copied and the project's `meanOp` and norms of `L(E)` are identified by unfolding, past the default heartbeats
set_option maxHeartbeats 4000000 in
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.UniformMeanInterface.UniformMeanRegulator.mean_bound :
    ∀ {d : ℕ} {p : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.TParams}
      {S : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.SpData d}
      {η : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d} {r : ENNReal}
      [inst : Fact ((1 : ENNReal) ≤ r)]
      (self : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.UniformMeanRegulator p S η r) (R : ℝ)
      (hR : (1 : ℝ) ≤ R),
      ‖StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.meanOp (self.Tsp R hR).T self.U‖ ≤
        self.M0 * ‖self.Ct‖ := by
  bridge_auto _root_.StratonovichHAMSecondMoment.UniformMeanInterface.UniformMeanRegulator.mean_bound
