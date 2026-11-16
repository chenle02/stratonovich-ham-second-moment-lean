namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Filter Metric Topology
open scoped ContDiff ENNReal RealInnerProductSpace
open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure IsEven)
open TimeSchur (kern kern_nonneg measurable_kern kern_sub_comm)
open SpaceTimePositivity (timeMeasure timeMeasure_eq_Icc)
open OccupationCeilingFinite (K0 K0_pos)
variable (p : TParams) (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℝ G]
variable {p G}
variable (p G)
variable {p G}
/-- For G complete and F in Lp G 2 on I: |F|^2 = int_I |F(t)|^2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.OccupationCompletion.Lp_norm_sq_eq [CompleteSpace G] (F : Lp G 2 timeMeasure) :
    ‖F‖ ^ 2 = ∫ t, ‖F t‖ ^ 2 ∂timeMeasure := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.OccupationCompletion.Lp_norm_sq_eq
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion
