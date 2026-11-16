namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
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
/-- Jlin p G F = the image of toK F in the completion HK p G (G complete). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.OccupationCompletion.Jlin_apply [CompleteSpace G] (F : Lp G 2 timeMeasure) :
    Jlin p G F = ((toK F : KPre p G) : HK p G) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.OccupationCompletion.Jlin_apply
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion
