namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalMeanDerivatives
-- Statement written from the source structure field `Good.smooth` (a structure field: the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Metric
open scoped ContDiff
/-- Structure field: a Good function is C^infinity. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.VariationalMeanDerivatives.Good.smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {S : Set E} {Φ : E → F} (self : Good S Φ) :
    ContDiff ℝ ∞ Φ := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.VariationalMeanDerivatives.Good.smooth
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalMeanDerivatives
