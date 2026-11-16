namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalMeanDerivatives
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Metric
open scoped ContDiff
open HomogHypothesis (Rd HomogCovariance IsTempered IsSpectralMeasure)
open VariationalDilation (CPos conv mean)
open VariationalMean (gMass exists_radius)
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Y : Type}
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- For E, F real normed spaces: if Good S Phi then Good S (fderiv R Phi). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.VariationalMeanDerivatives.Good.fderiv {S : Set E} {Φ : E → F} (h : Good S Φ) : Good S (fderiv ℝ Φ) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.VariationalMeanDerivatives.Good.fderiv
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalMeanDerivatives
