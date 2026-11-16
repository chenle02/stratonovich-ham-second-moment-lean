namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalMeanDerivatives
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Metric
open scoped ContDiff
open HomogHypothesis (Rd HomogCovariance IsTempered IsSpectralMeasure)
open VariationalDilation (CPos conv mean)
open VariationalMean (gMass exists_radius)
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Y : Type}
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Y]
variable {ν : Measure Y} {τ : Y → E} {w : Y → ℝ} {S : Set E}
/-- Under the hypotheses of hasFDerivAt_tInt: fderiv R (tInt nu tau w Phi) = tInt nu tau w (fderiv R Phi). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.VariationalMeanDerivatives.fderiv_tInt (hτ : Measurable τ) (hw : AEStronglyMeasurable w ν)
    (hdom : Dominated ν τ w S) {Φ : E → F} (h : Good S Φ) :
    fderiv ℝ (tInt ν τ w Φ) = tInt ν τ w (fderiv ℝ Φ) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalMeanDerivatives
