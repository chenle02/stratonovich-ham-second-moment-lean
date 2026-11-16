namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalMeanDerivatives
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Metric
open scoped ContDiff
open HomogHypothesis (Rd HomogCovariance IsTempered IsSpectralMeasure)
open VariationalDilation (CPos conv mean)
open VariationalMean (gMass exists_radius)
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Y : Type}
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Y]
variable {ν : Measure Y} {τ : Y → E} {w : Y → ℝ} {S : Set E}
/-- E real normed, Borel, second countable; nu a measure on Y, tau measurable, w a.e. strongly measurable, Dominated nu tau w S, Phi Good on S: tInt nu tau w Phi is C^infinity. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.VariationalMeanDerivatives.contDiff_tInt (hτ : Measurable τ) (hw : AEStronglyMeasurable w ν)
    (hdom : Dominated ν τ w S) {Φ : E → F} (h : Good S Φ) : ContDiff ℝ ∞ (tInt ν τ w Φ) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalMeanDerivatives
