namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalMeanDerivatives
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Metric
open scoped ContDiff
open HomogHypothesis (Rd HomogCovariance IsTempered IsSpectralMeasure)
open VariationalDilation (CPos conv mean)
open VariationalMean (gMass exists_radius)
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Y : Type}
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- If Good S Phi, n a natural number and q not in S: the n-th iterated derivative of Phi at q is 0. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.VariationalMeanDerivatives.Good.iteratedFDeriv_eq_zero {S : Set E} {Φ : E → F} (h : Good S Φ) (n : ℕ) {q : E}
    (hq : q ∉ S) : iteratedFDeriv ℝ n Φ q = 0 := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalMeanDerivatives
