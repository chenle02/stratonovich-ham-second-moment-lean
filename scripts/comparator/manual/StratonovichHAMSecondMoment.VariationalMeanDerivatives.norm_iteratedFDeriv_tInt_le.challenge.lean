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
/-- E Borel, second countable, tau measurable, w a.e. strongly measurable, Dominated nu tau w S, n natural, Phi Good on S: |D^n tInt Phi (p)| <= int |w y| |D^n Phi(p - tau y)| dnu for every p. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.VariationalMeanDerivatives.norm_iteratedFDeriv_tInt_le (hτ : Measurable τ) (hw : AEStronglyMeasurable w ν)
    (hdom : Dominated ν τ w S) (n : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {Φ : E → F}, Good S Φ → ∀ p,
      ‖iteratedFDeriv ℝ n (tInt ν τ w Φ) p‖ ≤
        ∫ y, |w y| * ‖iteratedFDeriv ℝ n Φ (p - τ y)‖ ∂ν := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalMeanDerivatives
