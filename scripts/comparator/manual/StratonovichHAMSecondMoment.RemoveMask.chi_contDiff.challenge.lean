namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RemoveMask
open MeasureTheory Set Metric Filter Topology
open scoped ContDiff
open HomogHypothesis (Rd HomogCovariance IsTempered IsSpectralMeasure)
open WeakSobolev
open VariationalDilation (CPos SetScaling mean rawCost rate integratedRate)
open VariationalFloor (fl gl)
open VariationalRate (psiBar)
-- Statement copied from the source (the printed type writes `ContDiff ℝ (↑⊤)` for the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`)).
/-- chi is smooth: ContDiff R infinity chi. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RemoveMask.chi_contDiff : ContDiff ℝ ∞ chi := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RemoveMask
