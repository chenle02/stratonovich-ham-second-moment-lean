namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RemoveMask
open MeasureTheory Set Metric Filter Topology
open scoped ContDiff
open HomogHypothesis (Rd HomogCovariance IsTempered IsSpectralMeasure)
open WeakSobolev
open VariationalDilation (CPos SetScaling mean rawCost rate integratedRate)
open VariationalFloor (fl gl)
open VariationalRate (psiBar)
-- Statement copied from the source (the printed type writes `ContDiff ℝ (↑⊤)` for the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`)).
-- The section variables used, written as binders: {d : ℕ}.
/-- For R > 0: mask R is smooth on R^d (ContDiff R infinity), including at the origin. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RemoveMask.mask_contDiff {d : ℕ} {R : ℝ} (hR : 0 < R) : ContDiff ℝ ∞ (mask (d := d) R) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.RemoveMask.mask_contDiff
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RemoveMask
