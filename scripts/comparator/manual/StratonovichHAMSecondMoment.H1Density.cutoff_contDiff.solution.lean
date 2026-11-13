namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Density
open MeasureTheory Filter Topology
open scoped ENNReal Pointwise ContDiff
open HomogHypothesis (Rd)
open WeakSobolev
open VariationalFloor (grad bumpN)
-- Statement copied from the source (the printed type writes `ContDiff ℝ (↑⊤)` for the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`)).
-- The section variables used, written as binders: {d : ℕ}.
/-- cutoff n is smooth (ContDiff R infinity) on R^d. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.H1Density.cutoff_contDiff {d : ℕ} (n : ℕ) : ContDiff ℝ ∞ (cutoff (d := d) n) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.H1Density.cutoff_contDiff
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Density
