namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialStaticControls
open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal
-- Statement copied from the source (the printed type writes `ContDiff ℝ (↑⊤)` for the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`)).
-- The section variables used, written as binders: {a : ℝ}.
/-- For every real a and n: fn a n is C^infinity on R. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SpatialStaticControls.fn_contDiff {a : ℝ} (n : ℕ) : ContDiff ℝ ∞ (fn a n) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.SpatialStaticControls.fn_contDiff
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialStaticControls
