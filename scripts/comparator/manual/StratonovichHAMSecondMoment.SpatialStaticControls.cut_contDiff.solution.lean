namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialStaticControls
open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal
-- Statement copied from the source (the printed type writes `ContDiff ℝ (↑⊤)` for the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`)).
/-- For every n: cut n is C^infinity on R. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SpatialStaticControls.cut_contDiff (n : ℕ) : ContDiff ℝ ∞ (cut n) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.SpatialStaticControls.cut_contDiff
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialStaticControls
