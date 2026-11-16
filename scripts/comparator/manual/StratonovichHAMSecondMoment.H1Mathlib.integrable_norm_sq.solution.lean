namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Mathlib
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Filter Topology FourierTransform TemperedDistribution
open scoped ENNReal ContDiff SchwartzMap LineDeriv Real
open HomogHypothesis (Rd)
open WeakSobolev
open VariationalFloor (grad)
variable {d : ℕ}
/-- For F in L^2(R^d; C): x -> |F x|^2 is integrable. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.H1Mathlib.integrable_norm_sq (F : Lp ℂ 2 (volume : Measure (Rd d))) :
    Integrable (fun x => ‖F x‖ ^ 2) volume := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.H1Mathlib.integrable_norm_sq
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Mathlib
