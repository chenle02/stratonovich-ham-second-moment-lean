namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Density
open MeasureTheory Filter Topology
open scoped ENNReal Pointwise ContDiff
open HomogHypothesis (Rd)
open WeakSobolev
open VariationalFloor (grad bumpN)
-- Statement copied from the source (the printed type elaborates `Real.semiring` where the declaration has the instance path through `Real.denselyNormedField`).
-- The section variables used, written as binders: {d : ℕ}.
/-- If norm(fderiv (cutBump d) y) <= C for every y, then norm(grad (cutoff n) x) <= C/(n+1) for every n and x. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.H1Density.norm_grad_cutoff_le {d : ℕ} {C : ℝ} (hC : ∀ y : Rd d, ‖fderiv ℝ (cutBump d) y‖ ≤ C)
    (n : ℕ) (x : Rd d) : ‖grad (cutoff n) x‖ ≤ C / ((n : ℝ) + 1) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.H1Density.norm_grad_cutoff_le
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Density
