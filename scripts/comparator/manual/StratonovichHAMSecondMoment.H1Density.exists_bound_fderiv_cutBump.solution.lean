namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Density
open MeasureTheory Filter Topology
open scoped ENNReal Pointwise ContDiff
open HomogHypothesis (Rd)
open WeakSobolev
open VariationalFloor (grad bumpN)
-- Statement copied from the source (the printed type elaborates `Real.semiring` where the declaration has the instance path through `Real.denselyNormedField`).
-- The section variables used, written as binders: {d : ℕ}.
/-- There is C >= 0 with norm(fderiv (cutBump d) y) <= C for every y in R^d. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.H1Density.exists_bound_fderiv_cutBump {d : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Rd d, ‖fderiv ℝ (cutBump d) y‖ ≤ C := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.H1Density.exists_bound_fderiv_cutBump
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Density
