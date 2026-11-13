namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Density
open MeasureTheory Filter Topology
open scoped ENNReal Pointwise ContDiff
open HomogHypothesis (Rd)
open WeakSobolev
open VariationalFloor (grad bumpN)
-- Statement copied from the source (the printed type writes `ContDiff ℝ (↑⊤)` for the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`)).
-- The section variables used, written as binders: {d : ℕ}.
/-- If h : R^d -> R is smooth, then grad (x -> cutoff n x * h x) x = cutoff n x * grad h x + h x * grad (cutoff n) x for every x. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.H1Density.grad_cutoff_mul {d : ℕ} (n : ℕ) {h : Rd d → ℝ} (hh : ContDiff ℝ ∞ h) (x : Rd d) :
    grad (fun x => cutoff n x * h x) x = cutoff n x • grad h x + h x • grad (cutoff n) x := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.H1Density.grad_cutoff_mul
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Density
