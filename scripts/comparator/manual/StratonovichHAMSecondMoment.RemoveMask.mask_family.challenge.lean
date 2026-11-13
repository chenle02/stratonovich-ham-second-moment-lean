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
/-- For R > 0, mask R is smooth, even, radial, [0,1]-valued, 1 on norm x <= R, with tsupport in the closed ball of radius 2R; mask R x <= mask R' x for 0 < R <= R'; mask R x -> 1 as R -> infinity. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RemoveMask.mask_family {d : ℕ} :
    (∀ R, 0 < R →
      ContDiff ℝ ∞ (mask (d := d) R) ∧ (∀ x : Rd d, mask R (-x) = mask R x) ∧
      (∀ x y : Rd d, ‖x‖ = ‖y‖ → mask R x = mask R y) ∧
      (∀ x : Rd d, 0 ≤ mask R x ∧ mask R x ≤ 1) ∧ (∀ x : Rd d, ‖x‖ ≤ R → mask R x = 1) ∧
      tsupport (mask (d := d) R) ⊆ closedBall 0 (2 * R)) ∧
    (∀ R R', 0 < R → R ≤ R' → ∀ x : Rd d, mask R x ≤ mask R' x) ∧
    (∀ x : Rd d, Tendsto (fun R => mask R x) atTop (𝓝 1)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RemoveMask
