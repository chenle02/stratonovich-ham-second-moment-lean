namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Density
open MeasureTheory Filter Topology
open scoped ENNReal Pointwise ContDiff
open HomogHypothesis (Rd)
open WeakSobolev
open VariationalFloor (grad bumpN)
-- Statement copied from the source (the printed type writes `ContDiff ℝ (↑⊤)` for the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`)).
-- The section variables used, written as binders: {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F].
/-- If u : R^d -> F is locally integrable, then mollify phi u is smooth (ContDiff R infinity). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.H1Density.contDiff_mollify {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (φ : ContDiffBump (0 : Rd d)) {u : Rd d → F}
    (hu : LocallyIntegrable u volume) : ContDiff ℝ ∞ (mollify φ u) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Density
