namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Filter Metric Topology
open scoped ContDiff ENNReal RealInnerProductSpace
open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure IsEven)
open TimeSchur (kern kern_nonneg measurable_kern kern_sub_comm)
open SpaceTimePositivity (timeMeasure timeMeasure_eq_Icc)
open OccupationCeilingFinite (K0 K0_pos)
open WeakSobolev (IsTestFunction)
open SpatialFourierBound (spatialPair)
open VariationalDilation (CPos rawCost)
variable {d : ℕ}
/-- For Psi smooth with compact support on R x R^d and every s: x |-> Psi(s,x) is a test function. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.OccupationCompletion.slice_isTest {Ψ : ℝ × Rd d → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hΨs : HasCompactSupport Ψ)
    (s : ℝ) : IsTestFunction fun x => Ψ (s, x) := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.OccupationCompletion.slice_isTest
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion
